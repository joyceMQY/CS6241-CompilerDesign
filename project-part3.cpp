#include "llvm/Transforms/Scalar.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/Hashing.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/Dominators.h"
#include "llvm/Analysis/InstructionSimplify.h"
#include "llvm/Analysis/Loads.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/MemoryDependenceAnalysis.h"
#include "llvm/Assembly/Writer.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Support/Allocator.h"
#include "llvm/Support/PatternMatch.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/Pass.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Support/raw_ostream.h"

#include <vector>
#include <set>
#include <queue>
#include <sstream>

using namespace llvm;
using namespace PatternMatch;

//===----------------------------------------------------------------------===//
//                         ValueTable Class
//===----------------------------------------------------------------------===//

/// This class holds the mapping between values and value numbers.  It is used
/// as an efficient mechanism to determine the expression-wise equivalence of
/// two values.
namespace {
struct Expression {
	uint32_t opcode;
	Type *type;
	SmallVector<uint32_t, 4> varargs;

	Expression(uint32_t o = ~2U) :
		opcode(o) {
	}

	bool operator==(const Expression &other) const {
		if (opcode != other.opcode)
			return false;
		if (opcode == ~0U || opcode == ~1U)
			return true;
		if (type != other.type)
			return false;
		if (varargs != other.varargs)
			return false;
		return true;
	}

	friend hash_code hash_value(const Expression &Value) {
		return hash_combine(Value.opcode, Value.type, hash_combine_range(
				Value.varargs.begin(), Value.varargs.end()));
	}
};
}
namespace llvm {
template<> struct DenseMapInfo<Expression> {
	static inline Expression getEmptyKey() {
		return ~0U;
	}

	static inline Expression getTombstoneKey() {
		return ~1U;
	}

	static unsigned getHashValue(const Expression e) {
		using llvm::hash_value;
		return static_cast<unsigned> (hash_value(e));
	}
	static bool isEqual(const Expression &LHS, const Expression &RHS) {
		return LHS == RHS;
	}
};
}
namespace {
class ValueTable {
	DenseMap<Value*, uint32_t> valueNumbering;
	DenseMap<Expression, uint32_t> expressionNumbering;
	AliasAnalysis *AA;
	MemoryDependenceAnalysis *MD;
	DominatorTree *DT;

	uint32_t nextValueNumber;

	Expression create_expression(Instruction* I);
	Expression create_cmp_expression(unsigned Opcode,
			CmpInst::Predicate Predicate, Value *LHS, Value *RHS);
	Expression create_extractvalue_expression(ExtractValueInst* EI);
	uint32_t lookup_or_add_call(CallInst* C);
public:
	ValueTable() :
		nextValueNumber(1) {
	}
	uint32_t lookup_or_add(Value *V);
	uint32_t lookup(Value *V) const;
	uint32_t find(Value *V) const;
	uint32_t lookup_or_add_cmp(unsigned Opcode, CmpInst::Predicate Pred,
			Value *LHS, Value *RHS);
	void add(Value *V, uint32_t num);
	void clear();
	void erase(Value *v);
	void setAliasAnalysis(AliasAnalysis* A) {
		AA = A;
	}
	AliasAnalysis *getAliasAnalysis() const {
		return AA;
	}
	void setMemDep(MemoryDependenceAnalysis* M) {
		MD = M;
	}
	void setDomTree(DominatorTree* D) {
		DT = D;
	}
	uint32_t getNextUnusedValueNumber() {
		return nextValueNumber;
	}
	void verifyRemoved(const Value *) const;
	void dump();
};
}

//===----------------------------------------------------------------------===//
//                     ValueTable Internal Functions
//===----------------------------------------------------------------------===//

Expression ValueTable::create_expression(Instruction *I) {
	Expression e;
	e.type = I->getType();
	e.opcode = I->getOpcode();
	for (Instruction::op_iterator OI = I->op_begin(), OE = I->op_end(); OI
			!= OE; ++OI)
		e.varargs.push_back(lookup_or_add(*OI));
	if (I->isCommutative()) {
		// Ensure that commutative instructions that only differ by a permutation
		// of their operands get the same value number by sorting the operand value
		// numbers.  Since all commutative instructions have two operands it is more
		// efficient to sort by hand rather than using, say, std::sort.
		assert(I->getNumOperands() == 2 && "Unsupported commutative instruction!");
		if (e.varargs[0] > e.varargs[1])
			std::swap(e.varargs[0], e.varargs[1]);
	}

	if (CmpInst *C = dyn_cast<CmpInst>(I)) {
		// Sort the operand value numbers so x<y and y>x get the same value number.
		CmpInst::Predicate Predicate = C->getPredicate();
		if (e.varargs[0] > e.varargs[1]) {
			std::swap(e.varargs[0], e.varargs[1]);
			Predicate = CmpInst::getSwappedPredicate(Predicate);
		}
		e.opcode = (C->getOpcode() << 8) | Predicate;
	} else if (InsertValueInst *E = dyn_cast<InsertValueInst>(I)) {
		for (InsertValueInst::idx_iterator II = E->idx_begin(), IE =
				E->idx_end(); II != IE; ++II)
			e.varargs.push_back(*II);
	}

	return e;
}

Expression ValueTable::create_cmp_expression(unsigned Opcode,
		CmpInst::Predicate Predicate, Value *LHS, Value *RHS) {
	assert((Opcode == Instruction::ICmp || Opcode == Instruction::FCmp) &&
			"Not a comparison!");
	Expression e;
	e.type = CmpInst::makeCmpResultType(LHS->getType());
	e.varargs.push_back(lookup_or_add(LHS));
	e.varargs.push_back(lookup_or_add(RHS));

	// Sort the operand value numbers so x<y and y>x get the same value number.
	if (e.varargs[0] > e.varargs[1]) {
		std::swap(e.varargs[0], e.varargs[1]);
		Predicate = CmpInst::getSwappedPredicate(Predicate);
	}
	e.opcode = (Opcode << 8) | Predicate;
	return e;
}

Expression ValueTable::create_extractvalue_expression(ExtractValueInst *EI) {
	assert(EI != 0 && "Not an ExtractValueInst?");
	Expression e;
	e.type = EI->getType();
	e.opcode = 0;

	IntrinsicInst *I = dyn_cast<IntrinsicInst> (EI->getAggregateOperand());
	if (I != 0 && EI->getNumIndices() == 1 && *EI->idx_begin() == 0) {
		// EI might be an extract from one of our recognised intrinsics. If it
		// is we'll synthesize a semantically equivalent expression instead on
		// an extract value expression.
		switch (I->getIntrinsicID()) {
		case Intrinsic::sadd_with_overflow:
		case Intrinsic::uadd_with_overflow:
			e.opcode = Instruction::Add;
			break;
		case Intrinsic::ssub_with_overflow:
		case Intrinsic::usub_with_overflow:
			e.opcode = Instruction::Sub;
			break;
		case Intrinsic::smul_with_overflow:
		case Intrinsic::umul_with_overflow:
			e.opcode = Instruction::Mul;
			break;
		default:
			break;
		}

		if (e.opcode != 0) {
			// Intrinsic recognized. Grab its args to finish building the expression.
			assert(I->getNumArgOperands() == 2 &&
					"Expect two args for recognised intrinsics.");
			e.varargs.push_back(lookup_or_add(I->getArgOperand(0)));
			e.varargs.push_back(lookup_or_add(I->getArgOperand(1)));
			return e;
		}
	}

	// Not a recognised intrinsic. Fall back to producing an extract value
	// expression.
	e.opcode = EI->getOpcode();
	for (Instruction::op_iterator OI = EI->op_begin(), OE = EI->op_end(); OI
			!= OE; ++OI)
		e.varargs.push_back(lookup_or_add(*OI));

	for (ExtractValueInst::idx_iterator II = EI->idx_begin(), IE =
			EI->idx_end(); II != IE; ++II)
		e.varargs.push_back(*II);

	return e;
}

//===----------------------------------------------------------------------===//
//                     ValueTable External Functions
//===----------------------------------------------------------------------===//

/// add - Insert a value into the table with a specified value number.
void ValueTable::add(Value *V, uint32_t num) {
	valueNumbering.insert(std::make_pair(V, num));
}

uint32_t ValueTable::lookup_or_add_call(CallInst *C) {
	if (AA->doesNotAccessMemory(C)) {
		Expression exp = create_expression(C);
		uint32_t &e = expressionNumbering[exp];
		if (!e)
			e = nextValueNumber++;
		valueNumbering[C] = e;
		return e;
	} else if (AA->onlyReadsMemory(C)) {
		Expression exp = create_expression(C);
		uint32_t &e = expressionNumbering[exp];
		if (!e) {
			e = nextValueNumber++;
			valueNumbering[C] = e;
			return e;
		}
		if (!MD) {
			e = nextValueNumber++;
			valueNumbering[C] = e;
			return e;
		}

		MemDepResult local_dep = MD->getDependency(C);

		if (!local_dep.isDef() && !local_dep.isNonLocal()) {
			valueNumbering[C] = nextValueNumber;
			return nextValueNumber++;
		}

		if (local_dep.isDef()) {
			CallInst* local_cdep = cast<CallInst> (local_dep.getInst());

			if (local_cdep->getNumArgOperands() != C->getNumArgOperands()) {
				valueNumbering[C] = nextValueNumber;
				return nextValueNumber++;
			}

			for (unsigned i = 0, e = C->getNumArgOperands(); i < e; ++i) {
				uint32_t c_vn = lookup_or_add(C->getArgOperand(i));
				uint32_t cd_vn = lookup_or_add(local_cdep->getArgOperand(i));
				if (c_vn != cd_vn) {
					valueNumbering[C] = nextValueNumber;
					return nextValueNumber++;
				}
			}

			uint32_t v = lookup_or_add(local_cdep);
			valueNumbering[C] = v;
			return v;
		}

		// Non-local case.
		const MemoryDependenceAnalysis::NonLocalDepInfo &deps =
				MD->getNonLocalCallDependency(CallSite(C));
		// FIXME: Move the checking logic to MemDep!
		CallInst* cdep = 0;

		// Check to see if we have a single dominating call instruction that is
		// identical to C.
		for (unsigned i = 0, e = deps.size(); i != e; ++i) {
			const NonLocalDepEntry *I = &deps[i];
			if (I->getResult().isNonLocal())
				continue;

			// We don't handle non-definitions.  If we already have a call, reject
			// instruction dependencies.
			if (!I->getResult().isDef() || cdep != 0) {
				cdep = 0;
				break;
			}

			CallInst *NonLocalDepCall = dyn_cast<CallInst> (
					I->getResult().getInst());
			// FIXME: All duplicated with non-local case.
			if (NonLocalDepCall && DT->properlyDominates(I->getBB(),
					C->getParent())) {
				cdep = NonLocalDepCall;
				continue;
			}

			cdep = 0;
			break;
		}

		if (!cdep) {
			valueNumbering[C] = nextValueNumber;
			return nextValueNumber++;
		}

		if (cdep->getNumArgOperands() != C->getNumArgOperands()) {
			valueNumbering[C] = nextValueNumber;
			return nextValueNumber++;
		}
		for (unsigned i = 0, e = C->getNumArgOperands(); i < e; ++i) {
			uint32_t c_vn = lookup_or_add(C->getArgOperand(i));
			uint32_t cd_vn = lookup_or_add(cdep->getArgOperand(i));
			if (c_vn != cd_vn) {
				valueNumbering[C] = nextValueNumber;
				return nextValueNumber++;
			}
		}

		uint32_t v = lookup_or_add(cdep);
		valueNumbering[C] = v;
		return v;

	} else {
		valueNumbering[C] = nextValueNumber;
		return nextValueNumber++;
	}
}

/// lookup_or_add - Returns the value number for the specified value, assigning
/// it a new number if it did not have one before.
uint32_t ValueTable::lookup_or_add(Value *V) {
	DenseMap<Value*, uint32_t>::iterator VI = valueNumbering.find(V);
	if (VI != valueNumbering.end())
		return VI->second;

	if (!isa<Instruction> (V)) {
		valueNumbering[V] = nextValueNumber;
		return nextValueNumber++;
	}

	Instruction* I = cast<Instruction> (V);
	Expression exp;
	switch (I->getOpcode()) {
	case Instruction::Call:
		return lookup_or_add_call(cast<CallInst> (I));
	case Instruction::Add:
	case Instruction::FAdd:
	case Instruction::Sub:
	case Instruction::FSub:
	case Instruction::Mul:
	case Instruction::FMul:
	case Instruction::UDiv:
	case Instruction::SDiv:
	case Instruction::FDiv:
	case Instruction::URem:
	case Instruction::SRem:
	case Instruction::FRem:
	case Instruction::Shl:
	case Instruction::LShr:
	case Instruction::AShr:
	case Instruction::And:
	case Instruction::Or:
	case Instruction::Xor:
	case Instruction::ICmp:
	case Instruction::FCmp:
	case Instruction::Trunc:
	case Instruction::ZExt:
	case Instruction::SExt:
	case Instruction::FPToUI:
	case Instruction::FPToSI:
	case Instruction::UIToFP:
	case Instruction::SIToFP:
	case Instruction::FPTrunc:
	case Instruction::FPExt:
	case Instruction::PtrToInt:
	case Instruction::IntToPtr:
	case Instruction::BitCast:
	case Instruction::Select:
	case Instruction::ExtractElement:
	case Instruction::InsertElement:
	case Instruction::ShuffleVector:
	case Instruction::InsertValue:
	case Instruction::GetElementPtr:
		exp = create_expression(I);
		break;
	case Instruction::ExtractValue:
		exp = create_extractvalue_expression(cast<ExtractValueInst> (I));
		break;
	default:
		valueNumbering[V] = nextValueNumber;
		return nextValueNumber++;
	}

	uint32_t& e = expressionNumbering[exp];
	if (!e)
		e = nextValueNumber++;
	valueNumbering[V] = e;
	return e;
}

uint32_t ValueTable::find(Value *V) const {
	DenseMap<Value*, uint32_t>::const_iterator VI = valueNumbering.find(V);
	if(VI == valueNumbering.end()) {
		return -1;
	} else {
		return VI->second;
	}
}

/// lookup - Returns the value number of the specified value. Fails if
/// the value has not yet been numbered.
uint32_t ValueTable::lookup(Value *V) const {
	DenseMap<Value*, uint32_t>::const_iterator VI = valueNumbering.find(V);
	assert(VI != valueNumbering.end() && "Value not numbered?");
	return VI->second;
}

/// lookup_or_add_cmp - Returns the value number of the given comparison,
/// assigning it a new number if it did not have one before.  Useful when
/// we deduced the result of a comparison, but don't immediately have an
/// instruction realizing that comparison to hand.
uint32_t ValueTable::lookup_or_add_cmp(unsigned Opcode,
		CmpInst::Predicate Predicate, Value *LHS, Value *RHS) {
	Expression exp = create_cmp_expression(Opcode, Predicate, LHS, RHS);
	uint32_t& e = expressionNumbering[exp];
	if (!e)
		e = nextValueNumber++;
	return e;
}

/// clear - Remove all entries from the ValueTable.
void ValueTable::clear() {
	valueNumbering.clear();
	expressionNumbering.clear();
	nextValueNumber = 1;
}

/// erase - Remove a value from the value numbering.
void ValueTable::erase(Value *V) {
	valueNumbering.erase(V);
}

/// verifyRemoved - Verify that the value is removed from all internal data
/// structures.
void ValueTable::verifyRemoved(const Value *V) const {
	for (DenseMap<Value*, uint32_t>::const_iterator I = valueNumbering.begin(),
			E = valueNumbering.end(); I != E; ++I) {
		assert(I->first != V && "Inst still occurs in value numbering map!");
	}
}

void ValueTable::dump() {
	errs() << "=============================================\n";
	errs() << "========Start dumping value table============\n";
	errs() << "=============================================\n";

	for(DenseMap<Value*, uint32_t>::iterator iter = valueNumbering.begin();
			iter != valueNumbering.end(); ++iter) {
		errs() << *iter->first << " <-> " << iter->second << "\n";
	}

	errs() << "=============================================\n";
	errs() << "===========Start dumping exp table===========\n";
	errs() << "=============================================\n";

	for(DenseMap<Expression, uint32_t>::iterator iter = expressionNumbering.begin();
			iter != expressionNumbering.end(); ++iter) {
		Expression exp = iter->first;
		errs() << "Type: " << *exp.type << " Opcode: " << exp.opcode
				<< " value: " << iter->second << "\nArgs:";
		for(SmallVector<unsigned int, 4>::iterator iter = exp.varargs.begin();
				iter != exp.varargs.end(); ++iter) {
			errs() << *iter << " ";
		}
		errs() << "\n";
	}
}

//===----------------------------------------------------------------------===//
//                                ModifiedGVN Pass
//===----------------------------------------------------------------------===//

namespace {
class ModifiedGVN: public FunctionPass {
	bool NoLoads;
	MemoryDependenceAnalysis *MD;
	DominatorTree *DT;

	ValueTable VN;

	/// LeaderTable - A mapping from value numbers to lists of Value*'s that
	/// have that value number.  Use findLeader to query it.
	struct LeaderTableEntry {
		Value *Val;
		const BasicBlock *BB;
		LeaderTableEntry *Next;
	};

	DenseMap<uint32_t, LeaderTableEntry> LeaderTable;
	BumpPtrAllocator TableAllocator;

	struct ArrayIndex {
		Value* max;
		Value* min;
		Value* index;
		BranchInst* maxBranch;
		BranchInst* minBranch;
		ICmpInst* maxCmp;
		ICmpInst* minCmp;
	};

	std::map<BasicBlock*, std::map<llvm::Value*, std::set<llvm::Instruction*> > > bb2in;
	std::map<BasicBlock*, std::map<llvm::Value*, std::set<llvm::Instruction*> > > bb2out;
public:
	static char ID; // Pass identification, replacement for typeid
	static bool DEBUG;
	static int errorBBcount;
	static int insertBBcount;
	ModifiedGVN(bool noloads = false) :
		FunctionPass(ID), NoLoads(noloads), MD(0) {
//		initializeModifiedGVNPass(*PassRegistry::getPassRegistry());
	}

	bool runOnFunction(Function &F);

	DominatorTree &getDominatorTree() const {
		return *DT;
	}
	AliasAnalysis *getAliasAnalysis() const {
		return VN.getAliasAnalysis();
	}
	MemoryDependenceAnalysis &getMemDep() const {
		return *MD;
	}
private:
	/// addToLeaderTable - Push a new Value to the LeaderTable onto the list for
	/// its value number.
	void addToLeaderTable(uint32_t N, Value *V, const BasicBlock *BB) {
		LeaderTableEntry &Curr = LeaderTable[N];
		if (!Curr.Val) {
			Curr.Val = V;
			Curr.BB = BB;
			return;
		}

		LeaderTableEntry *Node = TableAllocator.Allocate<LeaderTableEntry> ();
		Node->Val = V;
		Node->BB = BB;
		Node->Next = Curr.Next;
		Curr.Next = Node;
	}

	/// removeFromLeaderTable - Scan the list of values corresponding to a given
	/// value number, and remove the given instruction if encountered.
	void removeFromLeaderTable(uint32_t N, Instruction *I, BasicBlock *BB) {
		LeaderTableEntry* Prev = 0;
		LeaderTableEntry* Curr = &LeaderTable[N];

		while (Curr->Val != I || Curr->BB != BB) {
			Prev = Curr;
			Curr = Curr->Next;
		}

		if (Prev) {
			Prev->Next = Curr->Next;
		} else {
			if (!Curr->Next) {
				Curr->Val = 0;
				Curr->BB = 0;
			} else {
				LeaderTableEntry* Next = Curr->Next;
				Curr->Val = Next->Val;
				Curr->BB = Next->BB;
				Curr->Next = Next->Next;
			}
		}
	}

	// List of critical edges to be split between iterations.
	SmallVector<std::pair<TerminatorInst*, unsigned>, 4> toSplit;

	// This transformation requires dominator postdominator info
	virtual void getAnalysisUsage(AnalysisUsage &AU) const {
		AU.addRequired<DominatorTree> ();
		if (!NoLoads)
			AU.addRequired<MemoryDependenceAnalysis> ();
		AU.addRequired<AliasAnalysis> ();

		AU.addPreserved<DominatorTree> ();
		AU.addPreserved<AliasAnalysis> ();
	}

	// Other helper routines
	bool processInstruction(Instruction *I);
	bool processBlock(BasicBlock *BB);
	void LeaderTableDump();
	void iterateOnFunction(Function &F);
	Value *findLeader(const BasicBlock *BB, uint32_t num);
	void cleanupGlobalSets();
	bool splitCriticalEdges();
	BasicBlock *splitCriticalEdges(BasicBlock *Pred, BasicBlock *Succ);
	void propagateEquality(Value *LHS, Value *RHS, const BasicBlockEdge &Root);
	bool processFoldableCondBr(BranchInst *BI);

	void getReachDefs(Function &F);
	void mapUnion(std::map<Value*, std::set<Instruction*> > &target,
			std::map<Value*, std::set<Instruction*> > &source);
	void mapUnion(std::map<Value*, std::set<Instruction*> > &target,
			std::map<Value*, Instruction*> &source);
	std::map<Value*, std::set<Instruction*> > mapSub(
			std::map<Value*, std::set<Instruction*> > map1,
			std::map<Value*, std::set<Instruction*> > &map2);
	bool compare(std::map<BasicBlock*, std::map<Value*, std::set<Instruction*> > > &map1,
			std::map<BasicBlock*, std::map<Value*, std::set<Instruction*> > > &map2);
	bool compare(std::map<Value*, std::set<Instruction*> > &map1,
			std::map<Value*, std::set<Instruction*> > &map2);
	void dumpReachDef(Function &F);
	void findAllArrayIndexs(std::map<GetElementPtrInst*, ArrayIndex*>& arrayIndexMap,
			Function &F, std::map<BasicBlock*, std::set<GetElementPtrInst*> >& bb2indexs);
	BasicBlock* insertAllBoundChecks(std::map<GetElementPtrInst*, ArrayIndex*>& arrayIndexMap,
				Function &F, Module &M);
	std::string getBBName(bool isErrorBB, bool isMax);
	BasicBlock* creatErrorHandleBB(Function* func, Module* M);
	void removeDuplicateChecks(std::map<GetElementPtrInst*, ArrayIndex*>& arrayIndexMap,
			std::map<BasicBlock*, std::set<GetElementPtrInst*> >& bb2indexs, Function& F,
			std::set<Value*> &removedValues);
	bool checkMaxMin(ArrayIndex* index1, ArrayIndex* index2);
	bool compareValues(Value* v1, Value* v2);
	Value* findDefValue(Instruction* inst, AllocaInst* alloca);
	void findDefinitions(Instruction* curInstr, Instruction* startInstr,
			std::set<Instruction*>& visited, std::set<Instruction*>& result);
};

char ModifiedGVN::ID = 0;
bool ModifiedGVN::DEBUG = false;
int ModifiedGVN::errorBBcount = 0;
int ModifiedGVN::insertBBcount = 0;
}

/// runOnFunction - This is the main transformation entry point for a function.
bool ModifiedGVN::runOnFunction(Function& F) {
	errs() << "\nCurrent fucntion is: " << F.getName() << "\n";

	if (!NoLoads)
		MD = &getAnalysis<MemoryDependenceAnalysis> ();
	DT = &getAnalysis<DominatorTree> ();
	VN.setAliasAnalysis(&getAnalysis<AliasAnalysis> ());
	VN.setMemDep(MD);
	VN.setDomTree(DT);

	iterateOnFunction(F);
	if(DEBUG) {
		VN.dump();
		LeaderTableDump();
	}

	std::map<GetElementPtrInst*, ArrayIndex*> arrayIndexMap;
	std::map<BasicBlock*, std::set<GetElementPtrInst*> > bb2indexs;
	std::set<Value*> removedValues;

	std::map<BasicBlock*, std::map<Value*, std::set<Instruction*> > > bb2in;
	std::map<BasicBlock*, std::map<Value*, std::set<Instruction*> > > bb2out;

	getReachDefs(F);
	if(DEBUG) dumpReachDef(F);

	// first go through the program, find all GetElementPtrInsts and add them to a map
	findAllArrayIndexs(arrayIndexMap, F, bb2indexs);

	removeDuplicateChecks(arrayIndexMap, bb2indexs, F, removedValues);

	if(arrayIndexMap.size() > 0) {
		insertAllBoundChecks(arrayIndexMap, F, *F.getParent());
	}

	errs() << "================Global Value Numbering Results:================\n";
	if(removedValues.size() > 0) {
		for(std::set<Value*>::iterator iter = removedValues.begin();
				iter != removedValues.end(); ++iter) {
			errs() << "Checks for this index is duplicated, and it is removed by GVN! \n"
					<< **iter << "\n";
		}
	} else {
		errs() << "Nothing was found with GVN\n";
	}
	errs() << "\n";

	cleanupGlobalSets();

	return true;
}

// Use value table to remove duplicate checks
// Duplicate checks here means, for two variables, i and j
// they have the same checks, and same operations
void ModifiedGVN::removeDuplicateChecks(std::map<GetElementPtrInst*, ArrayIndex*>& arrayIndexMap,
		std::map<BasicBlock*, std::set<GetElementPtrInst*> >& bb2indexs, Function& F,
		std::set<Value*> &removedValues) {
	std::set<GetElementPtrInst*> removedSet;

	// firstly iterate each BB
	for(std::map<BasicBlock*, std::set<GetElementPtrInst*> >::iterator it = bb2indexs.begin();
			it != bb2indexs.end(); ++it) {
		std::set<GetElementPtrInst*> *indexList = &it->second;
		// for each array index pair in this BB
		for(std::set<GetElementPtrInst*>::iterator it1 = indexList->begin();
				it1 != indexList->end(); ++it1) {
			for(std::set<GetElementPtrInst*>::iterator it2 = indexList->begin();
					it2 != indexList->end(); ++it2) {
				// if they are not equal, and none of them is removed before
				if(it1 != it2 && removedSet.find(*it1) == removedSet.end()
						&& removedSet.find(*it2) == removedSet.end()) {
					if(arrayIndexMap.find(*it1) == arrayIndexMap.end() ||
						arrayIndexMap.find(*it2) == arrayIndexMap.end()) {
						errs() << "something went wrong, please check! \n";
					} else {
						// get their index
						ArrayIndex* index1 = arrayIndexMap.find(*it1)->second;
						ArrayIndex* index2 = arrayIndexMap.find(*it2)->second;
						// check their min and max
						if(checkMaxMin(index1, index2)) {
							// check their index
							if(compareValues(index1->index, index2->index)) {
								errs() << "Checks for these two indexes are duplicated! \n"
										<< *index1->index << " with " << *index2->index << "\n";
								removedSet.insert(*it2);
								arrayIndexMap.erase(*it2);
								removedValues.insert(index2->index);
							}
						}
					}
				}
			}
		}
	}
	errs() << "\n";
}

// Iteratively compare two values in value table, check whether their operations are all the same
bool ModifiedGVN::compareValues(Value* v1, Value* v2) {
	Instruction* inst1 = dyn_cast<Instruction> (v1);
	Instruction* inst2 = dyn_cast<Instruction> (v2);
	if(inst1 && inst2) {
		if(inst1->getNumOperands() == inst2->getNumOperands()) {
			// iteratively check each operand
			for(unsigned i = 0; i < inst1->getNumOperands(); i++) {
				Value* op1 = inst1->getOperand(i);
				Value* op2 = inst2->getOperand(i);
				unsigned num1 = VN.find(op1);
				unsigned num2 = VN.find(op2);
				unsigned max = VN.getNextUnusedValueNumber();
				if(num1 >= max || num2 >= max) {
					errs() << "something went wrong when querying value table\n";
					return false;
				}

				// if the operand is an alloca, then we need to check the value stored in the var
				if(isa<AllocaInst> (op1) && isa<AllocaInst> (op2)) {
					AllocaInst* alloca1 = dyn_cast<AllocaInst> (op1);
					AllocaInst* alloca2 = dyn_cast<AllocaInst> (op2);

					Value* storedV1 = findDefValue(inst1, alloca1);
					Value* storedV2 = findDefValue(inst2, alloca2);
					if(storedV1 && storedV2) {
						if((isa<Constant> (storedV1)) && (isa<Constant> (storedV2))) {
							if(storedV1 != storedV2) {
								return false;
							}
						} else { // it both operands are not constant, then check more
							if(!compareValues(storedV1, storedV2)) {
								return false;
							}
						}
					} else { // here means there might be multiple reachable definitions
						return false;
					}
				} else if(num1 != num2) {
					if(!compareValues(op1, op2)) {
						return false;
					}
				}
			}
			return true;
		}
	}

	return false;
}

// start from 'inst', check whether there any definitions for 'alloca' before 'inst'
Value* ModifiedGVN::findDefValue(Instruction* inst, AllocaInst* alloca) {
	BasicBlock* bb = inst->getParent();
	Value* res = NULL;
	for(BasicBlock::iterator instIter = bb->begin(); instIter != bb->end(); ++instIter) {
		if(&(*instIter) == inst) {
			break;
		} else {
			if(isa<StoreInst> (&(*instIter))) {
				StoreInst* storeInst = dyn_cast<StoreInst> (&(*instIter));
				if(storeInst->getOperand(1) == alloca) {
					res = storeInst->getOperand(0);
				}
			}
		}
	}
	if(res) {
		return res;
	}

	std::map<BasicBlock*, std::map<llvm::Value*, std::set<llvm::Instruction*> > >::iterator
		outIter = bb2in.find(bb);
	if(outIter != bb2in.end()) {
		std::map<llvm::Value*, std::set<llvm::Instruction*> >* value2def = &outIter->second;
		std::map<llvm::Value*, std::set<llvm::Instruction*> >::iterator innerIter =
				value2def->find(dyn_cast<Value> (alloca));
		if(innerIter != value2def->end()) {
			if(innerIter->second.size() == 1) {
				return (*innerIter->second.begin())->getOperand(0);
			}
		}
	}

	return NULL;
}

// check whether the upper and lower bound of 2 checks are the same
bool ModifiedGVN::checkMaxMin(ArrayIndex* index1, ArrayIndex* index2) {
	if(index1 && index2) {
		return index1->max == index2->max && index1->min == index2->min;
	} else if(index1 || index2) {
		return false;
	} else {
		return true;
	}
}

/// iterateOnFunction - Executes one iteration of ModifiedGVN
void ModifiedGVN::iterateOnFunction(Function &F) {
	cleanupGlobalSets();

	// Top-down walk of the dominator tree
	// Save the blocks this function have before transformation begins. ModifiedGVN may
	// split critical edge, and hence may invalidate the RPO/DT iterator.
	//
	std::vector<BasicBlock *> BBVect;
	BBVect.reserve(256);
	for (df_iterator<DomTreeNode*> DI = df_begin(DT->getRootNode()), DE =
			df_end(DT->getRootNode()); DI != DE; ++DI)
		BBVect.push_back(DI->getBlock());

	for (std::vector<BasicBlock *>::iterator I = BBVect.begin(), E =
			BBVect.end(); I != E; I++)
		processBlock(*I);
}

bool ModifiedGVN::processBlock(BasicBlock *BB) {
	for (BasicBlock::iterator BI = BB->begin(), BE = BB->end(); BI != BE; ++BI) {
		processInstruction(BI);
	}

	return false;
}

/// processInstruction - When calculating availability, handle an instruction
/// by inserting it into the appropriate sets
bool ModifiedGVN::processInstruction(Instruction *I) {
	// Ignore dbg info intrinsics.
	if (isa<DbgInfoIntrinsic> (I))
		return false;

	if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
		unsigned Num = VN.lookup_or_add(LI);
		addToLeaderTable(Num, LI, LI->getParent());
		return false;
	}

	// For conditional branches, we can perform simple conditional propagation on
	// the condition value itself.
//	if (BranchInst *BI = dyn_cast<BranchInst>(I)) {
//		if (!BI->isConditional())
//			return false;
//
//		Value *BranchCond = BI->getCondition();
//		BasicBlock *TrueSucc = BI->getSuccessor(0);
//		BasicBlock *FalseSucc = BI->getSuccessor(1);
//		// Avoid multiple edges early.
//		if (TrueSucc == FalseSucc)
//			return false;
//
//		BasicBlock *Parent = BI->getParent();
//
//		Value *TrueVal = ConstantInt::getTrue(TrueSucc->getContext());
//		BasicBlockEdge TrueE(Parent, TrueSucc);
//		propagateEquality(BranchCond, TrueVal, TrueE);
//
//		Value *FalseVal = ConstantInt::getFalse(FalseSucc->getContext());
//		BasicBlockEdge FalseE(Parent, FalseSucc);
//		propagateEquality(BranchCond, FalseVal, FalseE);
//
//		return false;
//	}
//
//	// For switches, propagate the case values into the case destinations.
//	if (SwitchInst *SI = dyn_cast<SwitchInst>(I)) {
//		Value *SwitchCond = SI->getCondition();
//		BasicBlock *Parent = SI->getParent();
//
//		// Remember how many outgoing edges there are to every successor.
//		SmallDenseMap<BasicBlock *, unsigned, 16> SwitchEdges;
//		for (unsigned i = 0, n = SI->getNumSuccessors(); i != n; ++i)
//			++SwitchEdges[SI->getSuccessor(i)];
//
//		for (SwitchInst::CaseIt i = SI->case_begin(), e = SI->case_end(); i
//				!= e; ++i) {
//			BasicBlock *Dst = i.getCaseSuccessor();
//			// If there is only a single edge, propagate the case value into it.
//			if (SwitchEdges.lookup(Dst) == 1) {
//				BasicBlockEdge E(Parent, Dst);
//				propagateEquality(SwitchCond, i.getCaseValue(), E);
//			}
//		}
//		return false;
//	}

	// Instructions with void type don't return a value, so there's
	// no point in trying to find redundancies in them.
	if (I->getType()->isVoidTy())
		return false;

	uint32_t NextNum = VN.getNextUnusedValueNumber();
	unsigned Num = VN.lookup_or_add(I);

	// Allocations are always uniquely numbered, so we can save time and memory
	// by fast failing them.
	if (isa<AllocaInst> (I) || isa<TerminatorInst> (I) || isa<PHINode> (I)) {
		addToLeaderTable(Num, I, I->getParent());
		return false;
	}

	// If the number we were assigned was a brand new VN, then we don't
	// need to do a lookup to see if the number already exists
	// somewhere in the domtree: it can't!
	if (Num >= NextNum) {
		addToLeaderTable(Num, I, I->getParent());
		return false;
	}

	// Perform fast-path value-number based elimination of values inherited from
	// dominators.
	Value *repl = findLeader(I->getParent(), Num);
	if (repl == 0) {
		// Failure, just remember this instance for future use.
		addToLeaderTable(Num, I, I->getParent());
		return false;
	}

	errs() << "Maybe need to check this inst: " << *I << "\n";
	return false;
}

void ModifiedGVN::LeaderTableDump() {
	errs() << "=============================================\n";
	errs() << "===========Start dump Leader Table===========\n";
	errs() << "=============================================\n";
	for(DenseMap<uint32_t, LeaderTableEntry>::iterator iter = LeaderTable.begin();
			iter != LeaderTable.end(); ++iter) {
		errs() << "Value: " << iter->first << "\n";
		LeaderTableEntry entry = iter->second;
		while(entry.Val) {
			errs() << *entry.Val << " " << entry.BB->getName() << "\n";
			if(!entry.Next) break;
			entry = *entry.Next;
		}
	}
}

// findLeader - In order to find a leader for a given value number at a
// specific basic block, we first obtain the list of all Values for that number,
// and then scan the list to find one whose block dominates the block in
// question.  This is fast because dominator tree queries consist of only
// a few comparisons of DFS numbers.
Value *ModifiedGVN::findLeader(const BasicBlock *BB, uint32_t num) {
	LeaderTableEntry Vals = LeaderTable[num];
	if (!Vals.Val)
		return 0;

	Value *Val = 0;
	if (DT->dominates(Vals.BB, BB)) {
		Val = Vals.Val;
		if (isa<Constant> (Val))
			return Val;
	}

	LeaderTableEntry* Next = Vals.Next;
	while (Next) {
		if (DT->dominates(Next->BB, BB)) {
			if (isa<Constant> (Next->Val))
				return Next->Val;
			if (!Val)
				Val = Next->Val;
		}

		Next = Next->Next;
	}

	return Val;
}
void ModifiedGVN::findAllArrayIndexs(std::map<GetElementPtrInst*, ArrayIndex*>& arrayIndexMap,
		Function &F, std::map<BasicBlock*, std::set<GetElementPtrInst*> >& bb2indexs) {
	// only used for array initialized with malloc
	std::map<Value*, unsigned> array2size;
	std::map<Value*, Value*> array2unknownSize;

	for(Function::iterator bbIter = F.begin(); bbIter != F.end(); ++bbIter) {
		std::set<GetElementPtrInst*> GEPlist;

		for(BasicBlock::iterator instIter = (*bbIter).begin(); instIter != (*bbIter).end(); ++instIter) {
			if (isa<AllocaInst> (*instIter)) {
				AllocaInst* allocaInst = dyn_cast<AllocaInst> (&(*instIter));
				if(allocaInst->getAllocatedType()->isPointerTy()) {
					array2size[dyn_cast<Value> (allocaInst)] = 0;
				}
			} else if (isa<CallInst> (*instIter)) {
				CallInst* callInst = dyn_cast<CallInst> (&(*instIter));
				// make sure it's a malloc function
				if(callInst->getCalledFunction()->getName().str() == "malloc"
						&& callInst->getNumArgOperands() == 1) {
					// check the allocated size for arrays
					if(isa<Constant>(callInst->getOperand(0))){
						Constant* constant = dyn_cast<Constant> (callInst->getOperand(0));
						unsigned num = constant->getUniqueInteger().getZExtValue();
						for(Value::use_iterator iter = callInst->use_begin(); iter != callInst->use_end(); ++iter) {
							if(isa<BitCastInst> (*iter)) {
								BitCastInst* bitCastInst = dyn_cast<BitCastInst> (*iter);
								for(Value::use_iterator it = bitCastInst->use_begin(); it != bitCastInst->use_end(); ++it) {
									if(isa<StoreInst> (*it)) {
										StoreInst* storeInst =  dyn_cast<StoreInst> (*it);
										array2size[storeInst->getPointerOperand()] = num / 8;;
									}
								}
							}
						}
					} else { // if the allocated size of array is in a variable
						// %mul = mul i64 8, %conv
						Value* arraySize = callInst->getOperand(0);
						Instruction* mulInst = dyn_cast<Instruction> (arraySize);

						// %conv = sext i32 %8 to i64
						Value* sextVal;
						if(mulInst->getNumOperands() == 2) {
							if(!(isa<Constant> (mulInst->getOperand(0)))) {
								sextVal = mulInst->getOperand(0);
							} else if(!(isa<Constant> (mulInst->getOperand(1)))) {
								sextVal = mulInst->getOperand(1);
							} else {
								continue;
							}
						} else {
							continue;
						}

						// %conv = sext i32 %8 to i64
						Instruction* sextInst = dyn_cast<Instruction> (sextVal);

						// find where is the StoreInst to allocate the array
						std::queue<Instruction*> worklist;
						worklist.push(callInst);
						StoreInst* storeInst;
						do{
							Instruction* inst = worklist.front();
							worklist.pop();
							if(isa<StoreInst> (inst)) {
								storeInst =  dyn_cast<StoreInst> (inst);
							}
							for(Value::use_iterator iter = inst->use_begin();
									iter != inst->use_end(); ++iter) {
								worklist.push(dyn_cast<Instruction> (*iter));
							}
						} while (!worklist.empty());

						// if it is in the form of %conv = sext i32 %8 to i64
						// and if we know which array it is
						if(sextInst->getOpcode() == 35 && storeInst) {
							Value* loadVal = sextInst->getOperand(0);
							if(isa <LoadInst> (loadVal)) {
								Instruction* loadInst = dyn_cast<Instruction> (loadVal);

								std::set<Instruction*> visited;
								std::set<Instruction*> result;
								findDefinitions(loadInst, loadInst, visited, result);
								// handle that:
								// int size = 4;
								// bool* test = (bool*) malloc(sizeof(bool)*size);
								if(result.size() == 1) {
									Constant* constant = dyn_cast<Constant> ((*result.begin())->getOperand(0));
									unsigned num = constant->getUniqueInteger().getZExtValue();
									array2size[storeInst->getPointerOperand()] = num;
								} else if(result.size() == 0){
									array2unknownSize[storeInst->getPointerOperand()] = sextInst;
								}
							}
						}
					}
				}
			} else if (isa<GetElementPtrInst> (*instIter)) {
				GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst> (&(*instIter));

				unsigned maxElements;
				Value* unknownMap;
				bool maxUnknown = false;

				// array initialization with [number]
				if (const ArrayType *ar = dyn_cast<ArrayType>(GEP->getPointerOperandType()->getArrayElementType())) {
					maxElements = ar->getNumElements();
				} else { // array initialization with malloc
					if(isa<LoadInst> (GEP->getPointerOperand())) {
						LoadInst* loadInst = dyn_cast<LoadInst>(GEP->getPointerOperand());
						if(array2unknownSize.count(loadInst->getOperand(0)) > 0) {
							unknownMap = array2unknownSize[loadInst->getOperand(0)];
							maxUnknown = true;
						}
						maxElements = array2size[loadInst->getOperand(0)];
					} else {
						errs() << "Some array index cannot be handled!!! \n"
								<< "We will ignore it. \n " << *GEP << "\n";
						continue;
					}
				}

				// for non-constant indices insert call to overflow checking code
				int index = GEP->getNumOperands() - 1;
				Value *v1 = GEP->getOperand(index);

				// if index is constant, then just give compile warnings
				if(isa<Constant> (v1)) {
					Constant* constant = dyn_cast<Constant>(v1);
					// indicating negative numbers
					if(constant->getUniqueInteger().countLeadingOnes() > 0) {
						errs() << "\n[WARNING]"<< *v1 << " is a negative number,"
								<< "it shouldn't be used as array index\n\n";
					} else {
						unsigned num = constant->getUniqueInteger().getZExtValue();
						if(num >= maxElements) {
							errs() << "\n[WARNING]" << *v1 << " is bigger than or equal to "
									<< maxElements << ", which is beyond the array bound\n\n";
						}
					}
				} else {
					Value *v2;
					if(maxUnknown) {
						v2 = unknownMap;
					} else {
						v2 = ConstantInt::get(v1->getType(), maxElements);
					}
					Value *v3 = ConstantInt::get(v1->getType(), 0);

					ArrayIndex* arrayIndex = new ArrayIndex();
					arrayIndex->index = v1;
					arrayIndex->max = v2;
					arrayIndex->min = v3;
					arrayIndexMap[GEP] = arrayIndex;

					GEPlist.insert(GEP);
				}
				errs() << "\n";
			}
		}
		if(GEPlist.size() > 0) {
			bb2indexs[&(*bbIter)] = GEPlist;
		}
	}
}

// A helper function, creat a BB with two statements,
// printf("Array out of bound\n");
// exit(0);
BasicBlock* ModifiedGVN::creatErrorHandleBB(Function* func, Module* M) {
	// create a BB to deal with error
	BasicBlock* errorBB = BasicBlock::Create(func->getContext(), "errorBB", func);

	// create global constant, 0
	ConstantInt* zero = ConstantInt::get(Type::getInt32Ty(func->getContext()), 0);

	// create constant string, "Array out of bound\n"
	ArrayType* ArrayTy = ArrayType::get(IntegerType::get(M->getContext(), 8), 26);
	GlobalVariable* strVar = new GlobalVariable(*M, ArrayTy, true, GlobalValue::PrivateLinkage, 0, ".str");
	strVar->setAlignment(1);
	Constant *outputStr = ConstantDataArray::getString(M->getContext(), "Array index out of bound\x0A", true);
	strVar->setInitializer(outputStr);
	std::vector<Constant*> indices;
	indices.push_back(zero);
	indices.push_back(zero);
	Constant* printArg = ConstantExpr::getGetElementPtr(strVar, indices);

	// create printf function, and insert it to the end of BB
	std::vector<Type*> printfFuncTyArgs;
	printfFuncTyArgs.push_back(PointerType::get(IntegerType::get(M->getContext(), 8), 0));
	FunctionType* printfFuncTy = FunctionType::get(IntegerType::get(M->getContext(), 32), printfFuncTyArgs, true);
	Function* printfFunc = M->getFunction("printf");
	if (!printfFunc) {
		// (external, no body)
		printfFunc = Function::Create(printfFuncTy, GlobalValue::ExternalLinkage, "printf", M);
		printfFunc->setCallingConv(CallingConv::C);
	}
	CallInst::Create(printfFunc, printArg, "", errorBB);

	// create exit(0), and insert it to the end of BB
	std::vector<Type*> exitFuncTyArgs;
	exitFuncTyArgs.push_back(IntegerType::get(M->getContext(), 32));
	FunctionType* exitFuncTy = FunctionType::get(Type::getVoidTy(M->getContext()), exitFuncTyArgs, false);
	Function* exitFunc = M->getFunction("exit");
	if (!exitFunc) {
		// (external, no body)
		exitFunc = Function::Create(exitFuncTy, GlobalValue::ExternalLinkage, "exit", M);
		exitFunc->setCallingConv(CallingConv::C);
	}
	CallInst::Create(exitFunc, zero, "", errorBB);

	// This is inserted to prevent the error: errorBB doesn't have a terminator
	new UnreachableInst(M->getContext(), errorBB);

	return errorBB;
}

BasicBlock* ModifiedGVN::insertAllBoundChecks(std::map<GetElementPtrInst*, ArrayIndex*>& arrayIndexMap,
		Function &F, Module &M) {
	// create a BB to deal with error
	BasicBlock* errorBB = creatErrorHandleBB(&F, &M);
	errorBB->setName(getBBName(true, false));

	// It's a weird BB, it will be deleted eventually, and it's just to prevent core dump happening..
	BasicBlock* emptyBB = BasicBlock::Create(F.getContext(), "emptyBB", &F, 0);

	// iterate each GetElementPtrInst to add array bound checks
	for(std::map<GetElementPtrInst*, ArrayIndex*>::iterator iter = arrayIndexMap.begin();
			iter != arrayIndexMap.end(); ++iter) {
		GetElementPtrInst *GEP = (*iter).first;
		BasicBlock* oldBB = GEP->getParent();
		BasicBlock* bottomBB = GEP->getParent()->splitBasicBlock(GEP);

		BranchInst* brInst = dyn_cast<BranchInst> (oldBB->getTerminator());
		brInst->setOperand(0, dyn_cast<Value> (emptyBB));
		oldBB->getTerminator()->removeFromParent();

		BasicBlock* middleBB = BasicBlock::Create(F.getContext(), "", &F);
		middleBB->setName(getBBName(false, true)); // create BB to check index >= min
		bottomBB->setName(getBBName(false, false)); // create BB to continue original operations

		ICmpInst* maxCmp;
		if(isa<SExtInst> ((*iter).second->max)) {
			SExtInst* sextInst = dyn_cast<SExtInst> ((*iter).second->max);
			Value* loadVal = sextInst->getOperand(0);
			if(isa<LoadInst> (loadVal)) {
				LoadInst* loadInst = dyn_cast<LoadInst> (loadVal);
				LoadInst* newLoad = new LoadInst(loadInst->getOperand(0), "", loadInst->getAlignment(), oldBB);
				SExtInst* newSext = new SExtInst(dyn_cast<Value> (newLoad), sextInst->getType(), "", oldBB);
				maxCmp = new ICmpInst(*oldBB, CmpInst::ICMP_SLT, (*iter).second->index, newSext);
			} else {
				maxCmp = new ICmpInst(*oldBB, CmpInst::ICMP_SLT, (*iter).second->index, (*iter).second->max);
			}
		} else {
			// compare instruction, index < max, it is inserted at the end of original BB
			maxCmp = new ICmpInst(*oldBB, CmpInst::ICMP_SLT, (*iter).second->index, (*iter).second->max);
		}
		// branch instruction
		BranchInst* maxBranch = BranchInst::Create(middleBB, errorBB, maxCmp, oldBB);

		// compare instruction, index >= min, it is inserted at the end of original BB
		ICmpInst* minCmp = new ICmpInst(*middleBB, CmpInst::ICMP_SGE, (*iter).second->index, (*iter).second->min);
		// branch instruction
		BranchInst* minBranch = BranchInst::Create(bottomBB, errorBB, minCmp, middleBB);

		(*iter).second->maxBranch = maxBranch;
		(*iter).second->maxCmp = maxCmp;
		(*iter).second->minBranch = minBranch;
		(*iter).second->minCmp = minCmp;
	}

	emptyBB->removeFromParent();

	// To check the updated IR immediately
	F.dump();

	return errorBB;
}

std::string ModifiedGVN::getBBName(bool isErrorBB, bool isMax) {
	std::string res;
	int count;
	if(isErrorBB) {
		count = errorBBcount++;
		res = "ErrorBB";
	} else {
		if(isMax) {
			count = insertBBcount;
			res = "InsertBBMin";
		} else {
			count = insertBBcount++;
			res = "InsertBBCont";
		}
	}
	std::stringstream ss;
	ss << res  << count;

	return ss.str();
}

// Find definitions for startInstr instruction (load instruction)
// curInstr: current instruction to be handled
// startInstr: the 'load' instruction whose definitions needs to be found
// visited: a set of visited instructions
// result: a set of found definitions
void ModifiedGVN::findDefinitions(Instruction* curInstr, Instruction* startInstr,
		std::set<Instruction*>& visited, std::set<Instruction*>& result){
	if(visited.find(curInstr) == visited.end()){
		visited.insert(curInstr);

		//If found
		if(curInstr->getOpcode() == 28 && curInstr->getOperand(1) == startInstr->getOperand(0)){
			result.insert(curInstr);
			return;
		}

		// If not found, backward traverse
		BasicBlock* curBB = curInstr->getParent();
		Instruction* first = curBB->begin();
		if(curInstr == first){
			// If curInstr is the first instruction of current basic block, back to previous basic blocks
			for(pred_iterator PI = pred_begin(curBB); PI != pred_end(curBB); PI++){
				if(*PI){
					BasicBlock* preBB = *PI;
					// Ignore empty block
					findDefinitions(preBB->getTerminator(), startInstr, visited, result);
				}
			}
		}else{
			findDefinitions(curInstr->getPrevNode(), startInstr, visited, result);
		}
	}
}

void ModifiedGVN::getReachDefs(Function &F) {
	// Iterate all the definitions and assign ID for each store instruction
	std::map<Value*, std::set<Instruction*> > allDefines;
	std::map<Instruction*, int> inst2id;
	int ids = 0;
	for (inst_iterator instIter = inst_begin(F); instIter != inst_end(F); ++instIter) {
		if(dyn_cast<StoreInst>(&(*instIter))) {
			inst2id[&(*instIter)] = ++ids;
			Value* value = (*instIter).getOperand(1);
			std::map<Value*, std::set<Instruction*> >::iterator valueIter = allDefines.find(value);
			if(valueIter != allDefines.end()) {
				(*valueIter).second.insert(&(*instIter));
			} else {
				std::set<Instruction*> set;
				set.insert(&(*instIter));
				allDefines[value] = set;
			}
		}
	}

	// For each BB, for each variable, only consider the last assignment to it
	std::map<BasicBlock*, std::map<Value*, Instruction*> > bb2gen;
	// For each BB, for each variable, there may be multiply instructions that are killed
	std::map<BasicBlock*, std::map<Value*, std::set<Instruction*> > > bb2kill;

	// Compute the GEN and KILL set for each basic block
	for (Function::iterator bbIter = F.begin(); bbIter != F.end(); ++bbIter) {
		std::map<Value*, Instruction*> genMap;
		std::map<Value*, std::set<Instruction*> > killMap;
		for(BasicBlock::iterator instIter = (*bbIter).begin(); instIter != (*bbIter).end(); ++instIter) {
			if(dyn_cast<StoreInst>(&(*instIter))) {
				Value* value = (*instIter).getOperand(1);
				genMap[value] = &(*instIter);

				std::set<Instruction*> defs = allDefines.find(value)->second;
				defs.erase(&(*instIter));
				killMap[value] = defs;
			}
		}
		bb2gen[&(*bbIter)] = genMap;
		bb2kill[&(*bbIter)] = killMap;
	}

	for (Function::iterator bbIter = F.begin(); bbIter != F.end(); ++bbIter) {
		std::map<Value*, std::set<Instruction*> > outMap;
		mapUnion(outMap, bb2gen[&(*bbIter)]);
		bb2out[&(*bbIter)] = outMap;
	}

	bool fixed = false;
	do{
		if(DEBUG) {
			errs() << "This is a new round \n";
		}
		// Update In and Out iteratively, In = U (Out(P)), Out = GEN U (In - Kill)
		std::map<BasicBlock*, std::map<Value*, std::set<Instruction*> > > bb2inNew;
		std::map<BasicBlock*, std::map<Value*, std::set<Instruction*> > > bb2outNew;
		for (Function::iterator bbIter = F.begin(); bbIter != F.end(); ++bbIter) {
			std::map<Value*, std::set<Instruction*> > inMap;
			for(pred_iterator predIterB = pred_begin(&(*bbIter)), predIterE = pred_end(&(*bbIter));
					predIterB != predIterE; ++predIterB) {
				mapUnion(inMap, bb2out[(*predIterB)]);
			}
			bb2inNew[&(*bbIter)] = inMap;

			std::map<Value*, std::set<Instruction*> > outMap;
			outMap = mapSub(inMap, bb2kill[&(*bbIter)]);
			mapUnion(outMap, bb2gen[&(*bbIter)]);
			bb2outNew[&(*bbIter)] = outMap;
		}

		fixed = compare(bb2in, bb2inNew) && compare(bb2out, bb2outNew);

		bb2in = bb2inNew;
		bb2out = bb2outNew;
	} while(!fixed);
}

// add elements from source to target
void ModifiedGVN::mapUnion(std::map<Value*, std::set<Instruction*> > &target,
		std::map<Value*, std::set<Instruction*> > &source) {
	for(std::map<Value*, std::set<Instruction*> >::iterator pair = source.begin();
			pair != source.end(); ++pair) {
		std::map<Value*, std::set<Instruction*> >::iterator targetIter = target.find((*pair).first);
		std::set<Instruction*> set = (*pair).second;
		if(targetIter == target.end()) {
			target[(*pair).first] = set;
		} else {
			for(std::set<Instruction*>::iterator iter = set.begin(); iter != set.end(); ++iter) {
				(*targetIter).second.insert((*iter));
			}
		}
	}
}

// add elements from source to target
void ModifiedGVN::mapUnion(std::map<Value*, std::set<Instruction*> > &target,
		std::map<Value*, Instruction*> &source) {
	for(std::map<Value*, Instruction*>::iterator pair = source.begin(); pair != source.end(); ++pair) {
		if(target.find((*pair).first) == target.end()) {
			std::set<Instruction*> outSet;
			target[(*pair).first] = outSet;
		}
		target[(*pair).first].insert((*pair).second);
	}
}

// return a new map, which is equal to map1 - map2
std::map<Value*, std::set<Instruction*> > ModifiedGVN::mapSub(
		std::map<Value*, std::set<Instruction*> > map1,
		std::map<Value*, std::set<Instruction*> > &map2) {
	// go through each value in map2
	for(std::map<Value*, std::set<Instruction*> >::iterator mapIter = map2.begin();
			mapIter != map2.end(); ++mapIter) {
		// if map1 also contains the value, do sub
		if(map1.find((*mapIter).first) != map1.end()) {
			// go through the instruction set for this value in map2
			for(std::set<Instruction*>::iterator instIter = (*mapIter).second.begin();
					instIter != (*mapIter).second.end(); ++instIter) {
				map1[(*mapIter).first].erase(*instIter);
			}
		}
	}

	return map1;
}

// compare 2 maps, return true if all the values are same
bool ModifiedGVN::compare(std::map<BasicBlock*, std::map<Value*, std::set<Instruction*> > > &map1,
		std::map<BasicBlock*, std::map<Value*, std::set<Instruction*> > > &map2) {
	if(map1.size() != map2.size()) {
		return false;
	}
	for(std::map<BasicBlock*, std::map<Value*, std::set<Instruction*> > >::iterator map1Iter = map1.begin();
			map1Iter != map1.end(); ++map1Iter) {
		std::map<BasicBlock*, std::map<Value*, std::set<Instruction*> > >::iterator map2Iter
				= map2.find((*map1Iter).first);
		if(map2Iter == map2.end()) {
			return false;
		} else {
			if(!compare((*map1Iter).second, (*map2Iter).second)) {
				return false;
			}
		}
	}
	return true;
}

// compare 2 maps, return true if all the values are same
bool ModifiedGVN::compare(std::map<Value*, std::set<Instruction*> > &map1,
		std::map<Value*, std::set<Instruction*> > &map2) {
	if(map1.size() != map2.size()) {
		return false;
	}
	for(std::map<Value*, std::set<Instruction*> >::iterator map1Iter = map1.begin();
			map1Iter != map1.end(); ++map1Iter) {
		std::map<Value*, std::set<Instruction*> >::iterator map2Iter = map2.find((*map1Iter).first);
		if(map2Iter == map2.end()) {
			return false;
		} else {
			if((*map1Iter).second.size() != (*map2Iter).second.size()) {
				return false;
			}
			for(std::set<Instruction*>::iterator setIter = (*map1Iter).second.begin();
					setIter != (*map1Iter).second.end(); ++setIter) {
				if((*map2Iter).second.find(*setIter) == (*map2Iter).second.end()) {
					return false;
				}
			}
		}
	}

	return true;
}

void ModifiedGVN::dumpReachDef(Function &F) {
	for (Function::iterator bbIter = F.begin(); bbIter != F.end(); ++bbIter) {
		errs() << "Basic Block: " << (*bbIter).getName() << "\n";

		errs() << "IN set: \n";
		for(std::map<Value*, std::set<Instruction*> >::iterator mapIter = bb2in[&(*bbIter)].begin();
				mapIter != bb2in[&(*bbIter)].end(); ++mapIter) {
			for(std::set<Instruction*>::iterator setIter = (*mapIter).second.begin();
					setIter != (*mapIter).second.end(); ++setIter) {
				errs() << (*mapIter).first->getName() << " : " << (*(*setIter)) << "\n";
			}
		}

		errs() << "OUT set: \n";
		for(std::map<Value*, std::set<Instruction*> >::iterator mapIter = bb2out[&(*bbIter)].begin();
				mapIter != bb2out[&(*bbIter)].end(); ++mapIter) {
			for(std::set<Instruction*>::iterator setIter = (*mapIter).second.begin();
					setIter != (*mapIter).second.end(); ++setIter) {
				errs() << (*mapIter).first->getName() << " : " << (*(*setIter)) << "\n";
			}
		}
		errs() << "\n";
	}
}

/// isOnlyReachableViaThisEdge - There is an edge from 'Src' to 'Dst'.  Return
/// true if every path from the entry block to 'Dst' passes via this edge.  In
/// particular 'Dst' must not be reachable via another edge from 'Src'.
static bool isOnlyReachableViaThisEdge(const BasicBlockEdge &E,
		DominatorTree *DT) {
	// While in theory it is interesting to consider the case in which Dst has
	// more than one predecessor, because Dst might be part of a loop which is
	// only reachable from Src, in practice it is pointless since at the time
	// ModifiedGVN runs all such loops have preheaders, which means that Dst will have
	// been changed to have only one predecessor, namely Src.
	const BasicBlock *Pred = E.getEnd()->getSinglePredecessor();
	const BasicBlock *Src = E.getStart();
	assert((!Pred || Pred == Src) && "No edge between these basic blocks!");
	(void) Src;
	return Pred != 0;
}

/// propagateEquality - The given values are known to be equal in every block
/// dominated by 'Root'.  Exploit this, for example by replacing 'LHS' with
/// 'RHS' everywhere in the scope.  Returns whether a change was made.
void ModifiedGVN::propagateEquality(Value *LHS, Value *RHS, const BasicBlockEdge &Root) {
	SmallVector<std::pair<Value*, Value*>, 4> Worklist;
	Worklist.push_back(std::make_pair(LHS, RHS));
	// For speed, compute a conservative fast approximation to
	// DT->dominates(Root, Root.getEnd());
	bool RootDominatesEnd = isOnlyReachableViaThisEdge(Root, DT);

	while (!Worklist.empty()) {
		std::pair<Value*, Value*> Item = Worklist.pop_back_val();
		LHS = Item.first;
		RHS = Item.second;

		if (LHS == RHS)
			continue;
		assert(LHS->getType() == RHS->getType() && "Equality but unequal types!");

		// Don't try to propagate equalities between constants.
		if (isa<Constant> (LHS) && isa<Constant> (RHS))
			continue;

		// Prefer a constant on the right-hand side, or an Argument if no constants.
		if (isa<Constant> (LHS)
				|| (isa<Argument> (LHS) && !isa<Constant> (RHS)))
			std::swap(LHS, RHS);
		assert((isa<Argument>(LHS) || isa<Instruction>(LHS)) && "Unexpected value!");

		// If there is no obvious reason to prefer the left-hand side over the right-
		// hand side, ensure the longest lived term is on the right-hand side, so the
		// shortest lived term will be replaced by the longest lived.  This tends to
		// expose more simplifications.
		uint32_t LVN = VN.lookup_or_add(LHS);
		if ((isa<Argument> (LHS) && isa<Argument> (RHS)) || (isa<Instruction> (
				LHS) && isa<Instruction> (RHS))) {
			// Move the 'oldest' value to the right-hand side, using the value number as
			// a proxy for age.
			uint32_t RVN = VN.lookup_or_add(RHS);
			if (LVN < RVN) {
				std::swap(LHS, RHS);
				LVN = RVN;
			}
		}

		// If value numbering later sees that an instruction in the scope is equal
		// to 'LHS' then ensure it will be turned into 'RHS'.  In order to preserve
		// the invariant that instructions only occur in the leader table for their
		// own value number (this is used by removeFromLeaderTable), do not do this
		// if RHS is an instruction (if an instruction in the scope is morphed into
		// LHS then it will be turned into RHS by the next ModifiedGVN iteration anyway, so
		// using the leader table is about compiling faster, not optimizing better).
		// The leader table only tracks basic blocks, not edges. Only add to if we
		// have the simple case where the edge dominates the end.
		if (RootDominatesEnd && !isa<Instruction> (RHS))
			addToLeaderTable(LVN, RHS, Root.getEnd());

		// Now try to deduce additional equalities from this one.  For example, if the
		// known equality was "(A != B)" == "false" then it follows that A and B are
		// equal in the scope.  Only boolean equalities with an explicit true or false
		// RHS are currently supported.
		if (!RHS->getType()->isIntegerTy(1))
			// Not a boolean equality - bail out.
			continue;
		ConstantInt *CI = dyn_cast<ConstantInt> (RHS);
		if (!CI)
			// RHS neither 'true' nor 'false' - bail out.
			continue;
		// Whether RHS equals 'true'.  Otherwise it equals 'false'.
		bool isKnownTrue = CI->isAllOnesValue();
		bool isKnownFalse = !isKnownTrue;

		// If "A && B" is known true then both A and B are known true.  If "A || B"
		// is known false then both A and B are known false.
		Value *A, *B;
		if ((isKnownTrue && match(LHS, m_And(m_Value(A), m_Value(B))))
				|| (isKnownFalse && match(LHS, m_Or(m_Value(A), m_Value(B))))) {
			Worklist.push_back(std::make_pair(A, RHS));
			Worklist.push_back(std::make_pair(B, RHS));
			continue;
		}

		// If we are propagating an equality like "(A == B)" == "true" then also
		// propagate the equality A == B.  When propagating a comparison such as
		// "(A >= B)" == "true", replace all instances of "A < B" with "false".
		if (ICmpInst *Cmp = dyn_cast<ICmpInst>(LHS)) {
			Value *Op0 = Cmp->getOperand(0), *Op1 = Cmp->getOperand(1);

			// If "A == B" is known true, or "A != B" is known false, then replace
			// A with B everywhere in the scope.
			if ((isKnownTrue && Cmp->getPredicate() == CmpInst::ICMP_EQ)
					|| (isKnownFalse && Cmp->getPredicate() == CmpInst::ICMP_NE))
				Worklist.push_back(std::make_pair(Op0, Op1));

			// If "A >= B" is known true, replace "A < B" with false everywhere.
			CmpInst::Predicate NotPred = Cmp->getInversePredicate();
			Constant *NotVal = ConstantInt::get(Cmp->getType(), isKnownFalse);
			// Since we don't have the instruction "A < B" immediately to hand, work out
			// the value number that it would have and use that to find an appropriate
			// instruction (if any).
			uint32_t Num = VN.lookup_or_add_cmp(Cmp->getOpcode(), NotPred, Op0,
					Op1);

			// Ensure that any instruction in scope that gets the "A < B" value number
			// is replaced with false.
			// The leader table only tracks basic blocks, not edges. Only add to if we
			// have the simple case where the edge dominates the end.
			if (RootDominatesEnd)
				addToLeaderTable(Num, NotVal, Root.getEnd());

			continue;
		}
	}
}

/// Split the critical edge connecting the given two blocks, and return
/// the block inserted to the critical edge.
BasicBlock *ModifiedGVN::splitCriticalEdges(BasicBlock *Pred, BasicBlock *Succ) {
	BasicBlock *BB = SplitCriticalEdge(Pred, Succ, this);
	if (MD)
		MD->invalidateCachedPredecessors();
	return BB;
}

/// splitCriticalEdges - Split critical edges found during the previous
/// iteration that may enable further optimization.
bool ModifiedGVN::splitCriticalEdges() {
	if (toSplit.empty())
		return false;
	do {
		std::pair<TerminatorInst*, unsigned> Edge = toSplit.pop_back_val();
		SplitCriticalEdge(Edge.first, Edge.second, this);
	} while (!toSplit.empty());
	if (MD)
		MD->invalidateCachedPredecessors();
	return true;
}

void ModifiedGVN::cleanupGlobalSets() {
	VN.clear();
	LeaderTable.clear();
	TableAllocator.Reset();
}

static RegisterPass<ModifiedGVN> X("part3", "Array bound check part3", false, false);
