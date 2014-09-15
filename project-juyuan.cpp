#include "llvm/Pass.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/CallingConv.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Analysis/ConstantFolding.h"

#include <map>
#include <set>
#include <queue>
#include <sstream>

using namespace llvm;

namespace {

struct project: public ModulePass {
	static char ID;
	static int errorBBcount;
	static int insertBBcount;
	project() :
		ModulePass(ID) {
	}

	struct ArrayIndex {
		Value* max;
		Value* min;
		Value* index;
		BranchInst* maxBranch;
		BranchInst* minBranch;
		ICmpInst* maxCmp;
		ICmpInst* minCmp;
	};

	struct MCFG_Node {
		std::string label;
		std::vector<Instruction*> instrs;
		std::set<MCFG_Node*> preds;
		std::set<MCFG_Node*> succs;
	};

	virtual bool runOnModule(Module &M) {
		for(Module::iterator funcIter = M.begin(); funcIter != M.end(); ++funcIter) {
			errs() << "\nCurrent function is: " << funcIter->getName() << " \n";

			std::map<GetElementPtrInst*, ArrayIndex*> arrayIndexMap;

			/////////////////////////////////////////////////////
			// Baseline, add all array bound checks
			/////////////////////////////////////////////////////
			// first go through the program, find all GetElementPtrInsts and add them to a map
			findAllArrayIndexs(arrayIndexMap, *funcIter);

			if(arrayIndexMap.size() > 0) {
				insertAllBoundChecks(arrayIndexMap, *funcIter, M);
			} else {
				// If there is no array index instructions, then just skip this function
				continue;
			}

			/////////////////////////////////////////////////////
			// Construct MCFG
			/////////////////////////////////////////////////////
			// Step 1: get all related instructions for given array index and cmp instruction (including, load, store, alloc)
//			std::set<Instruction*> allInstrs;
//		    getAllRelatedInstrs(arrayIndexMap, *funcIter, allInstrs);
//
//		    // Step 2: construct MCFG given function CFG and all related instructions set
//		    std::vector<MCFG_Node*> MCFG;
//		    // Step 2.0: Initialize MCFG (copy CFG)
//		    initializeMCFG(*funcIter, MCFG);
//		    // Step 2.1: Only leave array subscript expression and definitions related
//			optimizeMCFG1(allInstrs, MCFG);
//			// Step 2.2: Remove empty nodes and duplicate edges (T1, T2, T3, figure 3, def-use optimization in the paper).
//			// Refer to comments above function declaration for more details of optimizations conducted
//			optimizeMCFG2(MCFG);
//			// Step 2.3: Merge check nodes (T4, T5, T6)
//			optimizeMCFG3(MCFG);
//
//			// Print constructed MCFG
//			printMCFG(MCFG);

			errs() << "\n";
		}

		return true;
	}

	void insertAllBoundChecks(std::map<GetElementPtrInst*, ArrayIndex*>& arrayIndexMap, Function &F, Module &M) {
		// create a BB to deal with error
		BasicBlock* errorBB = creatErrorHandleBB(&F, &M);
		errorBB->setName(getBBName(true, false));

		// iterate each GetElementPtrInst to add array bound checks
		for(std::map<GetElementPtrInst*, ArrayIndex*>::iterator iter = arrayIndexMap.begin();
				iter != arrayIndexMap.end(); ++iter) {
			GetElementPtrInst *GEP = (*iter).first;
			BasicBlock* oldBB = GEP->getParent();
			BasicBlock* bottomBB = GEP->getParent()->splitBasicBlock(GEP);
			oldBB->getTerminator()->removeFromParent();
			BasicBlock* middleBB = BasicBlock::Create(F.getContext(), "", &F);
			middleBB->setName(getBBName(false, true));
			bottomBB->setName(getBBName(false, false));

			// compare instruction, index < max, it is inserted at the end of original BB
			ICmpInst* maxCmp = new ICmpInst(*oldBB, CmpInst::ICMP_SLT, (*iter).second->index, (*iter).second->max);
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

		// To check the updated IR immediately
		F.dump();
	}

	std::string getBBName(bool isErrorBB, bool isMax) {
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

	void findAllArrayIndexs(std::map<GetElementPtrInst*, ArrayIndex*>& arrayIndexMap, Function &F) {
		// only used for array initialized with malloc
		std::map<Value*, unsigned> array2size;

		for(Function::iterator bbIter = F.begin(); bbIter != F.end(); ++bbIter) {
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
						}
					}
				} else if (isa<GetElementPtrInst> (*instIter)) {
					GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst> (&(*instIter));

					errs() << *GEP << "\n" << *GEP->getPointerOperandType() <<
							*GEP->getPointerOperand() << "\n";
//					errs() << *GEP->getPointerOperand() << "\n";
//					errs() << GEP->getPointerOperandType()->getArrayElementType()->getArrayNumElements() << "\n";

					unsigned maxElements;

					// array initialization with [number]
					if (const ArrayType *ar = dyn_cast<ArrayType>(GEP->getPointerOperandType()->getArrayElementType())) {
						maxElements = ar->getNumElements();
					} else { // array initialization with malloc
						if(isa<LoadInst> (GEP->getPointerOperand())) {
							LoadInst* loadInst = dyn_cast<LoadInst>(GEP->getPointerOperand());
							errs() << array2size[loadInst->getOperand(0)] << "\n";
							maxElements = array2size[loadInst->getOperand(0)];
						} else {
							errs() << "Some array index cannot be handled!!! \n";
							exit(0);
						}
					}

					// TODO: check for constant and non-constant indices
					// compile time warning for constant indices
					// like A[100]

					// for non-constant indices insert call to overflow checking code
					int index = GEP->getNumOperands() - 1;
					Value *v1 = GEP->getOperand(index);
					Value *v2 = ConstantInt::get(v1->getType(), maxElements);
					Value *v3 = ConstantInt::get(v1->getType(), 0);
//					errs() << *v1 << "\n";

					ArrayIndex* arrayIndex = new ArrayIndex();
					arrayIndex->index = v1;
					arrayIndex->max = v2;
					arrayIndex->min = v3;
					arrayIndexMap[GEP] = arrayIndex;

					errs() << "\n";
				}
			}
		}
	}

	// A helper function, creat a BB with two statements,
	// printf("Array out of bound\n");
	// exit(0);
	BasicBlock* creatErrorHandleBB(Function* func, Module* M) {
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

	// Step 1 optimization of initialized MCFG: Only leave array subscript expressions and definitions related
	void optimizeMCFG1(std::set<Instruction*>& allInstrs, std::vector<MCFG_Node*>& MCFG) {
			// Step 1: Remove all inrelevant instructions. Only leave array subscript expression and definitions related.
			for(std::vector<MCFG_Node*>::iterator it = MCFG.begin(); it != MCFG.end(); it++){
				MCFG_Node* curNode = *it;
				std::vector<Instruction*> remained;

				for(std::vector<Instruction*>::iterator it2 = curNode->instrs.begin(); it2 != curNode->instrs.end(); ++it2){
					Instruction* curInstr = *it2;
					if(allInstrs.find(curInstr) != allInstrs.end()){
						remained.push_back(curInstr);
					}
				}

				curNode->instrs = remained;
			}

		}

	// Step 2 optimization of initialized MCFG: Remove empty nodes and redundant edges
	// (T1, T2, T3, figure 3, def-use optimization in the paper)
	/*
	 * 1. T3 is not necessary, as we checked duplicated edges while updating predecessors and successors
	 * 2. It is unnecessary to conduct optimization (page 276) "after the MCFG is constructed, use-def information
	 * for only the range checks is computed.If a definition included in the MCFG is not used by any of the range
	 * checks it is eliminated.". It is because that when we compute related instructions by method (getAllRelatedInstrs),
	 * we use a backward traverse starting from the range check (cmp instruction) and only find the latest definitions used
	 * in the range check then stop. All other definitions which would be killed are ignored.
	 */
	void optimizeMCFG2(std::vector<MCFG_Node*>& MCFG){
		// Unnecessary to apply T3 optimization (remove duplicated edges), since:
		// 1) During initialization, no duplicated edges
		// 2) When updating predecessors/successors after removing empty nodes, no duplicated edges
		std::vector<MCFG_Node*> toRemove;

		for(unsigned i=0; i<MCFG.size(); i++){
			MCFG_Node* curNode = MCFG[i];
			if(curNode->instrs.empty()){
				// Apply T2 optimization (remove self loop)
				if(curNode->preds.find(curNode) != curNode->preds.end()){
					curNode->preds.erase(curNode);
					curNode->succs.erase(curNode);
					i--;
					continue;
				}

				// Apply T1 optimization (remove empty node and update predecessors and successors) after all self loops for current node are removed
				toRemove.push_back(curNode);
				// Update predecessors and successors
				std::set<MCFG_Node*> predes = curNode->preds;
				std::set<MCFG_Node*> succs = curNode->succs;

				if(!predes.empty() && !succs.empty()){
					if(predes.size() == 1 || succs.size() == 1){
						// If current node has both predecessors and successors, connect predecessors to successors
						// Also apply the optimization illustrated in figure 3 here
						for (std::set<MCFG_Node*>::iterator predI =
								predes.begin(); predI != predes.end();
								predI++) {
							MCFG_Node* pre_node = *predI;
							for (std::set<MCFG_Node*>::iterator succI =
									succs.begin(); succI != succs.end();
									succI++) {
								MCFG_Node* succ_node = *succI;

								// Update successors (do not insert duplicated ones)
								pre_node->succs.erase(curNode);
								if (pre_node->succs.find(succ_node)
										== pre_node->succs.end()) {
									pre_node->succs.insert(succ_node);
								}

								// Update predecessors (do not insert duplicated ones)
								succ_node->preds.erase(curNode);
								if (succ_node->preds.find(pre_node)
										== succ_node->preds.end()) {
									succ_node->preds.insert(pre_node);
								}
							}
						}
					}
				}else if(predes.empty() && !succs.empty()){
					// If current node only has successors, remove current node from predecessor list of each successor
					for (std::set<MCFG_Node*>::iterator succI = succs.begin(); succI != succs.end(); succI++) {
						MCFG_Node* succ_node = *succI;
					    succ_node->preds.erase(curNode);
					}
				}else if(!predes.empty() && succs.empty()){
					// If current node only has predecessors, remove current node from successor list of each predecessor
					for (std::set<MCFG_Node*>::iterator predI = predes.begin(); predI != predes.end(); predI++) {
						MCFG_Node* pre_node = *predI;
						pre_node->succs.erase(curNode);
					}
				}

			}
		}

		// Remove empty nodes
		for(std::vector<MCFG_Node*>::iterator removeI = toRemove.begin(); removeI != toRemove.end(); removeI++){
			MCFG_Node* curNode = *removeI;
			// Remove empty node first
			std::vector<MCFG_Node*>::iterator it = std::find(MCFG.begin(),
					MCFG.end(), curNode);
			MCFG.erase(it);
		}
	}

	/*
	 * Step 3: Optimization by applying T4, T5, T6 (only combine here)
	 * 1. Check whether a node only contains 'check' (no 'store' instructions)
	 * 2. If only checks, remove self loop if it has ( we don't remove self-loop here, to help hoist loop invariant later)
	 * 3. Apply T5 and T6, i.e. combine T5 and T6 together, if predecessor only has one successor, and current node only has one predecessor
	 * move current node to predecessor
	 */
	void optimizeMCFG3(std::vector<MCFG_Node*>& MCFG){
		for(unsigned i=0; i<MCFG.size(); i++){
			MCFG_Node* curNode = MCFG[i];

			// Check if single predecessor - single successor
			if(curNode->preds.size() == 1 && (*(curNode->preds.begin()))->succs.size() == 1){
				// Merge current node to its predecessor
				MCFG_Node* pred = *(curNode->preds.begin());
				std::set<MCFG_Node*> succs = curNode->succs;

				// Merge instructions first
				for(std::vector<Instruction*>::iterator it = curNode->instrs.begin(); it != curNode->instrs.end(); it++){
					pred->instrs.push_back(*it);
				}

				// Connect predecessor and successors
				pred->succs.erase(curNode);
				curNode->preds.erase(pred);
				for(std::set<MCFG_Node*>::iterator it2 = succs.begin(); it2 != succs.end(); it2++){
					pred->succs.insert(*it2);
					(*it2)->preds.insert(pred);
					(*it2)->preds.erase(curNode);
				}
			}
		}

	}

	void initializeMCFG(Function& F, std::vector<MCFG_Node*>& MCFG) {
			// Basic block <--> MCFG node
			std::map<BasicBlock*, MCFG_Node*> visited;
			std::vector<BasicBlock*> worklist;
			for (Function::iterator bbIt = F.begin(); bbIt != F.end(); ++bbIt) {
				BasicBlock* bb = bbIt;
				MCFG_Node* node = new MCFG_Node() ;

				for (BasicBlock::iterator instrIt = bb->begin();
						instrIt != bb->end(); ++instrIt) {
					Instruction* curInstr = instrIt;
					node->instrs.push_back(curInstr);
				}
				node->label = bb->getName();

				// Add the new visited node to MCFG
				MCFG.push_back(node);

				// Mark the basic block as visited
				visited[bb] = node;

				//Resolve predecessors
				for (pred_iterator PI = pred_begin(bb); PI != pred_end(bb); PI++) {
					BasicBlock* pred = *PI;
					// If the predecessor is visited, resolve the predecessor for current block
					if (visited.find(pred) != visited.end()) {
						MCFG_Node* pred_node = visited[pred];

						// Do not insert duplicated predecessors and successors
						if(node->preds.find(pred_node) == node->preds.end()){
							node->preds.insert(pred_node);
						}

						if(pred_node->succs.find(node) == pred_node->succs.end()){
							pred_node->succs.insert(node);
						}
					}
				}

				// Resolve successors
				for (succ_iterator SI = succ_begin(bb); SI != succ_end(bb); SI++) {
					BasicBlock* succ = *SI;
					if (visited.find(succ) != visited.end()) {
						MCFG_Node* succ_node = visited[succ];

						// Do not insert duplicated predecessors and successors
					   if (node->succs.find(succ_node) == node->succs.end()) {
						  node->succs.insert(succ_node);
					   }

					   if(succ_node->preds.find(node) == succ_node->preds.end()){
						   succ_node->preds.insert(node);
					   }
					}
				}
			}
		}

	void printCFG(Function& F){
			errs() << "-------------------------------------------------------\n";
			errs() << "# Print CFG:\n";
			errs() << "-------------------------------------------------------\n";
			BasicBlock* entry = &F.getEntryBlock();
			std::queue<BasicBlock*> worklist;
			std::set<BasicBlock*> visited;
			worklist.push(entry);

			while(!worklist.empty()){
				BasicBlock* curBB = worklist.front();
				worklist.pop();

				if(visited.find(curBB) == visited.end()){
					errs() << "# [" << curBB->getName() << "]\n";
					for (BasicBlock::iterator instrIt = curBB->begin();
							instrIt != curBB->end(); ++instrIt) {
						Instruction* curInstr = instrIt;
						errs() << "    " << *curInstr << "\n";
					}
					errs() << "\n";

					visited.insert(curBB);
					for (succ_iterator SI = succ_begin(curBB);
							SI != succ_end(curBB); ++SI) {
						BasicBlock* nextBB = *SI;
						if (visited.find(nextBB) == visited.end()) {
							worklist.push(nextBB);
						}
					}
				}

			}
	//		for (Function::iterator bbIt = F.begin(); bbIt != F.end(); bbIt++) {
	//					BasicBlock* bb = bbIt;
	//					errs() << "# Current basic block [" << bb->getName() << "]\n";
	//
	//					for (BasicBlock::iterator instrIt = bb->begin();
	//							instrIt != bb->end(); instrIt++) {
	//						Instruction* curInstr = instrIt;
	//						errs() << "    " << *curInstr << "\n";
	//					}
	//
	//					errs() << "\n";
	//		}

		}

	void printMCFG(std::vector<MCFG_Node*>& MCFG){
			errs() << "-------------------------------------------------------\n";
			errs() << "# Print MCFG:\n";
			errs() << "-------------------------------------------------------\n";
			MCFG_Node* entry = *(MCFG.begin());
			std::queue<MCFG_Node*> worklist;
			std::set<MCFG_Node*> visited;
			worklist.push(entry);

			while (!worklist.empty()) {
				MCFG_Node* curNode = worklist.front();
				worklist.pop();

				if(visited.find(curNode) == visited.end()){
					errs() << "# [" << curNode->label << "]                     ";

					// Print predecessors
					errs() << ";preds = ";
					for(std::set<MCFG_Node*>::iterator preI = curNode->preds.begin(); preI != curNode->preds.end(); preI++){
						errs() << (*preI)->label << ", ";
					}
					errs() << "\n";

					for (std::vector<Instruction*>::iterator it =
							curNode->instrs.begin(); it != curNode->instrs.end();
							++it) {
						Instruction* curInstr = *it;
						errs() << "    " << *curInstr << "\n";
					}
					errs() << "\n";

					visited.insert(curNode);
					for (std::set<MCFG_Node*>::iterator it2 =
							curNode->succs.begin(); it2 != curNode->succs.end();
							++it2) {
						MCFG_Node* nextNode = *it2;
						if (visited.find(nextNode) == visited.end()) {
							worklist.push(nextNode);
						}
					}
				}

			}
		}

	void getAllRelatedInstrs(std::map<GetElementPtrInst*, ArrayIndex*>& arrayIndexMap, Function& F,
			std::set<Instruction*>& allInstrs){
		errs() << "-------------------------------------------------------\n";
		errs() << "# All relevant instructions:\n";
		errs() << "-------------------------------------------------------\n";
		for(std::map<GetElementPtrInst*, ArrayIndex*>::iterator it = arrayIndexMap.begin(); it != arrayIndexMap.end(); it++){
			ArrayIndex* curIndex = (*it).second;
			Instruction* maxCmp = curIndex->maxCmp;
			Instruction* minCmp = curIndex->minCmp;
			Instruction* varInstr = dyn_cast<Instruction>(curIndex->index);

			allInstrs.insert(maxCmp);
			allInstrs.insert(minCmp);
			allInstrs.insert(varInstr);
			errs() << *maxCmp << "\n";
			errs() << *minCmp << "\n";
			errs() << *varInstr << "\n";

			std::stack<llvm::Use*> worklist;
			for(Instruction::op_iterator opI = varInstr->op_begin(); opI != varInstr->op_end(); ++opI){
				worklist.push(&*opI);
			}

			while (!worklist.empty()) {
				llvm::Use* var = worklist.top();
				worklist.pop();

				Constant *op = dyn_cast<Constant>(var);
				if (!op) {
					// Do not consider constant value
					errs() << *(*var) << "\n ";
					Instruction* inst = dyn_cast<Instruction>((*var));
					allInstrs.insert(inst);

					// Add all the operands to the list
					for (Instruction::op_iterator opI = (*inst).op_begin();
							opI != (*inst).op_end(); ++opI) {
						worklist.push(&*opI);
					}

					// If it is a 'load' instruction, need to find the closest 'store' instruction
					if(inst->getOpcode() == 27){
						std::set<Instruction*> visited;
						std::set<Instruction*> result;
						findDefinitions(inst, inst, visited, result);
						for(std::set<Instruction*>::iterator defI = result.begin(); defI != result.end(); defI++){
							errs() << **defI << "\n";
							allInstrs.insert(*defI);
						}
					}
				}
			}
		}
	}

	// Find definitions for startInstr instruction (load instruction)
	// curInstr: current instruction to be handled
	// startInstr: the 'load' instruction whose definitions needs to be found
	// visited: a set of visited instructions
	// result: a set of found definitions
	void findDefinitions(Instruction* curInstr, Instruction* startInstr, std::set<Instruction*>& visited, std::set<Instruction*>& result){
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

};
}

char project::ID = 0;
int project::errorBBcount = 0;
int project::insertBBcount = 0;
static RegisterPass<project> X("project_juyuan", "Array bound check", false, false);
