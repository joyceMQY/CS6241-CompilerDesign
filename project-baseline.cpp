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

	virtual bool runOnModule(Module &M) {
		for(Module::iterator funcIter = M.begin(); funcIter != M.end(); ++funcIter) {
			errs() << "\nCurrent function is: " << funcIter->getName() << "\n";

			std::map<GetElementPtrInst*, ArrayIndex*> arrayIndexMap;

			/////////////////////////////////////////////////////
			// Baseline, add all array bound checks
		    ///////////////////////////////////////////////////
			// first go through the program, find all GetElementPtrInsts and add them to a map
			findAllArrayIndexs(arrayIndexMap, *funcIter);

			if(arrayIndexMap.size() > 0) {
				insertAllBoundChecks(arrayIndexMap, *funcIter, M);
			} else {
				// If there is no array index instructions, then just skip this function
				continue;
			}
		}

		return true;
	}

	BasicBlock* insertAllBoundChecks(std::map<GetElementPtrInst*, ArrayIndex*>& arrayIndexMap,
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
		std::map<Value*, Value*> array2unknownSize;

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
					}
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
static RegisterPass<project> X("part1", "Array bound check", false, false);
