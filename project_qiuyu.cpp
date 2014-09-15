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
#include <list>
#include <queue>
#include <iostream>
#include <sstream>
#include <string>
#include <stdlib.h>     /* atoi */

using namespace llvm;

namespace {

struct project: public ModulePass {
	static char ID;
	static int errorBBcount;
	static int insertBBcount;
	project() :
		ModulePass(ID) {
	}

	enum EffectType { unchanged = 0, increment = 1, decrement = 2, multiply = 3, divgt1 = 4, divlt1 = 5, changed = -1};

	enum CheckExprType { singleVar = 1, fv_vInc_fDec = 2, fv_vDec_fDec = 3, fv_vInc_fInc = 4, fv_vDec_fInc = 5};

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
		BasicBlock* bb;
		std::vector<Instruction*> instrs;
		std::set<MCFG_Node*> preds;
		std::set<MCFG_Node*> succs;
	};

	struct SimpleArrayIndex {
		std::string index_expr;
		Constant* max;
		Constant* min;
		std::set<Instruction*> def_instrs;
	};

	// Computed a structure for ArrayIndex to include all details to help eliminate duplications
	struct RangeCheck {
		Instruction* check;
		bool checkMax;
		CheckExprType checkExprType;
		std::string index_expr; // Expression example: (a + 1 -> add.1.load.a., 10*b+5+20*a+6 -> add.6.add.mul.20.load.a.add.5.mul.10.load.b.)
		std::set<Instruction*> def_instrs; // Definitions of the identifies used in the subscript expression
	};

	// Computed a structure for ArrayIndex to include all details to help eliminate duplications
	struct ComputedArrayIndex {
		Value* index;    // Instruction of the array index (e.g.  %idxprom2 = sext i32 %add to i64)
		ICmpInst* maxCmp;      // Upper bound of the array
		ICmpInst* minCmp;      // Lower bound of the array
		// Expression example: (a + 1 -> add.1.load.a., 10*b+5+20*a+6 -> add.6.add.mul.20.load.a.add.5.mul.10.load.b.)
		std::string index_expr;  // String that encodes the index subscript expression
		std::set<Instruction*> def_instrs;  // Definitions of the identifies used in the subscript expression
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

			/////////////////////////////////////////////////////
			// Construct MCFG
			/////////////////////////////////////////////////////
			// Step 1: get all related instructions for given array index and cmp instruction (including, load, store, alloc)
			std::set<Instruction*> allInstrs;
			std::map<Value*, RangeCheck*> rangeChecks;
		    getAllRelatedInstrs(arrayIndexMap, *funcIter, allInstrs, rangeChecks);
		   // printComputedIndexes(computedIndexes);
		    // Step 2: construct MCFG given function CFG and all related instructions set
		    std::vector<MCFG_Node*> MCFG;
		    constructMCFG(*funcIter, allInstrs, MCFG);

		    /////////////////////////////////////////////////////
		    // Local Elimination
		    /////////////////////////////////////////////////////
		    std::set<Value*> toRemoveChecks;
		    localElimination(rangeChecks, MCFG, toRemoveChecks);

		    /////////////////////////////////////////////////////
		    // Global Elimination
		    /////////////////////////////////////////////////////
		    globalElimination(rangeChecks, MCFG, toRemoveChecks);


			///////////////////////////////////////
			//Handle the loops
			///////////////////////////////////////
			std::set<Instruction*> allInstrsOld;
			std::map<Value*, ComputedArrayIndex*> computedIndexes;
		    getAllRelatedInstrsOld(arrayIndexMap, *funcIter, allInstrsOld, computedIndexes);

			//Dominatee - Dominators
			std::map<MCFG_Node*, std::set<MCFG_Node*> > dominatorSet;
			getDominators(dominatorSet, MCFG);
//			printDominators(dominatorSet);

			//BackEdge From node - BackEdge To node
			std::set<std::pair<MCFG_Node*, MCFG_Node*> > backEdges;
			findBackEdges(backEdges, dominatorSet);

			//BackEdge FromTo pair - the other bb contained in the loop
			std::map<std::pair<MCFG_Node*, MCFG_Node*>, std::set<MCFG_Node*> > loops;
			findLoops(loops, backEdges, dominatorSet);

			std::map<MCFG_Node*, std::set<Instruction*> > deletedChecks;
			std::map<MCFG_Node*, std::set<Instruction*> > hoistedChecks;

			findForLoops(deletedChecks, hoistedChecks, loops, computedIndexes);

//			hoistInsideLoop(deletedChecks, hoistedChecks, MCFG, dominatorSet, loops, computedIndexes);

//			//std::map<std::pair<std::pair<MCFG_Node*, MCFG_Node*>, std::set<MCFG_Node*> >, std::vector<Instruction*> > loopInvariant;
//			std::map<MCFG_Node*, std::set<Instruction*> > loopInvariant;
//			std::map<MCFG_Node*, std::set<Instruction*> > hoistedChecks;
//			findLoopInvariant(loopInvariant, hoistedChecks, dominatorSet, loops, computedIndexes);
//
//			std::map<MCFG_Node*, std::set<Instruction*> > MonotonicalVar;
//			findMonotonicalVar(MonotonicalVar, hoistedChecks, dominatorSet, loops, computedIndexes);


//			hoistOutLoop();

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
		for(Function::iterator bbIter = F.begin(); bbIter != F.end(); ++bbIter) {
			for(BasicBlock::iterator instIter = (*bbIter).begin(); instIter != (*bbIter).end(); ++instIter) {
				if (isa<GetElementPtrInst> (*instIter)) {
					GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst> (&(*instIter));

					errs() << *GEP << "\n" << *GEP->getPointerOperandType() << "\n";
//					errs() << GEP->getPointerOperandType()->getArrayElementType()->getArrayNumElements() << "\n";

					// TODO: it didn't handle malloc now
					if (const ArrayType *ar = dyn_cast<ArrayType>(GEP->getPointerOperandType()->getArrayElementType())) {
						unsigned max_elements = ar->getNumElements();

						errs() << max_elements << "\n";
						// check for constant and non-constant indices
						// compile time warning for constant indices
						// like A[100]

						// for non-constant indices insert call to overflow checking code
						int index = GEP->getNumOperands() - 1;
						Value *v1 = GEP->getOperand(index);
						Value *v2 = ConstantInt::get(v1->getType(), max_elements);
						Value *v3 = ConstantInt::get(v1->getType(), 0);
//						errs() << *v1 << " " << *v2 << "\n";

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
	/*	ConstantInt* zero = ConstantInt::get(Type::getInt32Ty(func->getContext()), 0);

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
		CallInst::Create(exitFunc, zero, "", errorBB);*/

		// This is inserted to prevent the error: errorBB doesn't have a terminator
		//new UnreachableInst(M->getContext(), errorBB);

		return errorBB;
	}


	// Given a MCFG and the computed details for each array index, conduct local elimination
	/**
	 * Conduct the following two eliminations:
	 * 1. Identical checks
	 * 2. Subsumed checks with identical subscript expressions
	 */
	/**
	 * TODO: Conduct elimination for "Subsumed checks with identical bounds"
	 */
	void localElimination(std::map<Value*, RangeCheck*>& rangeChecks, std::vector<MCFG_Node*>& MCFG, std::set<Value*>& toRemoveChecks){
		// Iterate every basic block in MCFG
		for (unsigned i = 0; i < MCFG.size(); i++) {
			std::map<std::string, Value*> visitedLowerChecks;
			std::map<std::string, Value*> visitedUpperChecks;
			std::map<Constant*, Value*> visitedLowerBound;
			std::map<Constant*, Value*> visitedUpperBound;
			MCFG_Node* curNode = MCFG[i];
			std::set<Value*> toRemove;

			// Iterate every instruction in current MCFG node
			for (unsigned j = 0; j < curNode->instrs.size(); j++) {
				Value* curInst = curNode->instrs[j];

				// If this is an array index instruction
				std::map<Value*, RangeCheck*>::iterator foundRangeCheck =
						rangeChecks.find(curInst);
				if (foundRangeCheck != rangeChecks.end()) {
					RangeCheck* cur_check_details = foundRangeCheck->second;
					std::string check_expr = cur_check_details->index_expr;
					std::set<Instruction*> cur_defs =
							cur_check_details->def_instrs;

					if (cur_check_details->checkMax) {
						Value* cur_max = cur_check_details->check->getOperand(1);
						Constant* cur_max_c = dyn_cast<Constant>(cur_max);
						// If it is an upper check
						// Check whether the same subscript expression has been checked before
						std::map<std::string, Value*>::iterator visitedCheck =
								visitedUpperChecks.find(check_expr);
						if (visitedCheck == visitedUpperChecks.end()) {
							// Not visited before
							//////////////////////////////////////////////////////
							// Check subsumed checks with identical bounds
							//////////////////////////////////////////////////////
							// Although two subscript expressions are not identical, we can still check whether share the identical bound
							// Check subscript expressions with the same upper bound
							std::map<Constant*, Value*>::iterator visitedub =
									visitedUpperBound.find(cur_max_c);
							if (visitedub == visitedUpperBound.end()) {
								visitedUpperBound[cur_max_c] = curInst;
							} else {
								RangeCheck* visited_check_details =
										rangeChecks.find(visitedub->second)->second;
								if (compareLocalCheckExprs(visited_check_details,
										cur_check_details) == 1) {
									//if always visited > cur, remove cur
									toRemove.insert(curInst);
								}
							}

							// Add the expression to the visited set
							visitedUpperChecks[check_expr] = curInst;
						} else {
							// Visited before, do elimination (Check identical subscript expressions)
							// Check whether these two identical checks use the same definitions
							Value* visited = visitedCheck->second;
							RangeCheck* visited_check_details =
									rangeChecks.find(visited)->second;

							std::set<Instruction*> visited_defs =
									visited_check_details->def_instrs;

							if (visited_defs == cur_defs) {
								// If the two identical checks are with the same definitions, eliminate duplicated ones
								Value* visited_max =
										visited_check_details->check->getOperand(
												1);
								Constant* visited_max_c = dyn_cast<Constant>(
										visited_max);

								if ((visited_max_c->getUniqueInteger()
										- cur_max_c->getUniqueInteger()).isNonNegative()) {
									// Replace the original upper bound to the smaller one
									visited_check_details->check->setOperand(1,
											cur_max);
								}

								// Remove current max bound check
								toRemove.insert(curInst);
							} else {
								// If the two identical checks are not with the same definitions, kill the original check
								visitedUpperChecks[check_expr] = curInst;
							}
						}
					}

					if (!cur_check_details->checkMax) {
						Value* cur_min = cur_check_details->check->getOperand(1);
						Constant* cur_min_c = dyn_cast<Constant>(cur_min);
						// If it is an lower check
						// Check whether the same subscript expression has been checked before
						std::map<std::string, Value*>::iterator visitedCheck =
								visitedLowerChecks.find(check_expr);
						if (visitedCheck == visitedLowerChecks.end()) {
							// Not visited before
							//////////////////////////////////////////////////////
							// Check subsumed checks with identical bounds
							//////////////////////////////////////////////////////
							// Although two subscript expressions are not identical, we can still check whether share the identical bound
							// Check subscript expressions with the same upper bound
							std::map<Constant*, Value*>::iterator visitedlb =
									visitedLowerBound.find(cur_min_c);
							if (visitedlb == visitedLowerBound.end()) {
								visitedLowerBound[cur_min_c] = curInst;
							} else {
								RangeCheck* visited_check_details =
										rangeChecks.find(visitedlb->second)->second;
								if (compareLocalCheckExprs(visited_check_details,
										cur_check_details) == -1) {
									//if always visited <= cur, remove cur
									toRemove.insert(curInst);
								}
							}

							// Add the expression to the visited set
							visitedLowerChecks[check_expr] = curInst;
						} else {
							// Visited before, do elimination (Check identical subscript expressions)
							// Check whether these two identical checks use the same definitions
							Value* visited = visitedCheck->second;
							RangeCheck* visited_check_details =
									rangeChecks.find(visited)->second;

							std::set<Instruction*> visited_defs =
									visited_check_details->def_instrs;

							if (visited_defs == cur_defs) {
								// If the two identical checks are with the same definitions, eliminate duplicated ones
								Value* visited_min =
										visited_check_details->check->getOperand(
												1);
								Constant* visited_min_c = dyn_cast<Constant>(
										visited_min);

								if ((visited_min_c->getUniqueInteger()
										- cur_min_c->getUniqueInteger()).isNegative()) {
									// Replace the original lower bound to the bigger one
									visited_check_details->check->setOperand(1,
											cur_min);
								}

								// Remove current min bound check
								toRemove.insert(curInst);
								} else {
									// If the two identical checks are not with the same definitions, kill the original check
									visitedLowerChecks[check_expr] = curInst;
								}
							}

						}
					}
				}

			removeDuplicateChecks(toRemove, curNode, toRemoveChecks);
			}

		errs() << "\n#####################################\n";
		errs() << "##### After Local Elimination #######\n";
		errs() << "# Removed checks: \n";
		for(std::set<Value*>::iterator it = toRemoveChecks.begin(); it!= toRemoveChecks.end(); it++){
			errs() << "    " << **it << "\n";
		}
		printMCFG(MCFG);

	}

	void globalElimination(std::map<Value*, RangeCheck*>& rangeChecks, std::vector<MCFG_Node*>& MCFG, std::set<Value*>& toRemoveChecks){
		////////////////////////////////////////////////////////////
		// Step 1: compute local information for all basic blocks and initialize IN,OUT
		///////////////////////////////////////////////////////////
		std::map<MCFG_Node*, std::set<RangeCheck*> > IN;
		std::map<MCFG_Node*, std::set<RangeCheck*> > OUT;
		std::map<MCFG_Node*, std::map<Instruction*, EffectType> > EFFECT;
		for (unsigned i = 0; i < MCFG.size(); i++) {
			MCFG_Node* curNode = MCFG[i];

			std::set<RangeCheck*> IN_B;
			std::set<RangeCheck*> OUT_B;
			std::map<Instruction*, EffectType> effect_B;

			// Initialize IN and OUT for all nodes to be an empty set
			IN[curNode] = IN_B;
			OUT[curNode] = OUT_B;

			// Iterate every instruction in current MCFG node
			for (unsigned j = 0; j < curNode->instrs.size(); j++) {
				Instruction* curInst = curNode->instrs[j];

				// If it is a definition instruction, like a = a + c, compute EFFECT(B, v)
				if (curInst->getOpcode() == 28) {
					effect_B[curInst] = getEffect(curInst);
				}
			}

			EFFECT[curNode] = effect_B;
		}

		////////////////////////////////////////////////////////////
		// Step 2: Compute very busy checks
		////////////////////////////////////////////////////////////
		// A map to record check -> a set of busy checks immediately following the current check
		std::map<RangeCheck*, std::set<RangeCheck*> > busyChecks;
		computeVeryBusyChecks(MCFG, rangeChecks, IN, OUT, EFFECT, busyChecks);

		////////////////////////////////////////////////////////////
		// Step 3: Modify checks
		////////////////////////////////////////////////////////////
		modifyChecks(busyChecks);

		////////////////////////////////////////////////////////////
		// Step 4: Available checks: compute local information for all basic blocks
		////////////////////////////////////////////////////////////
		std::map<MCFG_Node*, std::set<RangeCheck*> > AIN;
		std::map<MCFG_Node*, std::set<RangeCheck*> > AOUT;
		for (unsigned i = 0; i < MCFG.size(); i++) {
			MCFG_Node* curNode = MCFG[i];

			std::set<RangeCheck*> IN_B;
			std::set<RangeCheck*> OUT_B;

			// Initialize IN and OUT for all nodes to be an empty set
			AIN[curNode] = IN_B;
			AOUT[curNode] = OUT_B;
		}

		////////////////////////////////////////////////////////////
		// Step 5: Compute available checks
		////////////////////////////////////////////////////////////
		std::map<RangeCheck*, std::set<RangeCheck*> > avaiChecks;
		std::map<RangeCheck*, MCFG_Node*> avaiChecksPosition;
		computeAvailableChecks(MCFG, rangeChecks, AIN, AOUT, EFFECT, avaiChecks, avaiChecksPosition);

		////////////////////////////////////////////////////////////
		// Step 6: Eliminate redundant checks
		////////////////////////////////////////////////////////////
		removeRedundantAvaiChecks(avaiChecks, avaiChecksPosition, MCFG, toRemoveChecks);

		errs() << "\n#####################################\n";
		errs() << "##### After Global Elimination #######\n";
		errs() << "# Removed checks: \n";
		for (std::set<Value*>::iterator it = toRemoveChecks.begin();
				it != toRemoveChecks.end(); it++) {
			errs() << "    " << **it << "\n";
		}
		printMCFG(MCFG);

	}

	// Compute very busy checks
	void computeAvailableChecks(std::vector<MCFG_Node*>& MCFG,
			std::map<Value*, RangeCheck*>& rangeChecks,
			std::map<MCFG_Node*, std::set<RangeCheck*> >& IN,
			std::map<MCFG_Node*, std::set<RangeCheck*> >& OUT,
			std::map<MCFG_Node*, std::map<Instruction*, EffectType> >& EFFECT,
			std::map<RangeCheck*, std::set<RangeCheck*> >& avaiChecks,
			std::map<RangeCheck*, MCFG_Node*>& avaiChecksPosition) {
		bool changed = true;

		while (changed) {
			changed = false;

			MCFG_Node* entry = *MCFG.begin();
			std::queue<MCFG_Node*> worklist;
			std::set<MCFG_Node*> visited;
			worklist.push(entry);

			while (!worklist.empty()) {
				MCFG_Node* curNode = worklist.front();
				worklist.pop();
				visited.insert(curNode);

				// Compute IN set
				std::set<RangeCheck*> OLD_IN_B = IN[curNode];
				if (!curNode->preds.empty()) {
					// IN = INTERSECT(OUT(p))
					if (curNode->preds.size() < 2) {
						IN[curNode] = OUT[*curNode->preds.begin()];
					} else {
						std::set<RangeCheck*> set1 = OUT[*curNode->preds.begin()];
						IN[curNode] = set1;
						for(std::set<MCFG_Node*>::iterator it = curNode->preds.begin(); it != curNode->preds.end(); it++){
							if(it == curNode->preds.begin()) continue;
							std::set<RangeCheck*> set2 = OUT[*it];
							IN[curNode] = intersectChecks(IN[curNode], set2);
						}
					}
				}

				std::set<RangeCheck*> IN_B = IN[curNode];
				if (OLD_IN_B != IN_B) {
					changed = true;
				}

				// Compute OUT set
				// Do not use GEN set, instead, compute OUT set instruction by instruction in forward order
				std::set<RangeCheck*> OUT_B = IN_B;
				std::set<RangeCheck*> OLD_OUT_B = OUT[curNode];
				std::map<Instruction*, EffectType> effect_B = EFFECT[curNode];
				for (std::vector<Instruction*>::iterator instIt = curNode->instrs.begin(); instIt != curNode->instrs.end(); instIt++) {
					Instruction* curInst = *instIt;
					if (curInst->getOpcode() == 28) {
						// If it is a definition ('store') instruction, change the OUT set, as some checks may be killed by the redefinition
						OUT_B = forward(OUT_B, curInst, effect_B);
					}

					// If this is a check, add to OUT set
					std::map<Value*, RangeCheck*>::iterator foundRangeCheck =
							rangeChecks.find(curInst);
					if (foundRangeCheck != rangeChecks.end()) {
						RangeCheck* curCheck = foundRangeCheck->second;
						// Record the set of available checks at the point before current check
						avaiChecks[curCheck] = OUT_B;
						avaiChecksPosition[curCheck] = curNode;
						unionChecks(OUT_B, curCheck);
					}
				}

				if (OLD_OUT_B != OUT_B) {
					changed = true;
				}

				OUT[curNode] = OUT_B;

				// Add unvisited predecessors to the worklist
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

//				errs() << "############### IN ############## \n";
//				for(std::map<MCFG_Node*, std::set<RangeCheck*> >::iterator it = IN.begin(); it != IN.end(); it++){
//					errs() << "    # Node [" << it->first->label << "]\n";
//					std::set<RangeCheck*> checks = it->second;
//					for(std::set<RangeCheck*>::iterator it2 = checks.begin(); it2 != checks.end(); it2++){
//						errs() << "    - " << *(*it2)->check << "\n";
//					}
//				}
//
//				errs() << "############### OUT ############## \n";
//				for (std::map<MCFG_Node*, std::set<RangeCheck*> >::iterator it =
//						OUT.begin(); it != OUT.end(); it++) {
//					errs() << "    # Node [" << it->first->label << "]\n";
//					std::set<RangeCheck*> checks = it->second;
//					for (std::set<RangeCheck*>::iterator it2 = checks.begin();
//							it2 != checks.end(); it2++) {
//						errs() << "    - " << *(*it2)->check << "\n";
//					}
//				}

	}

	// Remove redundant available checks
	void removeRedundantAvaiChecks(
			std::map<RangeCheck*, std::set<RangeCheck*> >& avaiChecks,
			std::map<RangeCheck*, MCFG_Node*>& avaiChecksPosition,
			std::vector<MCFG_Node*>& MCFG, std::set<Value*>& toRemoveChecks) {
		for (std::map<RangeCheck*, std::set<RangeCheck*> >::iterator it1 =
				avaiChecks.begin(); it1 != avaiChecks.end(); it1++) {
			RangeCheck* curCheck = it1->first;
			std::set<RangeCheck*> avaiSet = it1->second;
			for (std::set<RangeCheck*>::iterator it2 = avaiSet.begin();
					it2 != avaiSet.end(); it2++) {
				RangeCheck* avaiCheck = *it2;

				if (subsume(avaiCheck, curCheck)) {
					// Remove current check
					MCFG_Node* node = avaiChecksPosition.find(curCheck)->second;
					std::vector<Instruction*>::iterator foundIt = std::find(node->instrs.begin(), node->instrs.end(), curCheck->check);
				    node->instrs.erase(foundIt);
				    toRemoveChecks.insert(curCheck->check);
					break;
				}
			}
		}
	}

	// Modify checks according to the very busy checks
	void modifyChecks(std::map<RangeCheck*, std::set<RangeCheck*> >& busyChecks){
		for(std::map<RangeCheck*, std::set<RangeCheck*> >::iterator it1 = busyChecks.begin(); it1 != busyChecks.end(); it1++){
			RangeCheck* curCheck = it1->first;
			std::set<RangeCheck*> busySet = it1->second;
			for(std::set<RangeCheck*>::iterator it2 = busySet.begin(); it2 != busySet.end(); it2++){
				RangeCheck* busyCheck = *it2;

				if(subsume(busyCheck, curCheck)){
					if(busyCheck->index_expr.compare(curCheck->index_expr) == 0){
						// Only modify for the identical expression now,
						// TODO: How to modify for subsumed subscript expressions with same bound,as the position of the definition is not determined
						curCheck->check->setOperand(1, busyCheck->check->getOperand(1));
					}
					break;
				}
			}
		}
	}

	// Compute very busy checks
	void computeVeryBusyChecks(std::vector<MCFG_Node*>& MCFG, std::map<Value*, RangeCheck*>& rangeChecks
			                  , std::map<MCFG_Node*, std::set<RangeCheck*> >& IN, std::map<MCFG_Node*, std::set<RangeCheck*> >& OUT
			                  , std::map<MCFG_Node*, std::map<Instruction*, EffectType> >& EFFECT
			                  , std::map<RangeCheck*, std::set<RangeCheck*> >& busyChecks){
		bool changed = true;

		std::vector<MCFG_Node*> exits;
		for(unsigned i = 0; i<MCFG.size(); i++){
			if(MCFG[i]->succs.empty()){
				exits.push_back(MCFG[i]);
			}
		}

		while(changed){
			changed = false;

			std::queue<MCFG_Node*> worklist;
			std::set<MCFG_Node*> visited;

			for(unsigned i = 0; i<exits.size(); i++){
				worklist.push(exits[i]);
			}

			while (!worklist.empty()) {
				MCFG_Node* curNode = worklist.front();
				worklist.pop();
				visited.insert(curNode);

				// Compute OUT set
				std::set<RangeCheck*> OLD_OUT_B = OUT[curNode];
				if(!curNode->succs.empty()){
					// OUT = INTERSECT(IN(s))
					// Assume at most two successors
					if(curNode->succs.size() < 2){
						OUT[curNode] = IN[*curNode->succs.begin()];
					}else{
						std::set<RangeCheck*> set1 = IN[*curNode->succs.begin()];
						std::set<RangeCheck*> set2 = IN[*curNode->succs.rbegin()];
						OUT[curNode] = intersectChecks(set1, set2);
					}
				}

				std::set<RangeCheck*> OUT_B = OUT[curNode];
				if(OLD_OUT_B != OUT_B){
					changed = true;
				}

				// Compute IN set
				// Do not use GEN set, instead, compute IN set instruction by instruction in backward order
				std::set<RangeCheck*> IN_B = OUT_B;
				std::set<RangeCheck*> OLD_IN_B = IN[curNode];
				std::map<Instruction*, EffectType> effect_B = EFFECT[curNode];
				for(std::vector<Instruction*>::reverse_iterator instIt = curNode->instrs.rbegin(); instIt != curNode->instrs.rend(); instIt++){
				    Instruction* curInst = *instIt;

					if(curInst->getOpcode() == 28){
						// If it is a definition ('store') instruction, change the IN set, as some checks may be killed by the redefinition
						IN_B = backward(IN_B, curInst, effect_B);
					}

					// If this is a check, add to IN set
					std::map<Value*, RangeCheck*>::iterator foundRangeCheck = rangeChecks.find(curInst);
					if (foundRangeCheck != rangeChecks.end()) {
						RangeCheck* curCheck = foundRangeCheck->second;
						// Record the set of busy checks at the point after current check
						busyChecks[curCheck] = IN_B;
						unionChecks(IN_B, curCheck);
					}
				}

				if(OLD_IN_B != IN_B){
					changed = true;
				}

				IN[curNode] = IN_B;

				// Add unvisited predecessors to the worklist
				for (std::set<MCFG_Node*>::iterator it2 = curNode->preds.begin(); it2 != curNode->preds.end(); ++it2) {
					MCFG_Node* nextNode = *it2;
					if (visited.find(nextNode) == visited.end()) {
						worklist.push(nextNode);
					}
				}
			}
		}

//		errs() << "############### IN ############## \n";
//		for(std::map<MCFG_Node*, std::set<RangeCheck*> >::iterator it = IN.begin(); it != IN.end(); it++){
//			errs() << "    # Node [" << it->first->label << "]\n";
//			std::set<RangeCheck*> checks = it->second;
//			for(std::set<RangeCheck*>::iterator it2 = checks.begin(); it2 != checks.end(); it2++){
//				errs() << "    - " << *(*it2)->check << "\n";
//			}
//		}
//
//		errs() << "############### OUT ############## \n";
//		for (std::map<MCFG_Node*, std::set<RangeCheck*> >::iterator it =
//				OUT.begin(); it != OUT.end(); it++) {
//			errs() << "    # Node [" << it->first->label << "]\n";
//			std::set<RangeCheck*> checks = it->second;
//			for (std::set<RangeCheck*>::iterator it2 = checks.begin();
//					it2 != checks.end(); it2++) {
//				errs() << "    - " << *(*it2)->check << "\n";
//			}
//		}


	}

	// Check whether check1 subsumes check2
	bool subsume(RangeCheck* check1, RangeCheck* check2){
		if(check1->checkMax != check2->checkMax) return false;

		Value* bound1 = check1->check->getOperand(1);
		Constant* bound_value1 = dyn_cast<Constant>(bound1);
		int value1 = bound_value1->getUniqueInteger().getSExtValue();

		Value* bound2 = check2->check->getOperand(1);
		Constant* bound_value2 = dyn_cast<Constant>(bound2);
		int value2 = bound_value2->getUniqueInteger().getSExtValue();

		if(check1->index_expr.compare(check2->index_expr) != 0){
			// identical check bound, but subsume check expression
			if(!bound_value1->getUniqueInteger().eq(bound_value2->getUniqueInteger())){
				return false;
			}

			// two checks uses the same variable
			// Return -1: always boundCheck1 <= boundCheck2
				// Return 1: always boundCheck1 > boundCheck2
				// Return 0: Can't determine the relationship between boundCheck1 and boundCheck2 at compile time
			int ret = compareGlobalCheckExprs(check1, check2);
			if(check1->checkMax && ret == 1){
				return true;
			}

			if(!check1->checkMax && ret == -1){
				return true;
			}
		}else{
			// Identical check expression, but different check bound
			if(check1->checkMax && check2->checkMax){
				return value2 >= value1;
			}else if(!check1->checkMax && !check2->checkMax){
				return value1 >= value2;
			}else{
				return false;
			}
		}

		return false;
	}

	bool equalCheck(RangeCheck* check1, RangeCheck* check2){
		if (check1->index_expr.compare(check2->index_expr) != 0) {
			return false;
		}

		if(check1->checkMax != check1->checkMax) return false;

		Value* bound1 = check1->check->getOperand(1);
		Constant* bound_value1 = dyn_cast<Constant>(bound1);

		Value* bound2 = check2->check->getOperand(1);
		Constant* bound_value2 = dyn_cast<Constant>(bound2);

		return bound_value1->getUniqueInteger().eq(bound_value2->getUniqueInteger());
	}

	// Add a new found check to the existing busy check set
	void unionChecks(std::set<RangeCheck*>& checkSet, RangeCheck* newCheck){
//		errs() << "&&&&& new: " << *newCheck->check << "\n";
//		for(std::set<RangeCheck*>::iterator it1 = checkSet.begin(); it1 != checkSet.end(); it1++){
//			errs() << "&&&&& old: " << *(*it1)->check << "\n";
//		}

		std::set<RangeCheck*> toRemove;
		bool toAdd = true;
		for(std::set<RangeCheck*>::iterator it1 = checkSet.begin(); it1 != checkSet.end(); it1++){
			RangeCheck* oldCheck = *it1;
			if(subsume(oldCheck, newCheck)){
				toAdd = false;
				break;
			}
		}

		if(toAdd){
			// Check whether the newCheck subsumes any oldCheck, if so, remove oldCheck
			for (std::set<RangeCheck*>::iterator it1 = checkSet.begin(); it1 != checkSet.end(); it1++) {
				RangeCheck* oldCheck = *it1;
				if (subsume(newCheck, oldCheck)) {
					toRemove.insert(oldCheck);
				}
			}

			// Remove old check
			for (std::set<RangeCheck*>::iterator it1 = toRemove.begin();
					it1 != toRemove.end(); it1++) {
				checkSet.erase(*it1);
			}

			// Add new check
			checkSet.insert(newCheck);
		}
	}

	// Intersect all the checks in the two sets
	std::set<RangeCheck*> intersectChecks(std::set<RangeCheck*>& checkSet1, std::set<RangeCheck*>& checkSet2){
		std::set<RangeCheck*> result;

		if(checkSet1.empty() || checkSet2.empty()){
			return result;
		}

		// Check all checks in set1
		for(std::set<RangeCheck*>::iterator it1 = checkSet1.begin(); it1 != checkSet1.end(); it1++){
			RangeCheck* check1 = *it1;

			// Check whether set2 also contains this check or subsumes this check
			for(std::set<RangeCheck*>::iterator it2 = checkSet2.begin(); it2 != checkSet2.end(); it2++){
				RangeCheck* check2 = *it2;

				if(equalCheck(check2, check1) || subsume(check2, check1)){
					result.insert(check1);
					break;
				}
			}
		}

		// Check all checks in set2
		for (std::set<RangeCheck*>::iterator it2 = checkSet2.begin();
				it2 != checkSet2.end(); it2++) {
			RangeCheck* check2 = *it2;

			// Check whether set2 also contains this check or subsumes this check
			for (std::set<RangeCheck*>::iterator it1 = checkSet1.begin();
					it1 != checkSet1.end(); it1++) {
				RangeCheck* check1 = *it1;

				if (equalCheck(check1, check2) || subsume(check1, check2)) {
					result.insert(check2);
					break;
				}
			}
		}

		return result;
	}

	// Backward compute IN according to OUT for busy checks
	std::set<RangeCheck*> backward(std::set<RangeCheck*>& OUT, Instruction* curDefInst, std::map<Instruction*, EffectType> effect){
		std::set<RangeCheck*> IN ;
		for (std::set<RangeCheck*>::iterator outIt = OUT.begin(); outIt != OUT.end(); outIt++) {
			RangeCheck* check = *outIt;
			std::string check_expr = check->index_expr;
			std::vector<std::string> exprs_vector = split(check_expr, '.', 0);

			// We only support subscript expression like x + c or x - c
			if (exprs_vector[exprs_vector.size() - 1].compare(
					curDefInst->getOperand(1)->getName()) != 0) {
				// Current check doesn't use the variable here
				IN.insert(check);
			} else {
				// Determine whether to add the current check according to the effect of the cur definition
				std::map<Instruction*, EffectType>::iterator foundDef =
						effect.find(curDefInst);
				EffectType effectType = foundDef->second;
				if (check->checkExprType == singleVar) {
					if (check->checkMax) {
						// Check upper bound
						switch (effectType) {
						case unchanged:
							IN.insert(check);
							break;
						case increment:
							IN.insert(check);
							break;
						case decrement:
							break;
						case multiply:
							IN.insert(check);
							break;
						case divgt1:
							break;
						case divlt1:
							IN.insert(check);
							break;
						case changed:
							break;
						}

					} else {
						// Check lower bound
						switch (effectType) {
						case unchanged:
							IN.insert(check);
							break;
						case increment:
							break;
						case decrement:
							IN.insert(check);
							break;
						case multiply:
							break;
						case divgt1:
							IN.insert(check);
							break;
						case divlt1:
							break;
						case changed:
							break;

						}

					}

				} else {
					if (check->checkMax) {
						// Check upper bound
						switch (effectType) {
						case unchanged:
							IN.insert(check);
							break;
						case increment:
						case multiply:
						case divlt1:
							if (check->checkExprType == fv_vInc_fInc) {
								IN.insert(check);
							}
							break;
						case decrement:
						case divgt1:
							if (check->checkExprType == fv_vDec_fInc) {
								IN.insert(check);
							}
							break;
						case changed:
							break;
						}

					} else {
						// Check lower bound
						switch (effectType) {
						case unchanged:
							IN.insert(check);
							break;
						case increment:
						case multiply:
						case divlt1:
							if (check->checkExprType == fv_vInc_fDec) {
								IN.insert(check);
							}
							break;
						case decrement:
						case divgt1:
							if (check->checkExprType == fv_vDec_fDec) {
								IN.insert(check);
							}
							break;
						case changed:
							break;
						}
					}

				}
			}
		}

//		errs() << ">>>> Instruction: [" << curDefInst << "]\n";
//		for(std::set<RangeCheck*>::iterator it = IN.begin(); it != IN.end(); it++){
//			errs() << ">>>> " << (*it)->check << "\n";
//		}
		return IN;
	}

	// Forward compute OUT according to IN for available checks
	std::set<RangeCheck*> forward(std::set<RangeCheck*>& IN,
			Instruction* curDefInst,
			std::map<Instruction*, EffectType> effect) {
		std::set<RangeCheck*> OUT;
		for (std::set<RangeCheck*>::iterator inIt = IN.begin();
				inIt != IN.end(); inIt++) {
			RangeCheck* check = *inIt;
			std::string check_expr = check->index_expr;
			std::vector<std::string> exprs_vector = split(check_expr, '.', 0);

			// We only support subscript expression like x + c or x - c
			if (exprs_vector[exprs_vector.size() - 1].compare(curDefInst->getOperand(1)->getName()) != 0) {
				// Current check doesn't use the variable here
				OUT.insert(check);
			} else {
				// Determine whether to add the current check according to the effect of the cur definition
				std::map<Instruction*, EffectType>::iterator foundDef =
						effect.find(curDefInst);
				EffectType effectType = foundDef->second;
				if (check->checkExprType == singleVar) {
					if (check->checkMax) {
						// Check upper bound
						switch (effectType) {
						case unchanged:
							OUT.insert(check);
							break;
						case increment:
							break;
						case decrement:
							OUT.insert(check);
							break;
						case multiply:
							break;
						case divgt1:
							OUT.insert(check);
							break;
						case divlt1:
							break;
						case changed:
							break;
						}

					} else {
						// Check lower bound
						switch (effectType) {
						case unchanged:
							OUT.insert(check);
							break;
						case increment:
							OUT.insert(check);
							break;
						case decrement:
							break;
						case multiply:
							OUT.insert(check);
							break;
						case divgt1:
							break;
						case divlt1:
							OUT.insert(check);
							break;
						case changed:
							break;

						}

					}

				} else {
					if (check->checkMax) {
						// Check upper bound
						switch (effectType) {
						case unchanged:
							OUT.insert(check);
							break;
						case increment:
						case multiply:
						case divlt1:
							if (check->checkExprType == fv_vInc_fDec) {
								OUT.insert(check);
							}
							break;
						case decrement:
						case divgt1:
							if (check->checkExprType == fv_vDec_fDec) {
								OUT.insert(check);
							}
							break;
						case changed:
							break;
						}

					} else {
						// Check lower bound
						switch (effectType) {
						case unchanged:
							OUT.insert(check);
							break;
						case increment:
						case multiply:
						case divlt1:
							if (check->checkExprType == fv_vInc_fInc) {
								OUT.insert(check);
							}
							break;
						case decrement:
						case divgt1:
							if (check->checkExprType == fv_vDec_fInc) {
								OUT.insert(check);
							}
							break;
						case changed:
							break;
						}
					}

				}
			}
		}

		return OUT;
	}

	// Compute the effect of a basic block on a definition instruction
	EffectType getEffect(Instruction* inst){
		Instruction* def_var = dyn_cast<Instruction>(inst->getOperand(1));
		Value* value = inst->getOperand(0);

		if(isa<Constant>(value)){
			return changed;
		}

		Instruction* op = dyn_cast<Instruction>(value);

		// If the definition is a = a + c
		// %3 = load i32* %a, align 4
		// %inc = add nsw i32 %3, 1
		// store i32 %inc, i32* %a, align 4
		if(op->getNumOperands() < 2) return changed;

		const char* opName = op->getOpcodeName();
		Value* value1 = op->getOperand(0);
		Value* value2 = op->getOperand(1);

		Instruction* operand1;
		Instruction* operand2;

		Constant* finalC;

		if(isa<Constant>(value1) && isa<Constant>(value2)){
			// z = 1 + 1
			return changed;
		}
		else if(isa<Constant>(value1) && !isa<Constant>(value2)){
			// z = 1 + z
			operand2 = dyn_cast<Instruction>(value2);
			if(operand2->getOpcode() != 27 || operand2->getOperand(0) != def_var){
				return changed;
			}
			finalC = dyn_cast<Constant>(value1);
		}else if(!isa<Constant>(value1) && isa<Constant>(value2)){
			operand1 = dyn_cast<Instruction>(value1);
			if(operand1->getOpcode() != 27 || operand1->getOperand(0) != def_var){
				return changed;
			}
			finalC =dyn_cast<Constant>(value2);
		}else if(!isa<Constant>(value1) && !isa<Constant>(value2)){
			// z = x + y
			return changed;
		}


		APInt result = finalC->getUniqueInteger();
		if(strcmp(opName, "add") == 0){
			if(result.sgt(0)) return increment;
		}else if(strcmp(opName, "sub") == 0){
			if(result.sgt(0)) return decrement;
		}else if(strcmp(opName, "mul") == 0){
			if(result.sgt(1)) return multiply;
		}else if(strcmp(opName, "sdiv") == 0){
			if(result.sgt(1)) return divgt1;
			if(result.sgt(0) && result.slt(1)) return divlt1;
		}else{
			return changed;
		}


		return changed;

	}
	// Check the relationship between two bound check expressions in local elimination
	// Return -1: always boundCheck1 <= boundCheck2
	// Return 1: always boundCheck1 > boundCheck2
	// Return 0: Can't determine the relationship between boundCheck1 and boundCheck2 at compile time
	int compareLocalCheckExprs(RangeCheck* boundCheck1, RangeCheck* boundCheck2){
		std::set<Instruction*> defs1 = boundCheck1->def_instrs;
		std::set<Instruction*> defs2 = boundCheck2->def_instrs;

		if(defs1 == defs2){
			// If the two subscript expressions use the same variable, check whether they are subsumed checks
			// We only support subsumed expression check in format of a+c (add.c.load.a)
			std::vector<std::string> expr_v1 = split(boundCheck1->index_expr, '.', 0);
			std::vector<std::string> expr_v2 = split(boundCheck2->index_expr, '.', 0);

			if(expr_v1.size() == 4 && expr_v2.size() == 2){
				// v1 = a + c, v2 = a
				std::string op = expr_v1[0];
				int operand = atoi(expr_v1[1].c_str());
				if(op.compare("add") == 0 && operand > 0) return 1;
				if(op.compare("add") == 0 && operand < 0) return -1;
				if(op.compare("sub") == 0 && operand > 0) return -1;
				if(op.compare("sub") == 0 && operand < 0) return 1;
			}else if(expr_v1.size() == 4 && expr_v2.size() == 4){
				// v1 = a + c, v2 = a + c
				std::string op1 = expr_v1[0];
				std::string op2 = expr_v2[0];
				int operand1 = atoi(expr_v1[1].c_str());
				int operand2 = atoi(expr_v2[1].c_str());

				if (op1 == "add" && op2 == "add") {
					return operand1 - operand2 > 0 ? 1 : -1;
				} else if (op1 == "add" && op2 == "sub") {
					return 1;
				} else if (op1 == "sub" && op2 == "add") {
					return -1;
				} else if (op1 == "sub" && op2 == "sub") {
					return operand1 - operand2 > 0 ? -1 : 1;
				}
			}else if(expr_v1.size() == 2 && expr_v2.size() == 4){
				// v1 = a, v2 = a + c
				std::string op = expr_v2[0];
				int operand = atoi(expr_v2[1].c_str());
				if (op.compare("add") == 0 && operand > 0)
					return -1;
				if (op.compare("add") == 0 && operand < 0)
					return 1;
				if (op.compare("sub") == 0 && operand > 0)
					return 1;
				if (op.compare("sub") == 0 && operand < 0)
					return -1;
			}else if(expr_v1.size() == 2 && expr_v2.size() == 2){
				// v1 = a, v2 = a
				return -1;
			}
		}

		return 0;
	}

	// Check the relationship between two bound check expressions in global elimination.
	// Return -1: always boundCheck1 <= boundCheck2
	// Return 1: always boundCheck1 > boundCheck2
	// Return 0: Can't determine the relationship between boundCheck1 and boundCheck2 at compile time
	int compareGlobalCheckExprs(RangeCheck* boundCheck1, RangeCheck* boundCheck2) {
		std::set<Instruction*> defs1 = boundCheck1->def_instrs;
		std::set<Instruction*> defs2 = boundCheck2->def_instrs;

		// If the two subscript expressions use the same variable, check whether they are subsumed checks
		// We only support subsumed expression check in format of a+c (add.c.load.a)
		std::vector<std::string> expr_v1 = split(boundCheck1->index_expr, '.',
				0);
		std::vector<std::string> expr_v2 = split(boundCheck2->index_expr, '.',
				0);

		if(expr_v1[expr_v1.size() - 1].compare(expr_v2[expr_v2.size() -1]) == 0){
			// The check expressions use the same variable
			if (expr_v1.size() == 4 && expr_v2.size() == 2) {
				// v1 = a + c, v2 = a
				std::string op = expr_v1[0];
				int operand = atoi(expr_v1[1].c_str());
				if (op.compare("add") == 0 && operand > 0)
					return 1;
				if (op.compare("add") == 0 && operand < 0)
					return -1;
				if (op.compare("sub") == 0 && operand > 0)
					return -1;
				if (op.compare("sub") == 0 && operand < 0)
					return 1;
			} else if (expr_v1.size() == 4 && expr_v2.size() == 4) {
				// v1 = a + c, v2 = a + c
				std::string op1 = expr_v1[0];
				std::string op2 = expr_v2[0];
				int operand1 = atoi(expr_v1[1].c_str());
				int operand2 = atoi(expr_v2[1].c_str());

				if (op1 == "add" && op2 == "add") {
					return operand1 - operand2 > 0 ? 1 : -1;
				} else if (op1 == "add" && op2 == "sub") {
					return 1;
				} else if (op1 == "sub" && op2 == "add") {
					return -1;
				} else if (op1 == "sub" && op2 == "sub") {
					return operand1 - operand2 > 0 ? -1 : 1;
				}
			} else if (expr_v1.size() == 2 && expr_v2.size() == 4) {
				// v1 = a, v2 = a + c
				std::string op = expr_v2[0];
				int operand = atoi(expr_v2[1].c_str());
				if (op.compare("add") == 0 && operand > 0)
					return -1;
				if (op.compare("add") == 0 && operand < 0)
					return 1;
				if (op.compare("sub") == 0 && operand > 0)
					return 1;
				if (op.compare("sub") == 0 && operand < 0)
					return -1;
			} else if (expr_v1.size() == 2 && expr_v2.size() == 2) {
				// v1 = a, v2 = a
				return -1;
			}

		}

		return 0;
	}


	// Remove a duplicate index check. Remove from MCFG first, then add to a list to be removed from CFG later
	void removeDuplicateChecks(std::set<Value*> checks, MCFG_Node* curNode, std::set<Value*>& toRemoveChecks){
		for(std::set<Value*>::iterator it = checks.begin(); it!= checks.end(); it++){
			Value* check = *it;
			std::vector<Instruction*>::iterator foundIt = std::find(curNode->instrs.begin(), curNode->instrs.end(), check);
		    curNode->instrs.erase(foundIt);
		    toRemoveChecks.insert(check);
		}

	}


	// Entry function to create a MCFG for given function
	void constructMCFG(Function& func, std::set<Instruction*>& allInstrs, std::vector<MCFG_Node*>& MCFG){
		// Step 2.0: Initialize MCFG (copy CFG)
		initializeMCFG(func, MCFG);
		// Step 2.1: Only leave array subscript expression and definitions related
		optimizeMCFG1(allInstrs, MCFG);
		// Step 2.2: Remove empty nodes and duplicate edges (T1, T2, T3, figure 3, def-use optimization in the paper).
		// Refer to comments above function declaration for more details of optimizations conducted
		optimizeMCFG2(MCFG);
		// Step 2.3: Merge check nodes (T4, T5, T6)
		optimizeMCFG3(MCFG);

		// Print constructed MCFG
		printMCFG(MCFG);
	}

	// Step 1 optimization of initialized MCFG: Only leave array subscript expressions and definitions related
	void optimizeMCFG1(std::set<Instruction*>& allInstrs, std::vector<MCFG_Node*>& MCFG) {
			// Step 1: Remove all inrelevant instructions. Only leave array subscript expression and definitions related.
			for(std::vector<MCFG_Node*>::iterator it = MCFG.begin(); it != MCFG.end(); it++){
				MCFG_Node* curNode = *it;
				std::vector<Instruction*> remained;



				for(std::vector<Instruction*>::iterator it2 = curNode->instrs.begin(); it2 != curNode->instrs.end(); ++it2){
					Instruction* curInstr = *it2;
					if(allInstrs.find(curInstr) != allInstrs.end()
							|| (curNode->label.find(".cond") != std::string::npos && strcmp(curInstr->getOpcodeName(), "icmp") == 0) ){
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
					if(predes.size() == 1 && succs.size() == 1){
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
		std::vector<MCFG_Node*> toRemove;

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

				// Remove current node
				toRemove.push_back(curNode);

			}
		}

		for(unsigned i=0; i<toRemove.size(); i++){
			MCFG_Node* curNode = toRemove[i];
		    std::vector<MCFG_Node*>::iterator it = std::find(MCFG.begin(),MCFG.end(), curNode);
			MCFG.erase(it);
		}
	}

	void initializeMCFG(Function& F, std::vector<MCFG_Node*>& MCFG) {
			// Basic block <--> MCFG node
			std::map<BasicBlock*, MCFG_Node*> visited;
			std::vector<BasicBlock*> worklist;
			for (Function::iterator bbIt = F.begin(); bbIt != F.end(); ++bbIt) {
				BasicBlock* bb = bbIt;
				MCFG_Node* node = new MCFG_Node() ;
				node->bb = bb;

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

	/*
	 * Parameter 1 (allInstrs): A set of all instructions related to array index (including definition and alloca declaration)
	 * Parameter 2 (computedIndexes): A map computed to include index details for each array index
	 */
	void getAllRelatedInstrsOld(std::map<GetElementPtrInst*, ArrayIndex*>& arrayIndexMap, Function& F,
			std::set<Instruction*>& allInstrs, std::map<Value*, ComputedArrayIndex*>& computedIndexes){
		for(std::map<GetElementPtrInst*, ArrayIndex*>::iterator it = arrayIndexMap.begin(); it != arrayIndexMap.end(); it++){
			ArrayIndex* curIndex = (*it).second;
			Instruction* maxCmp = curIndex->maxCmp;
			Instruction* minCmp = curIndex->minCmp;
			Instruction* varInstr = dyn_cast<Instruction>(curIndex->index);

			// Compute a set to include all the related instructions to the current check (including check and definition)
			// It is used to remove all irrelevant instructions to build MCFG
			allInstrs.insert(maxCmp);
			allInstrs.insert(minCmp);
			allInstrs.insert(varInstr);

			// Compute a new array index object to include all the details of current check
			// It is used to help further elimination
			ComputedArrayIndex* newIndex = new ComputedArrayIndex();
			computedIndexes[curIndex->index] = newIndex;
			newIndex->index = curIndex->index;
			newIndex->maxCmp = curIndex->maxCmp;
			newIndex->minCmp = curIndex->minCmp;

			std::stack<llvm::Use*> worklist;
			for(Instruction::op_iterator opI = varInstr->op_begin(); opI != varInstr->op_end(); ++opI){
				worklist.push(&*opI);
			}

			while (!worklist.empty()) {
				llvm::Use* var = worklist.top();
				worklist.pop();

				Instruction* inst = dyn_cast<Instruction>((*var));
				allInstrs.insert(inst);

				// Add opcode (operator) to the expression
				newIndex->index_expr.append(inst->getOpcodeName());
				newIndex->index_expr.append(".");

				// Add all the operands to the list
				for (Instruction::op_iterator opI = (*inst).op_begin();
						opI != (*inst).op_end(); ++opI) {
					Constant *op = dyn_cast<Constant>(*opI);

					if (!op) {
						// If not a constant
						Instruction* opInst = dyn_cast<Instruction>((*opI));

						if (opInst->getOpcode() == 26) {
							// If it is a variable declaration, do not need to propagate
							newIndex->index_expr.append(opInst->getName());
							newIndex->index_expr.append(".");

							allInstrs.insert(opInst);
						} else {
							worklist.push(&*opI);
						}
					} else {
						// If a constant, do not add to worklist
						newIndex->index_expr.append(
								op->getUniqueInteger().toString(10, true));
						newIndex->index_expr.append(".");
					}
				}

				// If it is a 'load' instruction, need to find the closest 'store' instruction
				if (inst->getOpcode() == 27) {
					std::set<Instruction*> visited;
					std::set<Instruction*> result;
					findDefinitions(inst, inst, visited, result);
					for (std::set<Instruction*>::iterator defI = result.begin();
							defI != result.end(); defI++) {
						allInstrs.insert(*defI);
						newIndex->def_instrs.insert(*defI);
					}
				}
			}
		}
	}

	/*
	 * Parameter 1 (allInstrs): A set of all instructions related to array index (including definition and alloca declaration)
	 * Parameter 2 (computedIndexes): A map computed to include index details for each array index
	 */
	void getAllRelatedInstrs(std::map<GetElementPtrInst*, ArrayIndex*>& arrayIndexMap, Function& F,
			std::set<Instruction*>& allInstrs, std::map<Value*, RangeCheck*>& computedIndexes){
		for(std::map<GetElementPtrInst*, ArrayIndex*>::iterator it = arrayIndexMap.begin(); it != arrayIndexMap.end(); it++){
			ArrayIndex* curIndex = (*it).second;
			Instruction* maxCmp = curIndex->maxCmp;
			Instruction* minCmp = curIndex->minCmp;
			Instruction* varInstr = dyn_cast<Instruction>(curIndex->index);

			// Compute a set to include all the related instructions to the current check (including check and definition)
			// It is used to remove all irrelevant instructions to build MCFG
			allInstrs.insert(maxCmp);
			allInstrs.insert(minCmp);
			allInstrs.insert(varInstr);

			// Compute a new array index object to include all the details of current check
			// It is used to help further elimination
			RangeCheck* maxCheck = new RangeCheck();
			RangeCheck* minCheck = new RangeCheck();
			computedIndexes[curIndex->maxCmp] = maxCheck;
			computedIndexes[curIndex->minCmp] = minCheck;

			maxCheck->check = curIndex->maxCmp;
			maxCheck->checkMax = true;

			minCheck->check = curIndex->minCmp;
			minCheck->checkMax = false;

			std::string index_expr;
			std::set<Instruction*> def_instrs;
			std::stack<llvm::Use*> worklist;
			for(Instruction::op_iterator opI = varInstr->op_begin(); opI != varInstr->op_end(); ++opI){
				worklist.push(&*opI);
			}

			while (!worklist.empty()) {
				llvm::Use* var = worklist.top();
				worklist.pop();

				Instruction* inst = dyn_cast<Instruction>((*var));
				allInstrs.insert(inst);

				// Add opcode (operator) to the expression
				index_expr.append(inst->getOpcodeName());
				index_expr.append(".");

				// Add all the operands to the list
				for (Instruction::op_iterator opI = (*inst).op_begin();
						opI != (*inst).op_end(); ++opI) {
					Constant *op = dyn_cast<Constant>(*opI);

					if (!op) {
						// If not a constant
						Instruction* opInst = dyn_cast<Instruction>((*opI));

						if (opInst->getOpcode() == 26) {
							// If it is a variable declaration, do not need to propagate
							index_expr.append(opInst->getName());
							index_expr.append(".");

							allInstrs.insert(opInst);
						} else {
							worklist.push(&*opI);
						}
					} else {
						// If a constant, do not add to worklist
						index_expr.append(
								op->getUniqueInteger().toString(10, true));
						index_expr.append(".");
					}
				}

				// If it is a 'load' instruction, need to find the closest 'store' instruction
				if (inst->getOpcode() == 27) {
					std::set<Instruction*> visited;
					std::set<Instruction*> result;
					findDefinitions(inst, inst, visited, result);
					for (std::set<Instruction*>::iterator defI = result.begin();
							defI != result.end(); defI++) {
						allInstrs.insert(*defI);
						def_instrs.insert(*defI);
					}
				}
			}

			maxCheck->def_instrs = def_instrs;
			maxCheck->index_expr = index_expr;
			minCheck->def_instrs = def_instrs;
			minCheck->index_expr = index_expr;

			// We assume only support subscript expression like x + b or x - b and b is a positive integer, to check the relationship f(x) with x easily
			std::vector<std::string> exprs = split(index_expr, '.', 0);
			if(exprs.size() > 0){
				if(exprs[0].compare( "load") == 0){
					maxCheck->checkExprType = singleVar;
					minCheck->checkExprType = singleVar;
				}else if(exprs[0].compare( "add") == 0){
					maxCheck->checkExprType = fv_vInc_fInc;
					minCheck->checkExprType = fv_vDec_fDec;
				}else if(exprs[0].compare( "sub") == 0){
					maxCheck->checkExprType = fv_vInc_fInc;
					minCheck->checkExprType = fv_vDec_fDec;
				}else if(exprs[0].compare( "mul") == 0){
					maxCheck->checkExprType = fv_vInc_fInc;
					minCheck->checkExprType = fv_vDec_fDec;
				}else if(exprs[0].compare( "sdiv") == 0){
					maxCheck->checkExprType = fv_vDec_fInc;
					minCheck->checkExprType = fv_vInc_fDec;
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

	void printComputedIndexes(std::map<Value*, RangeCheck*>& rangeChecks){
		errs() << "\n-------------------------------------------------------\n";
		errs() << "# Print computed array indexes:\n";
		errs() << "-------------------------------------------------------\n";

		for(std::map<Value*, RangeCheck*>::iterator it = rangeChecks.begin(); it != rangeChecks.end(); it++){
			RangeCheck* index = (*it).second;
			errs() << "# Range checks: \n";
			errs() << "    - " << *(index->check) << "\n";

			std::set<Instruction*> def_instrs = index->def_instrs;
			errs() << "# Definition instructions: \n";
			for (std::set<Instruction*>::iterator it2 = def_instrs.begin();it2 != def_instrs.end(); it2++) {
				errs() << "    -" << *(*it2) << "\n";
			}

			errs() << "# Expression: \n";
			errs() << index->index_expr << "\n";

			errs() << "\n";
		}
	}

	std::vector<std::string> split(std::string work, char delim, int rep) {
		std::vector<std::string> flds;
	    std::string buf = "";
	    unsigned long i = 0;
	    while (i < work.size()) {
	        if (work[i] != delim)
	            buf += work[i];
	        else if (rep == 1) {
	            flds.push_back(buf);
	            buf = "";
	        } else if (buf.length() > 0) {
	            flds.push_back(buf);
	            buf = "";
	        }
	        i++;
	    }
	    if (!buf.empty())
	        flds.push_back(buf);
	    return flds;
	}
	//Calculate the dom set of each basic block
	void getDominators(
			std::map<MCFG_Node*, std::set<MCFG_Node*> > &dominatorSet,
			std::vector<MCFG_Node*> MCFG) {
//		errs()<<"******************GET DOMINATORS************************\n";
		MCFG_Node* entry;
		for (std::vector<MCFG_Node*>::iterator it = MCFG.begin();
				it != MCFG.end(); ++it) {
			MCFG_Node* node = *it;
			if (node->preds.empty()) {
				entry = node;
				break;
			}
		}

		std::list<MCFG_Node*> nodeList;
		nodeList.push_back(entry);
		int current = 1;
		int next = 0;
		std::set<MCFG_Node*> visited;

		while (!nodeList.empty()) {
			MCFG_Node* node = nodeList.front();
//			errs()<<"A node "<<node->label<<" and its preds:\n";
			nodeList.pop_front();
			visited.insert(node);
			std::set<MCFG_Node*> succNodes = node->succs;
			for (std::set<MCFG_Node*>::iterator it = succNodes.begin();
					it != succNodes.end(); ++it) {
				MCFG_Node* succ = *it;
				if (visited.find(succ) == visited.end()) {
					nodeList.push_back(succ);
					next++;
				}
			}

			std::set<MCFG_Node*> dominators;
			std::map<MCFG_Node*, std::set<MCFG_Node*> > predDoms;

			std::set<MCFG_Node*> predNodes = node->preds;
			for (std::set<MCFG_Node*>::iterator it = predNodes.begin();
					it != predNodes.end(); ++it) {
				MCFG_Node* pred = *it;
//				errs()<< "The pred "<<pred->label<<" : \n";
				if (dominatorSet.find(pred) != dominatorSet.end()) {
//					errs()<< "can be found in the dom set\n";
					predDoms.insert(
							std::pair<MCFG_Node*, std::set<MCFG_Node*> >(pred,
									(*dominatorSet.find(pred)).second));
				}
			}
			bool first = true;
			for (std::map<MCFG_Node*, std::set<MCFG_Node*> >::iterator it =
					predDoms.begin(); it != predDoms.end(); ++it) {
				std::set<MCFG_Node*> doms = (*it).second;
				std::set<MCFG_Node*> temp;
				if (first) {
					//The dominators of the first pred
					for (std::set<MCFG_Node*>::iterator setItr = doms.begin();
							setItr != doms.end(); ++setItr) {
						dominators.insert(*setItr);
					}
					first = false;
				} else {
					//Do Intersection
					std::set<MCFG_Node*>::iterator setItr;
					for (setItr = dominators.begin();
							setItr != dominators.end(); ++setItr) {
//						errs()<< "\tIterating......"<<(*setItr)->label<<"\n";
						if (doms.find(*setItr) == doms.end()) {
							temp.insert(*setItr);
						}
					}
					for (setItr = temp.begin(); setItr != temp.end();
							++setItr) {
						if (dominators.find(*setItr) != dominators.end()) {
							dominators.erase(dominators.find(*setItr));
						}
					}
				}
			}

			dominators.insert(node);
			dominatorSet.insert(
					std::pair<MCFG_Node*, std::set<MCFG_Node*> >(node,
							dominators));
//			errs()<< "+-+-+-Dominators:\n";
//			for(std::set<MCFG_Node*>::iterator setItr = dominators.begin(); setItr != dominators.end(); ++setItr) {
//				errs()<< "\t\t"<<(*setItr)->label<<"\n";
//			}

			current--;
			if (current == 0) {
				current = next;
				next = 0;
			}
		}
	}

	void printDominators(
			std::map<MCFG_Node*, std::set<MCFG_Node*> > dominatorSet) {
		errs() << "-------------------------------------------------------\n";
		errs() << "# Print Dominators:\n";
		errs() << "-------------------------------------------------------\n";
		for (std::map<MCFG_Node*, std::set<MCFG_Node*> >::iterator it =
				dominatorSet.begin(); it != dominatorSet.end(); ++it) {
			errs() << "++++Node: " << it->first->label << "\n";
			errs() << "++++Dominators:\n";

			for (std::set<MCFG_Node*>::iterator domItr = it->second.begin();
					domItr != it->second.end(); ++domItr) {
				errs() << "\t----Node: " << (*domItr)->label << "\n";
			}
		}
	}

	void findBackEdges(std::set<std::pair<MCFG_Node*, MCFG_Node*> > &backEdges,
			std::map<MCFG_Node*, std::set<MCFG_Node*> > dominatorSet) {
//		errs()<<"******************GET BACKEDGES************************\n";
		std::set<MCFG_Node*> nodes;
		for (std::map<MCFG_Node*, std::set<MCFG_Node*> >::iterator it =
				dominatorSet.begin(); it != dominatorSet.end(); ++it) {
			nodes.insert(it->first);
		}
		for (std::set<MCFG_Node*>::iterator it = nodes.begin();
				it != nodes.end(); ++it) {
			for (std::set<MCFG_Node*>::iterator it2 = nodes.begin();
					it2 != nodes.end(); ++it2) {

				MCFG_Node* node = *it2;
				if (dominates(*it, node, dominatorSet)
						&& (((*it)->succs).find(node) != ((*it)->succs).end())) {
					//*it2 is the dominator of *it and there is an edge from it to it2 => This is a back edge.
					backEdges.insert(
							std::pair<MCFG_Node*, MCFG_Node*>((*it), (*it2)));
				}
			}
		}

//		for(std::set<std::pair<MCFG_Node*, MCFG_Node*> >::iterator it = backEdges.begin(); it != backEdges.end(); ++it) {
//			errs()<<"From: "<<(*it).first->label<<" To:" << it->second->label<<"\n";
//		}
	}

	//Find whether MCFG_Node B is the dominator of A
	bool dominates(MCFG_Node* A, MCFG_Node* B,
			std::map<MCFG_Node*, std::set<MCFG_Node*> > dominatorSet) {
		std::set<MCFG_Node*> dominator = dominatorSet.find(A)->second;
		if (dominator.find(B) != dominator.end()) {
			return true;
		} else {
			return false;
		}
	}

	void findLoops(
			std::map<std::pair<MCFG_Node*, MCFG_Node*>, std::set<MCFG_Node*> > &loops,
			std::set<std::pair<MCFG_Node*, MCFG_Node*> > backEdges,
			std::map<MCFG_Node*, std::set<MCFG_Node*> > dominatorSet) {
		errs() << "******************FIND LOOPS************************\n";
		for (std::set<std::pair<MCFG_Node*, MCFG_Node*> >::iterator it =
				backEdges.begin(); it != backEdges.end(); ++it) {
			std::set<MCFG_Node*> loopNodes;

			std::list<MCFG_Node*> nodeList;
			nodeList.push_back(it->first);
			int current = 1;
			int next = 0;
			std::set<MCFG_Node*> visited;

			while (!nodeList.empty()) {
				MCFG_Node* node = nodeList.front();
				nodeList.pop_front();
				visited.insert(node);
				std::set<MCFG_Node*> predNodes = node->preds;
				for (std::set<MCFG_Node*>::iterator predIt = predNodes.begin();
						predIt != predNodes.end(); ++predIt) {
					MCFG_Node* pred = *predIt;
					if (visited.find(pred) == visited.end()) {
						nodeList.push_back(pred);
						next++;
					}
				}

				if (dominates(node, (it->second), dominatorSet)
						//&& node != it->second && node != it->first
						) {
					loopNodes.insert(node);
				}

				current--;
				if (current == 0) {
					current = next;
					next = 0;
				}
			}

			loops.insert(
					std::pair<std::pair<MCFG_Node*, MCFG_Node*>,
							std::set<MCFG_Node*> >(*it, loopNodes));
		}

		for (std::map<std::pair<MCFG_Node*, MCFG_Node*>, std::set<MCFG_Node*> >::iterator it =
				loops.begin(); it != loops.end(); ++it) {
			errs() << "From: " << (*it).first.first->label << " To:"
					<< it->first.second->label << "\n";
			errs() << "Nodes:\n";
			for (std::set<MCFG_Node*>::iterator nodeIt = it->second.begin();
					nodeIt != it->second.end(); ++nodeIt) {
				errs() << "\t" << (*nodeIt)->label << "\n";
			}
		}
	}

//	void findForLoops(
//			std::map<
//					std::pair<std::pair<MCFG_Node*, MCFG_Node*>,
//							std::set<MCFG_Node*> >, std::pair<int, int> > &forLoops,
//			std::map<std::pair<MCFG_Node*, MCFG_Node*>, std::set<MCFG_Node*> > loops,
//			std::map<Value*, ComputedArrayIndex*> computedIndexes) {
//
//		//While and For - if the variable used to control the loop is
//
//	}

	void findLoopInvariant(std::map<MCFG_Node*, std::set<Instruction*> > &loopInvariant, std::map<MCFG_Node*, std::set<Instruction*> > &hoistedChecks, std::map<MCFG_Node*, std::set<MCFG_Node*> > dominatorSet, std::map<std::pair<MCFG_Node*, MCFG_Node*>, std::set<MCFG_Node*> > loops, std::map<Value*, ComputedArrayIndex*> computedIndexes) {
		errs() << "******************FIND LOOP INVARIANTS************************\n";

		for(std::map<std::pair<MCFG_Node*, MCFG_Node*>, std::set<MCFG_Node*> >::iterator it = loops.begin(); it != loops.end(); ++it) {

			std::set<MCFG_Node*> loopNode = (*it).second;
			std::set<MCFG_Node*> exit;
			std::set<MCFG_Node*> dominators;
			//For all the loop nodes, if it has a succ that is not in the loop, it is an exit
//			for(std::set<MCFG_Node*>::iterator nodeIt = loopNode.begin(); nodeIt != loopNode.end(); ++nodeIt) {
//				MCFG_Node* node = *nodeIt;
//				std::set<MCFG_Node*> succs = node->succs;
//				for(std::set<MCFG_Node*>::iterator succIt = succs.begin(); succIt != succs.end(); ++succIt) {
//					if(loopNode.find(*succIt) == loopNode.end()) {
//						exit.insert(node);
//						errs()<<"exit node: "<<node->label<<"\n";
//						break;
//					}
//				}
//			}

			exit.insert((*it).first.second);

			for(std::set<MCFG_Node*>::iterator nodeIt = loopNode.begin(); nodeIt != loopNode.end(); ++nodeIt) {
				MCFG_Node* node = *nodeIt;
				for(std::set<MCFG_Node*>::iterator exitIt = exit.begin(); exitIt != exit.end(); ++exitIt) {
					MCFG_Node* exitNode = *exitIt;
					if(dominates(exitNode, node, dominatorSet)) {
						dominators.insert(node);
					}
				}
			}

//			for(std::set<MCFG_Node*>::iterator nodeIt = loopNode.begin(); nodeIt != loopNode.end(); ++nodeIt) {
			for(std::set<MCFG_Node*>::iterator nodeIt = dominators.begin(); nodeIt != dominators.end(); ++nodeIt) {
				MCFG_Node* node = *nodeIt;
				errs()<<node->label<<"\n";
				std::set<Instruction*> hoistingList;
				std::vector<Instruction*> instrs = node->instrs;
				for(std::vector<Instruction*>::iterator instIt = instrs.begin(); instIt != instrs.end(); ++instIt) {
					Instruction* inst = *instIt;
					if(computedIndexes.find(inst) != computedIndexes.end()) {
						ComputedArrayIndex* index = computedIndexes.find(inst)->second;
						std::set<Instruction*> definitions = index->def_instrs;
						bool invariant = true;

						for(std::set<Instruction*>::iterator defIt = definitions.begin(); defIt != definitions.end(); ++defIt) {
							BasicBlock* bb = (*defIt)->getParent();
							for(std::set<MCFG_Node*>::iterator findIt = loopNode.begin(); findIt != loopNode.end(); ++findIt) {
								if((*findIt)->bb == bb) {
									invariant = false;
									break;
								}
							}
							if(!invariant) {
								break;
							}

						}
						if(invariant) {
							Instruction* previous;
							while(++instIt != instrs.end() && (*instIt)->getOpcode() == 46 ) {
								previous = *instIt;
								hoistingList.insert(previous);
							}
							--instIt;
						}
					}
				}
				if(hoistingList.size() > 0) {
					loopInvariant.insert(std::pair<MCFG_Node*, std::set<Instruction*> >(node, hoistingList));
				}
			}
		}

		for(std::map<std::pair<MCFG_Node*, MCFG_Node*>, std::set<MCFG_Node*> >::iterator it = loops.begin(); it != loops.end(); ++it) {
			MCFG_Node* entry = (*it).first.second;
			std::set<MCFG_Node*> loopPred = entry->preds;
			std::set<MCFG_Node*> loopDomPred;
			for(std::set<MCFG_Node*>::iterator predIt = loopPred.begin(); predIt != loopPred.end(); predIt++) {
				if(dominates(entry, *predIt, dominatorSet)) {
					loopDomPred.insert(*predIt);
				}
			}

			if(loopDomPred.size() == 1) {
				MCFG_Node* thePred = *loopDomPred.begin();
				std::vector<Instruction*> predInst = thePred->instrs;
				std::set<Instruction*> addedInst;

				std::set<MCFG_Node*> loopNode = it->second;
				for(std::map<MCFG_Node*, std::set<Instruction*> >::iterator deleteIt = loopInvariant.begin(); deleteIt != loopInvariant.end(); deleteIt++) {
					std::set<Instruction*> deleteSet = deleteIt->second;
					MCFG_Node* curNode = deleteIt->first;

					if(loopNode.find(deleteIt->first) != loopNode.end()) {
						std::vector<Instruction*> instSet = curNode->instrs;

						for(std::set<Instruction*>::iterator instIt = deleteSet.begin(); instIt != deleteSet.end(); instIt++) {
							bool test = false;
							for(std::vector<Instruction*>::iterator curIt = instSet.begin(); curIt != instSet.end(); curIt++) {
								if(*instIt == *curIt) {
									instSet.erase(curIt);//erase
									predInst.push_back(*instIt);//add
									addedInst.insert(*instIt);
									test = true;
									break;
								}
							}

							if(test) {
							}else {
								errs()<<"Impossible3!\n";
							}
						}

					}
				}
				if(addedInst.size() > 0) {
					hoistedChecks.insert(std::pair<MCFG_Node*, std::set<Instruction*> >(thePred, addedInst));//add set
				}
			}else {
				loopInvariant.erase(loopInvariant.begin(), loopInvariant.end());//no erase, so clear the erase set
			}
		}

		errs()<<"Erasing...\n";
		for(std::map<MCFG_Node*, std::set<Instruction*> >::iterator it = loopInvariant.begin(); it != loopInvariant.end(); it++) {
			errs()<<"MCFG_Node: "<< it->first->label<<"\n";
			for(std::set<Instruction*>::iterator instIt = it->second.begin(); instIt != it->second.end(); ++instIt) {
				errs() << "\t"<<**instIt<<"\n";
			}
		}

		errs()<<"Hoisting...\n";
		for(std::map<MCFG_Node*, std::set<Instruction*> >::iterator it = hoistedChecks.begin(); it != hoistedChecks.end(); it++) {
			errs()<<"MCFG_Node: "<< it->first->label<<"\n";
			for(std::set<Instruction*>::iterator instIt = it->second.begin(); instIt != it->second.end(); ++instIt) {
				errs() << "\t"<<**instIt<<"\n";
			}
		}

	}

	//For all checks about the same var, if all its def in the loop are changed in the same style, get it out
	void findMonotonicalVar(std::map<MCFG_Node*, std::set<Instruction*> > &monotonicalVar, std::map<MCFG_Node*, std::set<Instruction*> > &hoistedChecks, std::map<MCFG_Node*, std::set<MCFG_Node*> > dominatorSet, std::map<std::pair<MCFG_Node*, MCFG_Node*>, std::set<MCFG_Node*> > loops, std::map<Value*, ComputedArrayIndex*> computedIndexes) {
		errs() << "******************FIND MONOTONICAL VAR************************\n";

		for(std::map<std::pair<MCFG_Node*, MCFG_Node*>, std::set<MCFG_Node*> >::iterator it = loops.begin(); it != loops.end(); ++it) {

			std::set<MCFG_Node*> loopNode = (*it).second;
			std::set<MCFG_Node*> exit;
			std::set<MCFG_Node*> dominators;

			exit.insert((*it).first.second);

			for(std::set<MCFG_Node*>::iterator nodeIt = loopNode.begin(); nodeIt != loopNode.end(); ++nodeIt) {
				MCFG_Node* node = *nodeIt;
				for(std::set<MCFG_Node*>::iterator exitIt = exit.begin(); exitIt != exit.end(); ++exitIt) {
					MCFG_Node* exitNode = *exitIt;
					if(dominates(exitNode, node, dominatorSet)) {
						dominators.insert(node);
					}
				}
			}

//			errs()<<"Total: "<<loopNode.size()<<"\n";
			//for(std::set<MCFG_Node*>::iterator nodeIt = dominators.begin(); nodeIt != dominators.end(); ++nodeIt) {
			for(std::set<MCFG_Node*>::iterator nodeIt = loopNode.begin(); nodeIt != loopNode.end(); ++nodeIt) {
				MCFG_Node* node = *nodeIt;
//				errs()<<node->label<<"\n";
				std::set<Instruction*> checks;
				std::vector<Instruction*> instrs = node->instrs;
				for(std::vector<Instruction*>::iterator instIt = instrs.begin(); instIt != instrs.end(); ++instIt) {
					Instruction* inst = *instIt;
					if(computedIndexes.find(inst) != computedIndexes.end()) {
						ComputedArrayIndex* index = computedIndexes.find(inst)->second;
//						errs()<<"It is a check: "<<*inst<<"\n";
						int style = -2;//1 - inc, -1 - dec, 0 - no style
						std::set<Instruction*> def = index->def_instrs;
						for(std::set<Instruction*>::iterator defIt = def.begin(); defIt != def.end(); defIt++) {
							Instruction* theDef = *defIt;
//							errs()<<"-----It is a def: "<<*theDef<<"\n";
							bool inLoop = false;
							for(std::set<MCFG_Node*>::iterator findIt = loopNode.begin(); findIt != loopNode.end(); ++findIt) {
								MCFG_Node* curNode = *findIt;
								std::vector<Instruction*> instList = curNode->instrs;
								for(std::vector<Instruction*>::iterator curIt = instList.begin(); curIt != instList.end(); curIt++) {
									if(*curIt == theDef) {
										inLoop = true;
										break;
									}
								}
							}
							if(inLoop) {
//								errs()<<"\t"<<*theDef<<"\n";
								//BasicBlock::iterator backIt = theDef;
								//--backIt;
								//errs()<<"\t--:"<<*backIt<<"\n";
								//Instruction* op = backIt;
								EffectType effect = getEffect(theDef);
								//errs()<<"effect: "<< effect<<"\n";
								//errs()<<"style: "<< style<<"\n";
								if(effect == 1 || effect == 3 || effect == 5) {
									if(style == -2 || style == 1) {
										style = 1;
									}else {
										style = 0;
									}
								}else if(effect == 2 || effect == 4) {
									if(style == -2 || style == -1) {
										style = -1;
									}else {
										style = 0;
									}
								}else {
									style = 0;
								}

								if(style == 0) {
									break;
								}
							}
						}


						if(style == 1) {
							while(++instIt != instrs.end() && (*instIt)->getOpcode() == 46 ) {
					            CmpInst *cmpInst = dyn_cast<CmpInst>(*instIt);
					            if (cmpInst->getPredicate() == CmpInst::ICMP_SGE) {
					            	checks.insert(cmpInst);
//					            	errs()<<"Cmp: "<< *cmpInst<<"\n";
					            }
							}
							--instIt;
						}else if (style == -1) {
							while(++instIt != instrs.end() && (*instIt)->getOpcode() == 46 ) {
					            CmpInst *cmpInst = dyn_cast<CmpInst>(*instIt);
					            if (cmpInst->getPredicate() == CmpInst::ICMP_SLT) {
					            	checks.insert(cmpInst);
//					            	errs()<<"Cmp: "<< *cmpInst<<"\n";
					            }
							}

							--instIt;
						}else {
							//doing nothing
						}
					}
				}

				if(checks.size() > 0 ) {
					monotonicalVar.insert(std::pair<MCFG_Node*, std::set<Instruction*> >(node, checks));
				}
			}

//			errs()<<"Monotonical...\n";
//			for(std::map<MCFG_Node*, std::set<Instruction*> >::iterator theIt = monotonicalVar.begin(); theIt != monotonicalVar.end(); theIt++) {
//				std::set<Instruction*> instVec = theIt->second;
//				errs()<<"MCFG_Node: "<<theIt->first->label<<"\n";
//				for(std::set<Instruction*>::iterator vecIt = instVec.begin(); vecIt != instVec.end(); vecIt++) {
//					errs()<<"\t"<<**vecIt<<"\n";
//				}
//			}
		}

		for(std::map<std::pair<MCFG_Node*, MCFG_Node*>, std::set<MCFG_Node*> >::iterator it = loops.begin(); it != loops.end(); ++it) {
			MCFG_Node* entry = (*it).first.second;
			std::set<MCFG_Node*> loopPred = entry->preds;
			std::set<MCFG_Node*> loopDomPred;
			for(std::set<MCFG_Node*>::iterator predIt = loopPred.begin(); predIt != loopPred.end(); predIt++) {
				if(dominates(entry, *predIt, dominatorSet)) {
					loopDomPred.insert(*predIt);
				}
			}

			if(loopDomPred.size() == 1) {
//				errs()<<"pred's size = 1\n";
				MCFG_Node* thePred = *loopDomPred.begin();
				std::vector<Instruction*> predInst = thePred->instrs;
				std::set<Instruction*> addedInst;

				std::set<MCFG_Node*> loopNode = it->second;
				for(std::map<MCFG_Node*, std::set<Instruction*> >::iterator deleteIt = monotonicalVar.begin(); deleteIt != monotonicalVar.end(); deleteIt++) {
					std::set<Instruction*> deleteSet = deleteIt->second;
					MCFG_Node* curNode = deleteIt->first;

					if(loopNode.find(deleteIt->first) != loopNode.end()) {
						std::vector<Instruction*> instSet = curNode->instrs;

						for(std::set<Instruction*>::iterator instIt = deleteSet.begin(); instIt != deleteSet.end(); instIt++) {
							bool test = false;
							for(std::vector<Instruction*>::iterator curIt = instSet.begin(); curIt != instSet.end(); curIt++) {
								if(*instIt == *curIt) {
//									errs()<<"\t"<<**instIt<<"\n";
									instSet.erase(curIt);//erase
									predInst.push_back(*instIt);//add
									addedInst.insert(*instIt);
									test = true;
									break;
								}
							}

							if(test) {
							}else {
								errs()<<"Impossible3!\n";
							}
						}
					}
				}
				if(addedInst.size() > 0) {
					hoistedChecks.insert(std::pair<MCFG_Node*, std::set<Instruction*> >(thePred, addedInst));//add set
				}

			}else {
				monotonicalVar.erase(monotonicalVar.begin(), monotonicalVar.end());//no erase, so clear the erase set
			}
		}

		errs()<<"Erasing...\n";
		for(std::map<MCFG_Node*, std::set<Instruction*> >::iterator it = monotonicalVar.begin(); it != monotonicalVar.end(); it++) {
			errs()<<"MCFG_Node: "<< it->first->label<<"\n";
			for(std::set<Instruction*>::iterator instIt = it->second.begin(); instIt != it->second.end(); ++instIt) {
				errs() << "\t"<<**instIt<<"\n";
			}
		}

		errs()<<"Hoisting...\n";
		for(std::map<MCFG_Node*, std::set<Instruction*> >::iterator it = hoistedChecks.begin(); it != hoistedChecks.end(); it++) {
			errs()<<"MCFG_Node: "<< it->first->label<<"\n";
			for(std::set<Instruction*>::iterator instIt = it->second.begin(); instIt != it->second.end(); ++instIt) {
				errs() << "\t"<<**instIt<<"\n";
			}
		}

	}


	void hoistInsideLoop(std::map<MCFG_Node*, std::set<Instruction*> > &deletedChecks, std::map<MCFG_Node*, std::set<Instruction*> > &hoistedChecks, std::vector<MCFG_Node*> &MCFG, std::map<MCFG_Node*, std::set<MCFG_Node*> > dominatorSet, std::map<std::pair<MCFG_Node*, MCFG_Node*>, std::set<MCFG_Node*> > loops, std::map<Value*, ComputedArrayIndex*> computedIndexes) {
		errs() << "******************HOISTING INSIDE LOOPS************************\n";
		for(std::map<std::pair<MCFG_Node*, MCFG_Node*>, std::set<MCFG_Node*> >::iterator it = loops.begin(); it != loops.end(); ++it) {
			bool changed = true;
			std::set<MCFG_Node*> ND;
			std::set<MCFG_Node*> exit;
			std::set<MCFG_Node*> P;

			std::set<MCFG_Node*> loopNode = (*it).second;

			exit.insert((*it).first.second);
			//For all the loop nodes, if it has a succ that is not in the loop, it is an exit
//			for(std::set<MCFG_Node*>::iterator nodeIt = loopNode.begin(); nodeIt != loopNode.end(); ++nodeIt) {
//				MCFG_Node* node = *nodeIt;
//				std::set<MCFG_Node*> succs = node->succs;
//				for(std::set<MCFG_Node*>::iterator succIt = succs.begin(); succIt != succs.end(); ++succIt) {
//					if(loopNode.find(*succIt) == loopNode.end()) {
//						exit.insert(node);
//						break;
//					}
//				}
//			}
//
			//For all the loop nodes, if it cannot dominate all the loop exit, insert it to ND
			for(std::set<MCFG_Node*>::iterator nodeIt = loopNode.begin(); nodeIt != loopNode.end(); ++nodeIt) {
				MCFG_Node* node = *nodeIt;
				for(std::set<MCFG_Node*>::iterator exitIt = exit.begin(); exitIt != exit.end(); ++exitIt) {
					MCFG_Node* eNode = *exitIt;
					if(!dominates(eNode, node, dominatorSet)) {
						ND.insert(node);
						break;
					}
				}
			}

			//For all the loop node, if it is the only pred of all its succs and at least one of its succ belongs to ND, insert it to P
			for(std::set<MCFG_Node*>::iterator nodeIt = loopNode.begin(); nodeIt != loopNode.end(); ++nodeIt) {
				MCFG_Node* node = *nodeIt;
				std::set<MCFG_Node*> succs = node->succs;
				bool unique = true;
				bool inND = false;
				for(std::set<MCFG_Node*>::iterator succIt = succs.begin(); succIt != succs.end(); ++succIt) {
					MCFG_Node* succ = *succIt;
					if(succ->preds.size() != 1) {
						unique = false;
					}
					if(ND.find(succ) != ND.end()) {
						inND = true;
					}
					if(unique && inND) {
						P.insert(node);
					}
				}
			}

//			errs()<<"Exit...\n";
//			for(std::set<MCFG_Node*>::iterator theIt = exit.begin(); theIt != exit.end(); theIt++) {
//				errs()<<"\t"<<(*theIt)->label<<"\n";
//			}
//
//			errs()<<"ND...\n";
//			for(std::set<MCFG_Node*>::iterator theIt = ND.begin(); theIt != ND.end(); theIt++) {
//				errs()<<"\t"<<(*theIt)->label<<"\n";
//			}
//
//			errs()<<"P...\n";
//			for(std::set<MCFG_Node*>::iterator theIt = P.begin(); theIt != P.end(); theIt++) {
//				errs()<<"\t"<<(*theIt)->label<<"\n";
//			}


			//While there are hoisted insts in the loop
			while(changed){
				errs()<<"**********changed**************\n";
				changed = false;
				//First, find out all the available checks in the nodes in the program
				std::map<MCFG_Node*, std::map<Value*, ComputedArrayIndex*> > checks;
				for(std::map<MCFG_Node*, std::set<MCFG_Node*> >::iterator pIt = dominatorSet.begin(); pIt != dominatorSet.end(); ++pIt) {
//				for(std::set<MCFG_Node*>::iterator pIt = P.begin(); pIt != P.end(); ++pIt) {
					MCFG_Node* node = pIt->first;
					std::map<Value*, ComputedArrayIndex*> check;

					std::vector<Instruction*> instrs = node->instrs;
					for(std::vector<Instruction*>::iterator instIt = instrs.end(); instIt != instrs.begin(); --instIt) {
						std::vector<Instruction*>::iterator realIt = instIt;
						realIt--;
						Instruction* inst = *realIt;

						if(inst->getOpcode() == 35) {
							if(computedIndexes.find(inst) != computedIndexes.end()) {
//								BasicBlock* bb = inst->getParent();
								ComputedArrayIndex* index = (*computedIndexes.find(inst)).second;
								check.insert(std::pair<Value*, ComputedArrayIndex*>(inst, index));
							}else {
								errs()<<"There is no reason that sext cannot be found in computedIndexes!\n";
							}
						}
					}
					checks.insert(std::pair<MCFG_Node*, std::map<Value*, ComputedArrayIndex*> >(node, check));
				}

//				for(std::map<MCFG_Node*, std::map<Value*, ComputedArrayIndex*> >::iterator checkIt = checks.begin(); checkIt != checks.end(); checkIt ++) {
//					for(std::map<Value*, ComputedArrayIndex*>::iterator cIt = checkIt->second.begin(); cIt != checkIt->second.end(); cIt++) {
//						errs()<<"\t"<<*(cIt->first)<<"\n";
//					}
//				}

				std::map<MCFG_Node*, std::set<Instruction*> > curDeleteSet;
				std::map<MCFG_Node*, std::set<Instruction*> > curHoistSet;

				//For all the node n in P
				for(std::set<MCFG_Node*>::iterator pIt = P.begin(); pIt != P.end(); ++pIt) {
					MCFG_Node* node = *pIt;
					std::set<MCFG_Node*> succs = node->succs;
					std::map<SimpleArrayIndex*, std::map<MCFG_Node*, ComputedArrayIndex*> > hoistingList;
					std::set<SimpleArrayIndex*> intersection;
					bool firstTime = true;

					errs()<<"P Node: "<< node->label<<"\n";
//					int succSize = 0;
//					for(std::set<MCFG_Node*>::iterator succIt = succs.begin(); succIt != succs.end(); ++succIt) {
//						MCFG_Node* succ = *succIt;
//						if(loopNode.find(succ) == loopNode.end()) {
//							errs()<<"Continue...\n";
//							continue;
//						}
//						succSize++;
//					}

					//For all the succ s of n
					for(std::set<MCFG_Node*>::iterator succIt = succs.begin(); succIt != succs.end(); ++succIt) {
						MCFG_Node* succ = *succIt;
						if(loopNode.find(succ) == loopNode.end()) {
							errs()<<"Continue...\n";
							continue;
						}

						errs()<<"\tSucc Node: "<< succ->label<<"\n";
						//If there are checks in s
						if(checks.find(*succIt) != checks.end()){
							std::map<Value*, ComputedArrayIndex*> check = checks.find(*succIt)->second;
							if(firstTime){//If it is the first succ
								firstTime = false;
								//For all the checks
								for(std::map<Value*, ComputedArrayIndex*>::iterator cIt = check.begin(); cIt != check.end(); ++cIt) {
									std::map<MCFG_Node*, ComputedArrayIndex*> sameCheckMap;
									ComputedArrayIndex* cIndex = cIt->second;
									sameCheckMap.insert(std::pair<MCFG_Node*, ComputedArrayIndex*>(succ, cIndex));
									//Change it to SimpleArrayIndex
									SimpleArrayIndex* sIndex = new SimpleArrayIndex();
									sIndex->index_expr = cIndex->index_expr;
									sIndex->def_instrs = cIndex->def_instrs;
									sIndex->max = dyn_cast<Constant>(cIndex->maxCmp->getOperand(1));
									sIndex->min = dyn_cast<Constant>(cIndex->minCmp->getOperand(1));
									intersection.insert(sIndex);
									errs()<<"ComputedArrayIndex: "<<(*cIndex->index)<<"\n";
									hoistingList.insert(std::pair<SimpleArrayIndex*, std::map<MCFG_Node*, ComputedArrayIndex*> >(sIndex, sameCheckMap));
								}
							}else{//If it is not the first succ
								std::set<SimpleArrayIndex*> deleteSet;//No longer in the intersection and hoistingList any more

								for(std::set<SimpleArrayIndex*>::iterator interIt = intersection.begin(); interIt != intersection.end(); ++interIt) {
									SimpleArrayIndex* first = *interIt;
									bool toStay = false;//Whether the SimpleArrayIndex in the intersection should stay in it
									//For all the checks
									for(std::map<Value*, ComputedArrayIndex*>::iterator checkIt = check.begin(); checkIt != check.end(); ++checkIt) {
										ComputedArrayIndex* secondTemp = checkIt->second;
										//If the index expressions are the same
										if(first->index_expr==secondTemp->index_expr) {
											std::set<Instruction*> firstDef = first->def_instrs;
											std::set<Instruction*> secondDef = secondTemp->def_instrs;
											bool same = true;
											//If all defs in the first can be found in the second - cond1
											for(std::set<Instruction*>::iterator defIt = firstDef.begin(); defIt != firstDef.end(); ++defIt) {
												if(secondDef.find(*defIt) == secondDef.end()) {
													same = false;
													break;
												}
											}
											//If cond1 is satisfied, check if all the defs in the second can be found in the first - cond2
											if(same) {
												for(std::set<Instruction*>::iterator defIt = secondDef.begin(); defIt != secondDef.end(); ++defIt) {
													if(firstDef.find(*defIt) == firstDef.end()) {
														same = false;
														break;
													}
												}
											}
											//If cond2 is satisfied, check if the bound of the checks are the same
											if(same) {
												APInt firstMax = first->max->getUniqueInteger();
												APInt firstMin = first->min->getUniqueInteger();
												APInt secondMax = dyn_cast<Constant>(secondTemp->maxCmp->getOperand(1))->getUniqueInteger();
												APInt secondMin = dyn_cast<Constant>(secondTemp->minCmp->getOperand(1))->getUniqueInteger();
												errs()<<"first operand: "<<firstMax<<"\n";
												errs()<<"second operand: "<<secondMax<<"\n";
												if(firstMax.eq(secondMax) && firstMin.eq(secondMin)) {
													if(hoistingList.find(first) != hoistingList.end()) {
														std::map<MCFG_Node*, ComputedArrayIndex*> sameCheckMap = hoistingList.find(first)->second;
														hoistingList.erase(hoistingList.find(first));
														sameCheckMap.insert(std::pair<MCFG_Node*, ComputedArrayIndex*>(succ, secondTemp));
														errs()<<"Same check:"<<*(secondTemp->index)<<"\n";
														hoistingList.insert(std::pair<SimpleArrayIndex*, std::map<MCFG_Node*, ComputedArrayIndex*> >(first, sameCheckMap));
														toStay = true;
													}else{
														errs()<<"Impossible!\n";
													}


//												}else{
//													toDelete = true;
												}
//											}else {//The checks are not the same
//												toDelete = true;
											}
//										} else {
//											toDelete = true;
										}
									}
									if(!toStay) {
										deleteSet.insert(first);
									}
								}

								//Remove the different checks
								for(std::set<SimpleArrayIndex*>::iterator deleteIt = deleteSet.begin(); deleteIt != deleteSet.end(); ++deleteIt) {
									if(intersection.find(*deleteIt) != intersection.end()) {
										intersection.erase(intersection.find(*deleteIt));
									}else {
										errs()<<"impossible4!!!\n";
									}
									if(hoistingList.find(*deleteIt) != hoistingList.end()) {
										hoistingList.erase(hoistingList.find(*deleteIt));
									}else {
										errs()<<"impossible5!!!\n";
									}
								}

							}
						}
					}
					for(std::map<SimpleArrayIndex*, std::map<MCFG_Node*, ComputedArrayIndex*> >::iterator simpleIt = hoistingList.begin(); simpleIt != hoistingList.end(); simpleIt++) {
						errs()<<"SimpleArrayIndex: "<<simpleIt->first->index_expr<<"\n";
						errs()<<"\t"<<simpleIt->second.size()<<"\n";
					}
//

					for(std::map<SimpleArrayIndex*, std::map<MCFG_Node*, ComputedArrayIndex*> >::iterator simpleIt = hoistingList.begin(); simpleIt != hoistingList.end(); simpleIt++) {
						std::map<MCFG_Node*, ComputedArrayIndex*> removeMap = simpleIt->second;
						bool hoist = true;
						for(std::map<MCFG_Node*, ComputedArrayIndex*>::iterator rmIt = removeMap.begin(); rmIt != removeMap.end(); rmIt++) {
							MCFG_Node* dNode = rmIt->first;
							std::set<Instruction*> tInst;
							std::set<Instruction*> dInst;
							if(curDeleteSet.find(dNode) != curDeleteSet.end()) {
								dInst = curDeleteSet.find(dNode)->second;
								curDeleteSet.erase(curDeleteSet.find(dNode));
							}
							std::set<Instruction*> hInst;

							std::vector<Instruction*> succInst = (rmIt->first)->instrs;

							for(std::vector<Instruction*>::iterator iIt = succInst.begin(); iIt != succInst.end(); iIt++) {
								if(*iIt == rmIt->second->index) {
									Instruction* previous;
									while(++iIt != succInst.end() && (*iIt)->getOpcode() == 46 ) {
										previous = *iIt;
										tInst.insert(previous);
										dInst.insert(previous);
									}
									--iIt;
								}
							}
							if(hoist){
								if(curHoistSet.find(node) != curHoistSet.end()) {
									hInst = curHoistSet.find(node)->second;
									curHoistSet.erase(curHoistSet.find(node));
								}
								for(std::set<Instruction*>::iterator hIt = tInst.begin(); hIt != tInst.end(); hIt++) {
									hInst.insert(*hIt);
								}
								if(hInst.size() > 0) {
									curHoistSet.insert(std::pair<MCFG_Node*, std::set<Instruction*> >(node, hInst));
								}
								hoist = false;
							}

							if(dInst.size() > 0) {
								curDeleteSet.insert(std::pair<MCFG_Node*, std::set<Instruction*> >(dNode, dInst));

							}
						}
					}

					if(curDeleteSet.size() > 0 || curHoistSet.size() > 0) {
						changed = true;
					}

					errs()<<"DeleteSet...\n";
					for(std::map<MCFG_Node*, std::set<Instruction*> >::iterator aIt = curDeleteSet.begin(); aIt != curDeleteSet.end(); aIt++) {
						errs()<<(aIt->first)->label<<"\n";
						std::set<Instruction*> dInst = aIt->second;
						for(std::set<Instruction*>::iterator ddIt = dInst.begin(); ddIt != dInst.end(); ddIt++) {
							errs()<<"\t"<<**ddIt<<"\n";
						}
					}

					errs()<<"HoistSet...\n";
					for(std::map<MCFG_Node*, std::set<Instruction*> >::iterator aIt = curHoistSet.begin(); aIt != curHoistSet.end(); aIt++) {
						errs()<<(aIt->first)->label<<"\n";
						std::set<Instruction*> dInst = aIt->second;
						for(std::set<Instruction*>::iterator ddIt = dInst.begin(); ddIt != dInst.end(); ddIt++) {
							errs()<<"\t"<<**ddIt<<"\n";
						}
					}

				}

				//For all the loop nodes, do delete
				for(std::set<MCFG_Node*>::iterator nodeIt = loopNode.begin(); nodeIt != loopNode.end(); ++nodeIt) {
					MCFG_Node* node = *nodeIt;
					if(curDeleteSet.find(node) != curDeleteSet.end()) {
						std::vector<Instruction*> instSet = node->instrs;
						std::set<Instruction*> deleteInst = curDeleteSet.find(node)->second;
						for(std::set<Instruction*>::iterator instIt = deleteInst.begin(); instIt != deleteInst.end(); instIt++) {
							for(std::vector<Instruction*>::iterator curIt = (node->instrs).begin(); curIt != (node->instrs).end(); curIt++) {
								if(*instIt == *curIt) {
//									errs()<<"\t"<<**instIt<<"\n";
									(node->instrs).erase(curIt);//erase
									break;
								}
							}

						}
					}
				}

				//For all the loop nodes, do hoist
				for(std::set<MCFG_Node*>::iterator nodeIt = loopNode.begin(); nodeIt != loopNode.end(); ++nodeIt) {
					MCFG_Node* node = *nodeIt;
					if(curHoistSet.find(node) != curHoistSet.end()) {
						std::vector<Instruction*> instSet = node->instrs;
						std::set<Instruction*> hoistInst = curHoistSet.find(node)->second;
						for(std::set<Instruction*>::iterator instIt = hoistInst.begin(); instIt != hoistInst.end(); instIt++) {
							(node->instrs).push_back(*instIt);
						}
					}
				}

				//If the lines in curDeleteSet is not hoisted before, just add that lines to deletedChecks;
				//If the lines in curHoistSet, add that lines to hoistedChecks
				for(std::map<MCFG_Node*, std::set<Instruction*> >::iterator aIt = curDeleteSet.begin(); aIt != curDeleteSet.end(); aIt++) {
					std::set<Instruction*> temp;
					if(deletedChecks.find(aIt->first) != deletedChecks.end()) {
						temp = (deletedChecks.find(aIt->first))->second;
					}
					for(std::set<Instruction*>::iterator hIt = (aIt->second).begin(); hIt != (aIt->second).end(); hIt++) {
						temp.insert(*hIt);
					}
					deletedChecks.insert(std::pair<MCFG_Node*, std::set<Instruction*> >(aIt->first, temp));
				}

				errs()<<"HoistChecks...\n";
				for(std::map<MCFG_Node*, std::set<Instruction*> >::iterator aIt = curHoistSet.begin(); aIt != curHoistSet.end(); aIt++) {
					std::set<Instruction*> temp;
					if(hoistedChecks.find(aIt->first) != hoistedChecks.end()) {
						temp = (hoistedChecks.find(aIt->first))->second;
					}
					for(std::set<Instruction*>::iterator hIt = (aIt->second).begin(); hIt != (aIt->second).end(); hIt++) {
						temp.insert(*hIt);
					}
					hoistedChecks.insert(std::pair<MCFG_Node*, std::set<Instruction*> >(aIt->first, temp));
				}
				//printMCFG(MCFG);


			}


		}
	}


//	void findForLoops(std::map<MCFG_Node*, std::set<Instruction*> > &deletedChecks, std::map<MCFG_Node*, std::set<Instruction*> > &hoistedChecks, std::map<std::pair<MCFG_Node*, MCFG_Node*>, std::set<MCFG_Node*> > loops, std::map<Value*, ComputedArrayIndex*> computedIndexes) {
//		errs() << "******************FIND FOR LOOPS************************\n";
//		for(std::map<std::pair<MCFG_Node*, MCFG_Node*>, std::set<MCFG_Node*> >::iterator it = loops.begin(); it != loops.end(); ++it) {
//			MCFG_Node* firstNode = (it->first).second;
//			MCFG_Node* lastNode = (it->first).first;
//			std::set<MCFG_Node*> loopNode = it->second;
//
//			Constant* max;
//			Constant* min;
//
//			Instruction* forCmp = (firstNode->instrs)[0];//Most loop.cond has only one instruction which is used for comparison
//			Constant* bound = dyn_cast<Constant>(forCmp->getOperand(0));
//			int style = 0;//1 - i < c; 2 - i <= c; 3 - i > c; 4 - i >= c
//            CmpInst *cmpInst = dyn_cast<CmpInst>(forCmp);
//            if (cmpInst->getPredicate() == CmpInst::ICMP_SLT) {
//            	style = 1;
//            	max =???
//				errs()<<"Cmp: "<< *cmpInst<<"\n";
//            } else if (cmpInst->getPredicate() == CmpInst::ICMP_SLE) {
//            	style = 2;
//				errs()<<"Cmp: "<< *cmpInst<<"\n";
//            } else if (cmpInst->getPredicate() == CmpInst::ICMP_SGT) {
//            	style = 3;
//				errs()<<"Cmp: "<< *cmpInst<<"\n";
//            } else if (cmpInst->getPredicate() == CmpInst::ICMP_SGE) {
//            	style = 4;
//				errs()<<"Cmp: "<< *cmpInst<<"\n";
//            } else {
//            	errs()<<"Impossible for Loop!\n";
//            }
//
//            BasicBlock::const_iterator backIt = forCmp;
//            backIt--;
//            const Instruction* storeInst = backIt;
//			//Value* varInst = forCmp->getOperand(0); // Assume the format is like i < 10;
//            errs()<<"Store: "<<*storeInst<<"\n";
//			const Value* varTemp = storeInst->getOperand(0);
//			std::string var = varTemp->getName().data();
//			errs()<<"Var: "<< var<<"\n";
//
//
//			std::map<MCFG_Node*, std::set<Instruction*> > curDeleteSet;
//			std::set<Instruction*> curHoistSet;
//
//
//			for(std::set<MCFG_Node*>::iterator loopIt = loopNode.begin(); loopIt != loopNode.end(); loopIt++) {
//				MCFG_Node* node = *loopIt;
//				std::vector<Instruction*> nodeInst = node->instrs;
//				for(std::vector<Instruction*>::iterator instIt = nodeInst.begin(); instIt != nodeInst.end(); instIt++) {
//					Instruction* inst = *instIt;
//					if(computedIndexes.find(inst) != computedIndexes.end()) {
//						errs()<<*inst<<"\n";
//						ComputedArrayIndex* index = (computedIndexes.find(inst))->second;
//						std::string expr = index->index_expr;
//						std::vector<std::string> exprParts = split(expr, '.', 0);
//						if(exprParts.size() > 4) {
//							break;//Only consider the situation of checks like [i+1]
//						}
//						if(exprParts.size() == 4) {
//							if(exprParts[3].compare(var) != 0) {
//								break;
//							}
//						}
//
//						if(exprParts.size() == 2) {
//							if(exprParts[1].compare(var) != 0) {
//								break;
//							}
//						}
//
//						//All the defs must be in the last node of the loop or outside the loop
//						//All the defs out side the loop must be defined by the same constant
//						//Else - don't hoist it
//						bool defLoc = true;//false - don't hoist it
//						std::set<Instruction*> initial;//size = 0 or all the inst are not store using the same constant - don't hoist
//						std::set<Instruction*> def = index->def_instrs;
//						for(std::set<Instruction*>::iterator defIt = def.begin(); defIt != def.end(); defIt++) {
//							BasicBlock* bb = (*defIt)->getParent();
//							bool inLoop = false;
//							for(std::set<MCFG_Node*>::iterator dIt = loopNode.begin(); dIt != loopNode.end(); dIt++) {
//								MCFG_Node* curNode = *dIt;
//								if(curNode->bb == bb) {
//									inLoop = true;
//									if(curNode != lastNode) {
//										defLoc = false;
//										break;
//									}
//								}
//							}
//							if(!defLoc) {
//								break;
//							}
//							if(!inLoop) {
//								initial.insert(*defIt);
//							}
//						}
//
//						bool toDelete = false;
//						if(defLoc && initial.size() > 0) {
//							Constant* c;
//							bool firstC = true;
//							for(std::set<Instruction*>::initIt = initial.begin(); initIt != initial.end(); initIt++) {
//								Value* op1 = (*initIt)->getOperand(0);
//								if(isa<Constant>(op1)) {
//									if(firstC) {
//										firstC = false;
//										c = dyn_cast<Constant>(op1);
//									}else {
//										Constant* c1 = dyn_cast<Constant>(op1);
//										if(c1->getUniqueInteger() == c->getUniqueInteger()) {
//											toDelete = true;
//										}else {
//											toDelete = false;
//										}
//									}
//								}else {
//									toDelete = false;
//								}
//							}
//						}
//
//						if(toDelete) {
//							bool hasLb = false;
//							bool hasUb = false;
//							Constant* lb;
//							Constant* up;
//							while(++instIt != nodeInst.end() && (*instIt)->getOpcode() == 46 ) {
//					            CmpInst *cmpInst = dyn_cast<CmpInst>(*instIt);
//					            if (cmpInst->getPredicate() == CmpInst::ICMP_SGE) {
//					            	lb = dyn_cast<Constant>(cmpInst->getOperand(1));
//					            	hasLb = true;
//					            	std::set<Instruction*>
//					            	deletedChecks.insert(std::pair<MCFG_Node*, std::set<Instruction*> >(node,));
//
////					            	errs()<<"Cmp: "<< *cmpInst<<"\n";
//					            }
//					            if (cmpInst->getPredicate() == CmpInst::ICMP_SLT) {
//					            	ub = dyn_cast<Constant>(cmpInst->getOperand(1));
//					            	hasUb = true;
//					            	deletedChecks.insert(cmpInst);
//					            	checks.insert(cmpInst);
////					            	errs()<<"Cmp: "<< *cmpInst<<"\n";
//					            }
//							}
//							--instIt;
//						}
//					}
//				}
//			}
//
//		}
//	}


};
}

char project::ID = 0;
int project::errorBBcount = 0;
int project::insertBBcount = 0;
static RegisterPass<project> X("project_2", "Uninitialized variables", false, false);

