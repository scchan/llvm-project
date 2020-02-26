//===- IrreducibilityElimination.cpp - Eliminate irreducibility -*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
#include "llvm/ADT/LoopWalker.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/Transforms/Utils.h"

#define DEBUG_TYPE "eliminate-irreducibility"

using namespace llvm;
using namespace llvm::PatternMatch;

using BBPredicates = DenseMap<BasicBlock *, Value *>;
using PredMap = DenseMap<BasicBlock *, BBPredicates>;
using BBVector = SmallVector<BasicBlock *, 8>;
using BBSet = SmallPtrSet<BasicBlock *, 8>;
using BBSetVector = SetVector<BasicBlock *, BBVector, BBSet>;

namespace {
struct EliminateIrreducibilityPass : public FunctionPass {
  static char ID;
  EliminateIrreducibilityPass()
      : FunctionPass(ID) {}

  void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<LoopInfoWrapperPass>();
  }

  bool runOnFunction(Function &F);
};
} // end anonymous namepsace

char EliminateIrreducibilityPass::ID = 0;

static RegisterPass<EliminateIrreducibilityPass>
X("eliminate-irreducibility", "Convert irreducible cycles into natural loops",
  false /* Only looks at CFG */,
  false /* Analysis Pass */);

FunctionPass *llvm::createEliminateIrreducibilityPass() {
  return new EliminateIrreducibilityPass();
}

static Value *invert(Value *Condition) {
  // First: Check if it's a constant
  if (Constant *C = dyn_cast<Constant>(Condition))
    return ConstantExpr::getNot(C);

  // Second: If the condition is already inverted, return the original value
  Value *NotCondition;
  if (match(Condition, m_Not(m_Value(NotCondition))))
    return NotCondition;

  if (Instruction *Inst = dyn_cast<Instruction>(Condition)) {
    // Third: Check all the users for an invert
    BasicBlock *Parent = Inst->getParent();
    for (User *U : Condition->users())
      if (Instruction *I = dyn_cast<Instruction>(U))
        if (I->getParent() == Parent && match(I, m_Not(m_Specific(Condition))))
          return I;

    // Last option: Create a new instruction
    return BinaryOperator::CreateNot(Condition, "", Parent->getTerminator());
  }

  if (Argument *Arg = dyn_cast<Argument>(Condition)) {
    BasicBlock &EntryBlock = Arg->getParent()->getEntryBlock();
    return BinaryOperator::CreateNot(Condition,
                                     Arg->getName() + ".inv",
                                     EntryBlock.getTerminator());
  }

  llvm_unreachable("Unhandled condition to invert");
}

static void squeeze(SmallVectorImpl<BasicBlock*> &CycleHeaders, const BBSetVector &Headers) {
  auto F = Headers.front()->getParent();
  auto &Context = F->getContext();
  auto BoolTrue = ConstantInt::getTrue(Context);
  auto BoolFalse = ConstantInt::getFalse(Context);
  PredMap Predicates;
  BBSetVector Predecessors;
  for (auto Header : Headers) {
    for (auto Predecessor : predecessors(Header)) {
      Predecessors.insert(Predecessor);
      auto Branch = cast<BranchInst>(Predecessor->getTerminator());
      if (!Branch->isConditional()) {
        Predicates[Header][Predecessor] = BoolTrue;
        continue;
      }
      if (Branch->getSuccessor(0) == Header) {
        Predicates[Header][Predecessor] = Branch->getCondition();
        continue;
      }
      Predicates[Header][Predecessor] = invert(Branch->getCondition());
    }
  }

  LLVM_DEBUG(dbgs() << "Found headers:";
             for (auto H : Headers) {
               dbgs() << " " << H->getName();
             }
             dbgs() << "\n");

  LLVM_DEBUG(dbgs() << "Found predecessors:";
             for (auto P : Predecessors) {
               dbgs() << " " << P->getName();
             }
             dbgs() << "\n");

    for (auto Predecessor : Predecessors) {
    auto Branch = cast<BranchInst>(Predecessor->getTerminator());
    if (Branch->getNumSuccessors() != 1) {
      assert(Branch->getNumSuccessors() == 2);
      auto Succ0 = Branch->getSuccessor(0);
      auto Succ1 = Branch->getSuccessor(1);
      if (Headers.count(Succ0) && !Headers.count(Succ1)) {
        Predicates[Succ0][Predecessor] = BoolTrue;
      } else if (Headers.count(Succ1) && !Headers.count(Succ0)) {
        Predicates[Succ1][Predecessor] = BoolTrue;
      }
    }
    for (auto Header : Headers) {
      if (Predicates[Header].count(Predecessor) == 0) {
        Predicates[Header][Predecessor] = BoolFalse;
      }
    }
  }

  auto PreHeader = BasicBlock::Create(Context, "CycleHeader", F);
  CycleHeaders.push_back(PreHeader);

  assert(Predecessors.size() > 1);

  for (auto Predecessor : Predecessors) {
    auto Branch = cast<BranchInst>(Predecessor->getTerminator());
    if (!Branch->isConditional()) {
      Branch->setSuccessor(0, PreHeader);
      continue;
    }
    auto Succ0 = Branch->getSuccessor(0);
    auto Succ1 = Branch->getSuccessor(1);
    if (Headers.count(Succ0)) {
      if (Headers.count(Succ1)) {
        Branch->eraseFromParent();
        BranchInst::Create(PreHeader, Predecessor);
        continue;
      }
      Branch->setSuccessor(0, PreHeader);
      continue;
    }
    assert(Headers.count(Succ1));
    Branch->setSuccessor(1, PreHeader);
  }

  for (auto Header : Headers) {
    while (!Header->empty() && isa<PHINode>(Header->begin())) {
      auto Phi = cast<PHINode>(Header->begin());
      Phi->moveBefore(*PreHeader, PreHeader->begin());

      for (auto Predecessor : Predecessors) {
        if (-1 == Phi->getBasicBlockIndex(Predecessor)) {
          Phi->addIncoming(UndefValue::get(Phi->getType()), Predecessor);
        }
      }
    }
  }

  BBPredicates Guards;
  for (int i = 0, e = Headers.size() - 1; i != e; ++i) {
    auto Header = Headers[i];
    auto Phi = PHINode::Create(BoolTrue->getType(), Predecessors.size(), "", PreHeader);
    Guards[Header] = Phi;
    auto Preds = Predicates[Header];
    LLVM_DEBUG(dbgs() << "Guard for " << Header->getName() << ": ";
               for (auto P : Preds) {
                 dbgs() << " " << P.first->getName();
               }
               dbgs() << "\n");
    Predicates.erase(Header);
    assert(Preds.size() == Predecessors.size());
    // Don't iterate on Preds because the DenseMap does not create a stable
    // order, which affects the lit tests. Instead, the SetVector on
    // Predecessors provides a stable order.
    for (auto P : Predecessors) {
      assert(Preds.count(P));
      auto Predicate = Preds[P];
      Phi->addIncoming(Predicate, P);
      if (isa<Constant>(Predicate)) {
        continue;
      }
      for (auto &OtherPreds : Predicates) {
        auto &X = OtherPreds.second[P];
        if (isa<Constant>(X)) {
          continue;
        }
        X = BoolTrue;
      }
    }
  }

  auto GuardBlock = PreHeader;
  int i = 0;
  for (int e = Headers.size() - 2; i != e; ++i) {
    auto Header = Headers[i];
    auto Next = BasicBlock::Create(Context, "CycleHeader", F);
    CycleHeaders.push_back(Next);
    BranchInst::Create(Header, Next, Guards[Header], GuardBlock);
    GuardBlock = Next;
  }
  BranchInst::Create(Headers[i], Headers[i+1], Guards[Headers[i]], GuardBlock);
}

static void makeReducible(LoopInfo &LI, BBSetVector &Blocks, BBSetVector &Headers) {
  for (auto H : Headers) {
    assert(Blocks.count(H));
  }

  auto ParentLoop = LI.getLoopFor(Blocks.front());
  auto NewLoop = LI.AllocateLoop();
  if (ParentLoop)
    ParentLoop->addChildLoop(NewLoop);
  else
    LI.addTopLevelLoop(NewLoop);

  SmallVector<BasicBlock *, 8> CycleHeaders;
  squeeze(CycleHeaders, Headers);

  // Create a new loop from the now-transformed cycle
  for (auto H : CycleHeaders) {
    LLVM_DEBUG(dbgs() << "added new block: " << H->getName() << "\n");
    NewLoop->addBasicBlockToLoop(H, LI);
  }

  // FIXME: A child loop whose header is also a header in the current SCC gets
  // destroyed at this point, since its backedges are removed. That's not really
  // necessary; we can just choose to not reconnect such backedges. This
  // needs improvements in the reconnection of PHI nodes in the new header.
  for (auto I : Blocks) {
    if (LI.isLoopHeader(I)) {
      auto Child = LI.getLoopFor(I);
      LLVM_DEBUG(dbgs() << "child loop: " << Child->getHeader()->getName() << "\n");
      for (auto B : Child->blocks()) {
        NewLoop->addBlockEntry(B);
        if (Headers.count(I)) {
          LI.changeLoopFor(I, NewLoop);
          LLVM_DEBUG(dbgs() << "  moved block from child: " << B->getName() << "\n");
        } else {
          LLVM_DEBUG(dbgs() << "  added block from child: " << B->getName() << "\n");
        }
      }

      if (auto Parent = Child->getParentLoop()) {
        Parent->removeChildLoop(Child);
      } else {
        bool Found = false;
        for (auto II = LI.begin(), IE = LI.end(); II != IE; ++II) {
          if (*II == Child) {
            Found = true;
            LI.removeLoop(II);
            break;
          }
        }
        assert(Found);
      }
      if (Headers.count(I)) {
        LI.destroy(Child);
        LLVM_DEBUG(dbgs() << "destroyed child loop\n");
      } else {
        NewLoop->addChildLoop(Child);
        LLVM_DEBUG(dbgs() << "moved child loop\n");
      }
    } else {
      NewLoop->addBlockEntry(I);
      LI.changeLoopFor(I, NewLoop);
      LLVM_DEBUG(dbgs() << "moved block from parent: " << I->getName() << "\n");
    }
  }

  LLVM_DEBUG(dbgs() << "header for new loop: " << NewLoop->getHeader()->getName() << "\n");

  NewLoop->verifyLoop();
  if (ParentLoop) ParentLoop->verifyLoop();
}

static bool makeReducible(LoopInfo &LI, LoopWalker<LoopInfo> &G) {
  bool Changed = false;
  for (auto Scc = scc_begin(G); !Scc.isAtEnd(); ++Scc) {
    if (Scc->size() < 2)
      continue;
    BBSetVector Blocks;
    LLVM_DEBUG(dbgs() << "Found SCC:\n");
    for (auto N : *Scc) {
      LLVM_DEBUG(dbgs() << "  " << N.BB->getName() << "\n");
      Blocks.insert(N.BB);
    }
    BBSetVector Headers;
    for (auto B : Blocks) {
      for (const auto P : predecessors(B)) {
        if (!Blocks.count(P) && G.isIncomingPred(P)) {
          Headers.insert(B);
          break;
        }
      }
    }
    makeReducible(LI, Blocks, Headers);
    Changed = true;
  }
  return Changed;
}

bool EliminateIrreducibilityPass::runOnFunction(Function &F) {
  LLVM_DEBUG(dbgs() << "===== Eliminate irreducibility in function: " << F.getName() << "\n");
  auto &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();

  bool Changed = false;
  SmallVector<Loop*, 8> WorkList;

  LLVM_DEBUG(dbgs() << "visiting top-level\n");
  LoopWalker<LoopInfo> G{&LI, &F.getEntryBlock()};
  Changed |= makeReducible(LI, G);

  for (auto L : LI) {
    WorkList.push_back(L);
  }

  while (!WorkList.empty()) {
    auto L = WorkList.back();
    WorkList.pop_back();
    LLVM_DEBUG(dbgs() << "visiting loop with header " << L->getHeader()->getName() << "\n");
    LoopWalker<LoopInfo> G{&LI, L->getHeader()};
    Changed |= makeReducible(LI, G);
    WorkList.append(L->begin(), L->end());
  }

  // TODO: Update and verify any missing bits related to LoopInfo (dominator
  // tree?). Then we can preserve it.
  return Changed;
}
