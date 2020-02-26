//===- UnifyLoopExits.cpp - Redirect exiting edges to one block -*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
#include "llvm/ADT/SetVector.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Transforms/Utils.h"

#define DEBUG_TYPE "unify-loop-exits"

using namespace llvm;

using BBPredicates = DenseMap<BasicBlock *, Value *>;
using PredMap = DenseMap<BasicBlock *, BBPredicates>;
using BBVector = SmallVector<BasicBlock *, 8>;
using BBSet = SmallPtrSet<BasicBlock *, 8>;
using BBSetVector = SetVector<BasicBlock *, BBVector, BBSet>;
using InstVector = SmallVector<Instruction *, 8>;
using IIMap = DenseMap<Instruction *, InstVector>;

namespace {
struct UnifyLoopExitsPass : public FunctionPass {
  static char ID;
  UnifyLoopExitsPass()
      : FunctionPass(ID) {}

  void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequiredID(LowerSwitchID);
    AU.addRequired<LoopInfoWrapperPass>();
    AU.addRequired<DominatorTreeWrapperPass>();
  }

  bool runOnFunction(Function &F);
};
} // end anonymous namepsace

char UnifyLoopExitsPass::ID = 0;

static RegisterPass<UnifyLoopExitsPass>
X("unify-loop-exits", "Unify loop exits",
  false /* Only looks at CFG */,
  false /* Analysis Pass */);

FunctionPass *llvm::createUnifyLoopExitsPass() {
  return new UnifyLoopExitsPass();
}

static void reconnectMovedPhis(BasicBlock *Successor, BasicBlock *GuardBlock,
                               DenseMap<PHINode*, PHINode*> &MovedPhis) {
  for (auto &RefI : *Successor) {
    auto I = &RefI;
    if (!isa<PHINode>(I)) break;
    auto Phi = cast<PHINode>(I);
    assert(MovedPhis.count(Phi));
    Phi->addIncoming(MovedPhis[Phi], GuardBlock);
  }
}

static void squeeze(const DominatorTree &DT, const Loop *L, const BBSetVector &Predecessors, const BBSetVector &Successors) {
  auto F = Predecessors.front()->getParent();
  auto &Context = F->getContext();
  auto BoolTrue = ConstantInt::getTrue(Context);
  auto BoolFalse = ConstantInt::getFalse(Context);
  PredMap Predicates;

  assert(Successors.size() > 1);
  // Every predecessor has only one successor. So the previous assertion implies
  // the next one.
  assert(Predecessors.size() >= Successors.size());

  for (auto Predecessor : Predecessors) {
    for (auto X : successors(Predecessor)) {
      if (Successors.count(X))
        Predicates[X][Predecessor] = BoolTrue;
    }
  }

  for (auto Predecessor : Predecessors) {
    for (auto Successor : Successors) {
      assert(Predicates.count(Successor));
      if (!Predicates[Successor].count(Predecessor))
        Predicates[Successor][Predecessor] = BoolFalse;
    }
  }

  auto LoopExitBlock = BasicBlock::Create(Context, "LoopExitBlock", F);

  for (auto Predecessor : Predecessors) {
    auto Branch = cast<BranchInst>(Predecessor->getTerminator());
    if (!Branch->isConditional()) {
      Branch->setSuccessor(0, LoopExitBlock);
      continue;
    }
    auto Succ0 = Branch->getSuccessor(0);
    auto Succ1 = Branch->getSuccessor(1);
    if (Successors.count(Succ0)) {
      assert(!Successors.count(Succ1));
      Branch->setSuccessor(0, LoopExitBlock);
      continue;
    }
    assert(Successors.count(Succ1));
    Branch->setSuccessor(1, LoopExitBlock);
  }

  // Restore SSA:
  //
  // The current transform introduces new control flow paths which may break the
  // SSA requirement that every def must dominate all its uses. For example,
  // consider a value D defined inside the loop that is used by some instruction
  // U outside the loop. It follows that D dominates U, since the original
  // program has valid SSA form. After merging the exits, all paths from D to U
  // now flow through the unified exit block. In addition, there may be other
  // paths that do not pass through D, but now reach the unified exit
  // block. Thus, D no longer dominates U.
  //
  // To restore SSA, we first identify the set of all such defs inside the loop.
  IIMap ExternalUsers;
  for (auto BB : L->blocks()) {
    for (auto &I : *BB) {
      for (auto &U : I.uses()) {
        if (auto UI = dyn_cast<Instruction>(U.getUser())) {
          auto UBB = UI->getParent();
          if (L->contains(UBB)) continue;
          LLVM_DEBUG(dbgs() << "added ext use for " << I.getName()
                     << "(" << BB->getName() << ")"
                     << ": " << UI->getName()
                     << "(" << UBB->getName() << ")"
                     << "\n");
          ExternalUsers[&I].push_back(UI);
        }
      }
    }
  }

  for (auto II : ExternalUsers) {
    // For each internal def Inst, we create NewPhi in LoopExitBlock. NewPhi
    // receives Inst only along exiting blocks that dominate the it, while the
    // remaining values are undefined since those paths didn't exist in the
    // original CFG.
    auto Inst = II.first;
    LLVM_DEBUG(dbgs() << "externally used: " << Inst->getName() << "\n");
    auto NewPhi = PHINode::Create(Inst->getType(), Predecessors.size(), Inst->getName() + ".moved", LoopExitBlock);
    for (auto P : Predecessors) {
      LLVM_DEBUG(dbgs() << "predecessor " << P->getName() << ": ");
      if (Inst->getParent() == P || DT.dominates(Inst, P)) {
        LLVM_DEBUG(dbgs() << "dominated\n");
        NewPhi->addIncoming(Inst, P);
      } else {
        LLVM_DEBUG(dbgs() << "not dominated\n");
        NewPhi->addIncoming(UndefValue::get(Inst->getType()), P);
      }
    }

    // NewPhi replaces every use of Inst except where:
    // 1. The user U is a phi in an exit block, and,
    // 2. Inst arrives at U along an exiting block.
    LLVM_DEBUG(dbgs() << "external users:");
    for (auto U : II.second) {
      LLVM_DEBUG(dbgs() << " " << U->getName());
      if (isa<PHINode>(U) && Successors.count(U->getParent())) {
        auto Phi = cast<PHINode>(U);
        for (unsigned int e = Phi->getNumIncomingValues(), i = 0; i != e; ++i) {
          auto V = Phi->getIncomingValue(i);
          auto VBB = Phi->getIncomingBlock(i);
          if (V == Inst && !Predecessors.count(VBB))
            Phi->setIncomingValue(i, NewPhi);
        }
        continue;
      }
      U->replaceUsesOfWith(Inst, NewPhi);
    }
    LLVM_DEBUG(dbgs() << "\n");

    // When all the uses of Inst happen to satisfy the exception above, NewPhi
    // is never used and so we delete it.
    if (NewPhi->use_empty()) {
      NewPhi->eraseFromParent();
    }
  }

  // Phi nodes in the exit blocks are handled specially:
  DenseMap<PHINode*, PHINode*> MovedPhis;
  for (auto Successor : Successors) {
    //  If all the predececessors of an exit block B are exiting blocks, then
    //  all its Phi nodes are moved to LoopExitBlock, where it is padded with
    //  undefined values for all exiting blocks that were not orginally
    //  predecessors of B.
    if (pred_empty(Successor)) {
      LLVM_DEBUG(dbgs() << "Exit block " << Successor->getName() << ": all predecessors inside the loop\n");
      while (!Successor->empty() && isa<PHINode>(Successor->begin())) {
        auto Phi = cast<PHINode>(Successor->begin());
        Phi->moveBefore(*LoopExitBlock, LoopExitBlock->begin());

        for (auto Predecessor : Predecessors) {
          if (-1 == Phi->getBasicBlockIndex(Predecessor)) {
            Phi->addIncoming(UndefValue::get(Phi->getType()), Predecessor);
          }
        }
      }
      continue;
    }

    // In an exit block B where some predecessors are from outside the loop, for
    // every Phi in B, the values coming along exiting blocks are handled
    // separately from other values.
    LLVM_DEBUG(
        dbgs() << "Exit block " << Successor->getName() << ": some predecessors outside the loop:";
        for (auto P: predecessors(Successor)) {
          dbgs() << " " << P->getName();
        }
        dbgs() << "\n";);

    // Since the original CFG edges have been deleted, we recognize exiting
    // blocks by their predicates.
    SmallVector<BasicBlock *, 4> MovedPredecessors;
    SmallVector<BasicBlock *, 4> NotPredecessors;
    auto &Preds = Predicates[Successor];
    for (auto P : Preds) {
      if (P.second != BoolFalse) {
        LLVM_DEBUG(dbgs() << "  Exiting block as predecessor: " << P.first->getName() << "\n");
        MovedPredecessors.push_back(P.first);
      } else {
        LLVM_DEBUG(dbgs() << "  Exiting block not a predecessor: " << P.first->getName() << "\n");
        NotPredecessors.push_back(P.first);
      }
    }

    // For each Phi in B, create NewPhi in LoopExitBlock. Add NewPhi to Phi as
    // the incoming value from LoopExitBlock. Move the values arriving at Phi
    // from exiting blocks to NewPhi and pad NewPhi with undefined values for
    // the remaining exiting blocks.
    for (auto &RefI : *Successor) {
      auto I = &RefI;
      if (!isa<PHINode>(I)) break;
      auto Phi = cast<PHINode>(I);
      auto NewPhi = PHINode::Create(Phi->getType(), MovedPredecessors.size(),
                                    Phi->getName() + ".moved", LoopExitBlock);
      MovedPhis[Phi] = NewPhi;
      for (auto P : MovedPredecessors) {
        auto V = Phi->removeIncomingValue(P, false);
        NewPhi->addIncoming(V, P);
      }
      assert(Phi->getNumIncomingValues() != 0);
      for (auto P : NotPredecessors) {
        NewPhi->addIncoming(UndefValue::get(Phi->getType()), P);
      }
      assert(NewPhi->getNumIncomingValues() == Preds.size());
    }
  }

  // In the newly created UnifiedExit, create one guard predicate for each
  // successor that decides whether control should flow to that successor. The
  // UnifiedExit block becomes the first in a chain of guard blocks, one for
  // each successor. Each guard block uses the guard predicate to either
  // transfer control out of the chain to the corresponding successor, or
  // forward control to the next guard block.
  //
  // Note that the predicate for the last successor is trivially true, and so we
  // process only the first N-1 successors.
  BBPredicates Guards;
  for (int i = 0, e = Successors.size() - 1; i != e; ++i) {
    auto Successor = Successors[i];
    LLVM_DEBUG(dbgs() << "Creating guard for " << Successor->getName() << "\n");
    auto Phi = PHINode::Create(BoolTrue->getType(), Predecessors.size(),
                               StringRef("LoopExitGuard.") + Successor->getName(), LoopExitBlock);
    Guards[Successor] = Phi;

    // Connect the incoming guard values for the current successor.
    auto &Preds = Predicates[Successor];
    for (auto P : predecessors(Successor)) {
      if (Preds.count(P)) {
        assert(Preds[P] != BoolFalse);
      }
    }

    assert(Preds.size() == Predecessors.size());
    // Don't iterate on Preds because the DenseMap does not create a stable
    // order, which affects the lit tests. Instead, the SetVector on
    // Predecessors provides a stable order.
    for (auto P : Predecessors) {
      assert(Preds.count(P));
      auto Predicate = Preds[P];
      Phi->addIncoming(Predicate, P);
    }
  }

  // Assert validity of predicates on the last successor since the previous loop
  // did not visit it.
  auto Last = Successors.back();
  assert(Predicates.count(Last));
  auto &Preds = Predicates[Last];
  for (auto P : predecessors(Last)) {
    if (Preds.count(P)) {
      assert(Preds[P] != BoolFalse);
    }
  }

  auto GuardBlock = LoopExitBlock;

  int NumSuccs = Successors.size();
  for (int i = 0; i != NumSuccs - 2; ++i) {
    auto Successor = Successors[i];
    auto Next = BasicBlock::Create(Context, "LoopExitBlock", F);
    assert(Guards.count(Successor));
    BranchInst::Create(Successor, Next, Guards[Successor], GuardBlock);
    reconnectMovedPhis(Successor, GuardBlock, MovedPhis);
    GuardBlock = Next;
  }

  BranchInst::Create(Successors[NumSuccs - 2],
                     Successors[NumSuccs - 1],
                     Guards[Successors[NumSuccs - 2]], GuardBlock);
  reconnectMovedPhis(Successors[NumSuccs - 2], GuardBlock, MovedPhis);
  reconnectMovedPhis(Successors[NumSuccs - 1], GuardBlock, MovedPhis);
}

static bool unifyLoopExits(const DominatorTree &DT, const LoopInfo &LI, Loop *L) {
  BBVector ExitingBlocks;
  L->getExitingBlocks(ExitingBlocks);

  BBSetVector Predecessors;
  BBSetVector Successors;
  for (auto P : ExitingBlocks) {
    Predecessors.insert(P);
    for (auto S : successors(P)) {
      auto SL = LI.getLoopFor(S);
      if (SL == L || L->contains(SL)) continue;
      Successors.insert(S);
    }
  }

  LLVM_DEBUG(
      dbgs() << "Found exit blocks:";
      for (auto H : Successors) {
        dbgs() << " " << H->getName() << "";
      }
      dbgs() << "\n";

      dbgs() << "Found exiting blocks:";
      for (auto P : Predecessors) {
        dbgs() << " " << P->getName();
      }
      dbgs() << "\n";);

  if (Successors.size() < 2) {
    LLVM_DEBUG(dbgs() << "Loop has a single exit block; nothing to do.\n");
    return false;
  }

  squeeze(DT, L, Predecessors, Successors);
  return true;
}

bool UnifyLoopExitsPass::runOnFunction(Function &F) {
  LLVM_DEBUG(dbgs() << "===== Unifying loop exits in function " << F.getName() << "\n");
  auto &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
  auto &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();

  bool Changed = false;
  auto Loops = LI.getLoopsInPreorder();
  for (auto L : Loops) {
    //    if (!L->getParentLoop()) continue;
    if (L->getExitingBlock()) continue;
    LLVM_DEBUG(dbgs() << "Loop: " << L->getHeader()->getName()
               << " (depth: " << LI.getLoopDepth(L->getHeader()) << ")\n");
    Changed |= unifyLoopExits(DT, LI, L);
  }
  return Changed;
}
