//===--  PromotePointerKernargsToGlobal.cpp - Promote Pointers To Global --===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file declares and defines a pass which uses the double-cast trick (
// flat-to-global and global-to-flat) for pointers that reside in the
// __constant__ address space. For example, given __constant__ int** foo, all
// single dereferences of foo will be promoted to yield a global int*, as
// opposed to a flat int*. It is preferable to execute SelectAcceleratorCode
// before, as this reduces the workload by pruning functions that are not
// reachable by an accelerator. It is mandatory to run InferAddressSpaces after,
// otherwise no benefit shall be obtained (the spurious casts do get removed).
//===----------------------------------------------------------------------===//
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Pass.h"

using namespace llvm;

namespace {
class PromoteConstant : public ModulePass {
  // TODO: query the address spaces robustly.
  static constexpr unsigned int FlatAddrSpace{0u};
  static constexpr unsigned int GlobalAddrSpace{1u};
  static constexpr unsigned int ConstantAddrSpace{4u};

  // TODO: this should be hoisted to a common header with HC utility functions
  //       once the related work on PromotePointerKernArgsToGlobal gets merged
  void createPromotableCast(IRBuilder<>& Builder, Value *From, Value *To) {
    From->replaceAllUsesWith(To);

    Value *FToG = Builder.CreateAddrSpaceCast(
      From,
      cast<PointerType>(
        From->getType())->getElementType()->getPointerTo(GlobalAddrSpace));
    Value *GToF = Builder.CreateAddrSpaceCast(FToG, From->getType());

    To->replaceAllUsesWith(GToF);
  }

  // TODO: this should be hoisted to a common header with HC utility functions
  //       once the related work on PromotePointerKernArgsToGlobal gets merged
  bool maybePromoteUse(IRBuilder<>& Builder, Instruction *UI) {
    if (!UI)
      return false;

    Builder.SetInsertPoint(UI->getNextNonDebugInstruction());

    Value *Tmp = Builder.CreateBitCast(UndefValue::get(UI->getType()),
                                       UI->getType());
    createPromotableCast(Builder, UI, Tmp);

    return true;
  }
public:
  static char ID;
  PromoteConstant() : ModulePass{ID} {}

  bool runOnModule(Module &M) override {
    bool Modified = false;

    for (auto &&F : M.functions()) {
      for (auto &&BB : F) {
        for (auto &&I : BB) {
          if (isa<BitCastInst>(I))
            continue;
          if (isa<AddrSpaceCastInst>(I))
            continue;
          if (isa<CallInst>(I))
            continue;
          if (!I.getType()->isPointerTy())
            continue;
          if (I.getType()->getPointerAddressSpace() != FlatAddrSpace)
            continue;

          if (auto GEPOp = dyn_cast<GEPOperator>(&I))
            if (GEPOp->getPointerAddressSpace() != ConstantAddrSpace)
              continue; // TODO: not handled.
          if (auto GEP = dyn_cast<GetElementPtrInst>(&I))
            if (GEP->getPointerAddressSpace() != ConstantAddrSpace)
              continue;
          if (auto LI = dyn_cast<LoadInst>(&I))
            if (LI->getPointerAddressSpace() != ConstantAddrSpace)
              continue;

          IRBuilder<> Builder(I.getContext());
          if (maybePromoteUse(Builder, &I))
            Modified = true;
        }
      }
    }

    return Modified;
  }
};
char PromoteConstant::ID = 0;

static RegisterPass<PromoteConstant> X{
  "promote-constant",
  "Promotes uses of variables annotated with __constant__ to refer to the "
  "global address space iff the use yields a flat pointer since, by "
  "definition a pointer which is placed in __constant__ storage can only point "
  "to the global address space.",
  false,
  false};
}