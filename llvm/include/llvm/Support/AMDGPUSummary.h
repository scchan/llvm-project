//===- AMDGPUSummary.h - AMDGPU ThinLTO summary data ------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Per-function AMDGPU summary information carried through ThinLTO for
// cross-TU attribute propagation. Stored in the AMDGPU_SUMMARY bitcode
// block, separate from the standard module summary, so that non-AMDGPU
// targets are completely unaffected.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_SUPPORT_AMDGPUSUMMARY_H
#define LLVM_SUPPORT_AMDGPUSUMMARY_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/IR/GlobalValue.h"
#include <algorithm>
#include <cstdint>
#include <limits>

namespace llvm {
namespace AMDGPU {

struct FunctionSummary {
  bool IsKernel = false;

  uint32_t FlatWGSizeMin = 1;
  uint32_t FlatWGSizeMax = 1024;

  uint32_t WavesPerEUMin = 1;
  uint32_t WavesPerEUMax = 10;

  uint32_t MaxNumWGX = std::numeric_limits<uint32_t>::max();
  uint32_t MaxNumWGY = std::numeric_limits<uint32_t>::max();
  uint32_t MaxNumWGZ = std::numeric_limits<uint32_t>::max();

  /// Merge another kernel's attributes into this (device) function's state.
  /// The merged result must be conservative enough to service all callers.
  void mergeFrom(const FunctionSummary &Caller) {
    FlatWGSizeMin = std::max(FlatWGSizeMin, Caller.FlatWGSizeMin);
    FlatWGSizeMax = std::max(FlatWGSizeMax, Caller.FlatWGSizeMax);
    WavesPerEUMin = std::min(WavesPerEUMin, Caller.WavesPerEUMin);
    WavesPerEUMax = std::min(WavesPerEUMax, Caller.WavesPerEUMax);
    MaxNumWGX = std::max(MaxNumWGX, Caller.MaxNumWGX);
    MaxNumWGY = std::max(MaxNumWGY, Caller.MaxNumWGY);
    MaxNumWGZ = std::max(MaxNumWGZ, Caller.MaxNumWGZ);
  }

  bool hasValidWavesPerEU() const { return WavesPerEUMin <= WavesPerEUMax; }
};

using SummaryMap = DenseMap<GlobalValue::GUID, FunctionSummary>;

} // namespace AMDGPU
} // namespace llvm

#endif // LLVM_SUPPORT_AMDGPUSUMMARY_H
