//===- AMDGPUObjectLinking.cpp - AMDGPU link-time resolution --------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Implements link-time resolution passes for AMDGPU object linking:
//
// LDS (Local Data Share) resolution:
//   1. Collects all SHN_AMDGPU_LDS symbols (deduplicated across TUs)
//   2. Parses .amdgpu.callgraph sections to build the cross-TU call graph
//   3. Computes transitive LDS reachability per kernel via BFS
//   4. Groups kernels with disjoint LDS usage into independent groups
//   5. Assigns per-group offsets with a two-tier layout (shared then kernel)
//
// Resource usage propagation:
//   1. Parses .amdgpu.resource_usage sections for per-function local usage
//   2. Propagates resource usage across the cross-TU call graph (MAX for
//      registers, OR for flags, SUM for scratch)
//
// After resolution, the linker binary-patches each kernel descriptor in
// .rodata with the propagated values (LDS size, VGPR/SGPR blocks, scratch
// size, etc.) and updates HSA metadata in the .note section.
//
//===----------------------------------------------------------------------===//

#include "AMDGPUObjectLinking.h"
#include "Config.h"
#include "InputFiles.h"
#include "InputSection.h"
#include "SymbolTable.h"
#include "Symbols.h"
#include "lld/Common/ErrorHandler.h"
#include "llvm/ADT/EquivalenceClasses.h"
#include "llvm/BinaryFormat/AMDGPUMetadataVerifier.h"
#include "llvm/BinaryFormat/ELF.h"
#include "llvm/BinaryFormat/MsgPackDocument.h"
#include "llvm/MC/MCSubtargetInfo.h"
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Support/AMDGPUResourceUsage.h"
#include "llvm/Support/AMDHSAKernelDescriptor.h"
#include "llvm/Support/Alignment.h"
#include "llvm/Support/Allocator.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/Endian.h"
#include "llvm/Support/TimeProfiler.h"
#include "llvm/TargetParser/Triple.h"

#define DEBUG_TYPE "amdgpu-object-linking"

using namespace llvm;
using namespace llvm::support::endian;
using namespace llvm::object;
using namespace llvm::ELF;
using namespace lld;
using namespace lld::elf;

namespace {

struct LDSSymbolInfo {
  Symbol *sym;
  uint64_t size;
  Align alignment;
  uint64_t assignedOffset = 0;
};

struct NamedBarrierInfo {
  Symbol *sym;
  uint32_t slotCount;
  uint32_t assignedBarId = 0;
};

struct FunctionResourceInfo {
  uint32_t numArchVGPR = 0;
  uint32_t numAccVGPR = 0;
  uint32_t numSGPR = 0;
  uint32_t numNamedBarrier = 0;
  uint32_t privateSegmentSize = 0;
  bool usesVCC = false;
  bool usesFlatScratch = false;
  bool hasDynSizedStack = false;
  uint32_t occupancyLDSLimit = 0;
};

struct PropagatedResourceInfo {
  uint32_t numArchVGPR = 0;
  uint32_t numAccVGPR = 0;
  uint32_t numSGPR = 0;
  uint32_t numNamedBarrier = 0;
  uint32_t totalScratchSize = 0;
  bool usesVCC = false;
  bool usesFlatScratch = false;
  bool hasDynSizedStack = false;
  bool hasIncompleteRes = false;
};

struct ResourceUsageHeader {
  uint32_t version = 0;
  uint32_t entrySize = 0;
  uint32_t vgprEncodingGranule = 0;
  uint32_t sgprEncodingGranule = 0;
  uint32_t flags = 0;
  // bit 0: hasAccumOffset (GFX90A)
  // bit 1: sgprBlocksAlwaysZero (GFX10+)

  bool operator==(const ResourceUsageHeader &rhs) const {
    return version == rhs.version && entrySize == rhs.entrySize &&
           vgprEncodingGranule == rhs.vgprEncodingGranule &&
           sgprEncodingGranule == rhs.sgprEncodingGranule && flags == rhs.flags;
  }
  bool operator!=(const ResourceUsageHeader &rhs) const {
    return !(*this == rhs);
  }
};

struct CGNode {
  Symbol *sym;
  bool isKernel = false;

  SmallVector<CGNode *, 4> callees;
  SmallVector<size_t, 2> ldsUseIndices;
  SmallVector<size_t, 2> barrierUseIndices;

  FunctionResourceInfo localRes;
  bool hasLocalRes = false;

  DenseSet<size_t> reachableLDS;
  DenseSet<size_t> reachableBarriers;
  uint64_t ldsSize = 0;

  uint32_t occupancyLDSLimit = 0;

  uint32_t numNamedBarrier = 0;

  PropagatedResourceInfo propagatedRes;
  bool hasPropagatedRes = false;
};

struct PrototypeInfo {
  SmallVector<CGNode *, 4> functions;
  SmallVector<CGNode *, 4> indirectCallers;
};

class AMDGPUCallGraph {
  SpecificBumpPtrAllocator<CGNode> alloc;
  DenseMap<Symbol *, CGNode *> symToNode;
  SmallVector<CGNode *> kernelNodes;
  bool hasLDSUseEntries = false;
  bool hasBarrierUseEntries = false;

  DenseSet<CGNode *> addressTakenNodes;
  DenseSet<Symbol *> namedBarrierSyms;
  StringMap<PrototypeInfo> prototypeMap;

public:
  CGNode &getOrCreate(Symbol *sym) {
    auto [it, inserted] = symToNode.try_emplace(sym, nullptr);
    if (inserted) {
      it->second = new (alloc.Allocate()) CGNode();
      it->second->sym = sym;
    }
    return *it->second;
  }

  CGNode *lookup(Symbol *sym) const {
    auto it = symToNode.find(sym);
    return it != symToNode.end() ? it->second : nullptr;
  }

  void addKernel(CGNode &node) {
    node.isKernel = true;
    kernelNodes.push_back(&node);
  }

  void markAddressTaken(CGNode *node) { addressTakenNodes.insert(node); }

  void addIndirectCall(CGNode *caller, StringRef encoding) {
    prototypeMap[encoding].indirectCallers.push_back(caller);
  }

  void addPrototype(CGNode *node, StringRef encoding) {
    prototypeMap[encoding].functions.push_back(node);
  }

  // After all sections are parsed, resolve indirect call edges by matching
  // prototype encodings: for each indirect call encoding, the potential callees
  // are address-taken functions with the same encoding.
  void buildIndirectEdges() {
    for (auto &[encoding, info] : prototypeMap) {
      if (info.indirectCallers.empty())
        continue;

      SmallVector<CGNode *, 4> potentialCallees;
      for (CGNode *func : info.functions) {
        if (addressTakenNodes.count(func))
          potentialCallees.push_back(func);
      }

      if (potentialCallees.empty())
        continue;

      for (CGNode *caller : info.indirectCallers) {
        for (CGNode *callee : potentialCallees) {
          LLVM_DEBUG(dbgs() << "  indirect edge: " << caller->sym->getName()
                            << " -> " << callee->sym->getName()
                            << " (proto=" << encoding << ")\n");
          caller->callees.push_back(callee);
        }
      }
    }
  }

  void setHasLDSUses() { hasLDSUseEntries = true; }
  bool hasLDSUses() const { return hasLDSUseEntries; }

  void markNamedBarrier(Symbol *sym) { namedBarrierSyms.insert(sym); }
  bool isNamedBarrier(Symbol *sym) const { return namedBarrierSyms.count(sym); }
  void setHasBarrierUses() { hasBarrierUseEntries = true; }
  bool hasBarrierUses() const { return hasBarrierUseEntries; }

  ArrayRef<CGNode *> kernels() const { return kernelNodes; }

  using const_iterator = DenseMap<Symbol *, CGNode *>::const_iterator;
  const_iterator begin() const { return symToNode.begin(); }
  const_iterator end() const { return symToNode.end(); }
};

} // namespace

//===----------------------------------------------------------------------===//
// LDS symbol collection
//===----------------------------------------------------------------------===//

static void collectLDSSymbols(Ctx &ctx,
                              SmallVectorImpl<LDSSymbolInfo> &ldsSymbols) {
  DenseSet<Symbol *> seen;
  for (ELFFileBase *file : ctx.objectFiles) {
    if (!file->hasCommonSyms)
      continue;
    for (Symbol *sym : file->getGlobalSymbols()) {
      if (!sym->isAMDGPULDS)
        continue;
      auto *cs = dyn_cast<CommonSymbol>(sym);
      if (!cs)
        continue;
      if (!seen.insert(sym).second)
        continue;
      LLVM_DEBUG(dbgs() << "  collected LDS symbol: " << sym->getName()
                        << " size=" << cs->size << " align=" << cs->alignment
                        << "\n");
      ldsSymbols.push_back(
          {sym, cs->size, Align(cs->alignment), /*assignedOffset=*/0});
    }
  }
}

static bool compareLDSSymbol(const LDSSymbolInfo &a, const LDSSymbolInfo &b) {
  if (a.alignment != b.alignment)
    return a.alignment > b.alignment;
  if (a.size != b.size)
    return a.size > b.size;
  return a.sym->getName() < b.sym->getName();
}

static void assignUniversalOffsets(SmallVectorImpl<LDSSymbolInfo> &ldsSymbols) {
  llvm::sort(ldsSymbols, compareLDSSymbol);
  uint64_t currentOffset = 0;
  for (LDSSymbolInfo &lds : ldsSymbols) {
    currentOffset = alignTo(currentOffset, lds.alignment);
    lds.assignedOffset = currentOffset;
    currentOffset += lds.size;
  }
}

//===----------------------------------------------------------------------===//
// Section parsing
//===----------------------------------------------------------------------===//

// Parse the .amdgpu.callgraph section from an object file into the call graph.
// The section contains pairs of 8-byte symbol references encoded via
// relocations.
//   - Kernel entry:  (kernel_sym, kernel_sym) -- self-referencing pair
//   - Direct call:   (caller_sym, callee_sym)
//   - LDS-use entry: (func_sym, lds_sym) where lds_sym is SHN_AMDGPU_LDS
template <class ELFT>
static void
parseCallGraphSection(Ctx &ctx, ObjFile<ELFT> *obj, AMDGPUCallGraph &cg,
                      const DenseMap<Symbol *, size_t> &ldsSymToIndex) {
  if (obj->amdgpuCallGraphSectionIndex == 0)
    return;

  ArrayRef<typename ELFT::Shdr> objSections = obj->template getELFShdrs<ELFT>();
  const ELFFile<ELFT> &elfObj = obj->getObj();

  SmallVector<uint32_t, 32> symbolIndices;
  for (size_t i = 0, e = objSections.size(); i < e; ++i) {
    const Elf_Shdr_Impl<ELFT> &sec = objSections[i];
    if (sec.sh_info != obj->amdgpuCallGraphSectionIndex)
      continue;

    if (sec.sh_type == SHT_RELA) {
      ArrayRef<typename ELFT::Rela> relas =
          CHECK(elfObj.relas(sec),
                "could not retrieve .amdgpu.callgraph rela section");
      for (const auto &rel : relas)
        symbolIndices.push_back(rel.getSymbol(false));
      break;
    }
    if (sec.sh_type == SHT_REL) {
      ArrayRef<typename ELFT::Rel> rels = CHECK(
          elfObj.rels(sec), "could not retrieve .amdgpu.callgraph rel section");
      for (const auto &rel : rels)
        symbolIndices.push_back(rel.getSymbol(false));
      break;
    }
    if (sec.sh_type == SHT_CREL) {
      auto crels = CHECK(elfObj.crels(sec),
                         "could not retrieve .amdgpu.callgraph crel section");
      for (const auto &rel : crels.first)
        symbolIndices.push_back(rel.getSymbol(false));
      for (const auto &rel : crels.second)
        symbolIndices.push_back(rel.getSymbol(false));
      break;
    }
  }

  LLVM_DEBUG(dbgs() << "  found " << symbolIndices.size()
                    << " relocation entries in .amdgpu.callgraph\n");

  if (symbolIndices.empty())
    return;

  if (symbolIndices.size() % 2 != 0) {
    Err(ctx) << obj
             << ": .amdgpu.callgraph has odd number of relocation entries";
    return;
  }

  for (size_t i = 0, e = symbolIndices.size(); i < e; i += 2) {
    uint32_t idx1 = symbolIndices[i];
    uint32_t idx2 = symbolIndices[i + 1];
    Symbol &sym1 = obj->getSymbol(idx1);

    if (idx1 == idx2) {
      if (sym1.getName().empty())
        continue;
      LLVM_DEBUG(dbgs() << "  kernel: " << sym1.getName() << "\n");
      cg.addKernel(cg.getOrCreate(&sym1));
    } else {
      Symbol &sym2 = obj->getSymbol(idx2);
      if (sym1.getName().empty() || sym2.getName().empty())
        continue;
      if (sym2.isAMDGPULDS) {
        auto it = ldsSymToIndex.find(&sym2);
        if (it != ldsSymToIndex.end()) {
          LLVM_DEBUG(dbgs() << "  lds-use: " << sym1.getName() << " -> "
                            << sym2.getName() << "\n");
          cg.getOrCreate(&sym1).ldsUseIndices.push_back(it->second);
          cg.setHasLDSUses();
        }
      } else if (sym2.getName() == "__amdgpu_address_taken") {
        LLVM_DEBUG(dbgs() << "  address-taken: " << sym1.getName() << "\n");
        cg.markAddressTaken(&cg.getOrCreate(&sym1));
      } else if (sym2.getName().starts_with("__amdgpu_icall.")) {
        StringRef enc = sym2.getName().drop_front(strlen("__amdgpu_icall."));
        LLVM_DEBUG(dbgs() << "  indirect-call: " << sym1.getName()
                          << " enc=" << enc << "\n");
        cg.addIndirectCall(&cg.getOrCreate(&sym1), enc);
      } else if (sym2.getName().starts_with("__amdgpu_proto.")) {
        StringRef enc = sym2.getName().drop_front(strlen("__amdgpu_proto."));
        LLVM_DEBUG(dbgs() << "  prototype: " << sym1.getName() << " enc=" << enc
                          << "\n");
        cg.addPrototype(&cg.getOrCreate(&sym1), enc);
      } else if (sym2.getName() == "__amdgpu_named_barrier") {
        LLVM_DEBUG(dbgs() << "  named-barrier: " << sym1.getName() << "\n");
        cg.markNamedBarrier(&sym1);
      } else {
        LLVM_DEBUG(dbgs() << "  call: " << sym1.getName() << " -> "
                          << sym2.getName() << "\n");
        CGNode &caller = cg.getOrCreate(&sym1);
        CGNode &callee = cg.getOrCreate(&sym2);
        caller.callees.push_back(&callee);
      }
    }
  }
}

// Parse the .amdgpu.resource_usage section and attach info to graph nodes.
template <class ELFT>
static bool parseResourceUsageSection(Ctx &ctx, ObjFile<ELFT> *obj,
                                      AMDGPUCallGraph &cg,
                                      ResourceUsageHeader &header) {
  if (obj->amdgpuResourceUsageSectionIndex == 0)
    return false;

  ArrayRef<typename ELFT::Shdr> objSections = obj->template getELFShdrs<ELFT>();
  const ELFFile<ELFT> &elfObj = obj->getObj();
  const typename ELFT::Shdr &sec =
      objSections[obj->amdgpuResourceUsageSectionIndex];

  ArrayRef<uint8_t> data =
      CHECK(elfObj.getSectionContents(sec),
            "could not read .amdgpu.resource_usage section");

  constexpr size_t headerSize = 24;
  if (data.size() < headerSize) {
    Err(ctx) << obj << ": .amdgpu.resource_usage section too small for header";
    return false;
  }

  header.version = read32le(data.data());
  header.entrySize = read32le(data.data() + 4);
  header.vgprEncodingGranule = read32le(data.data() + 8);
  header.sgprEncodingGranule = read32le(data.data() + 12);
  header.flags = read32le(data.data() + 16);

  if (header.version != 1) {
    Err(ctx) << obj << ": unsupported .amdgpu.resource_usage version: "
             << header.version;
    return false;
  }

  SmallVector<uint32_t, 32> symbolIndices;
  for (size_t i = 0, e = objSections.size(); i < e; ++i) {
    const auto &relSec = objSections[i];
    if (relSec.sh_info != obj->amdgpuResourceUsageSectionIndex)
      continue;
    if (relSec.sh_type == SHT_RELA) {
      ArrayRef<typename ELFT::Rela> relas =
          CHECK(elfObj.relas(relSec),
                "could not read .amdgpu.resource_usage rela section");
      for (const auto &rel : relas)
        symbolIndices.push_back(rel.getSymbol(false));
      break;
    }
    if (relSec.sh_type == SHT_REL) {
      ArrayRef<typename ELFT::Rel> rels =
          CHECK(elfObj.rels(relSec),
                "could not read .amdgpu.resource_usage rel section");
      for (const auto &rel : rels)
        symbolIndices.push_back(rel.getSymbol(false));
      break;
    }
    if (relSec.sh_type == SHT_CREL) {
      auto crels = CHECK(elfObj.crels(relSec),
                         "could not read .amdgpu.resource_usage crel section");
      for (const auto &rel : crels.first)
        symbolIndices.push_back(rel.getSymbol(false));
      for (const auto &rel : crels.second)
        symbolIndices.push_back(rel.getSymbol(false));
      break;
    }
  }

  size_t dataAfterHeader = data.size() - headerSize;
  size_t numEntries =
      header.entrySize > 0 ? dataAfterHeader / header.entrySize : 0;
  if (symbolIndices.size() != numEntries) {
    Err(ctx) << obj
             << ": .amdgpu.resource_usage entry/relocation count mismatch: "
             << numEntries << " entries vs " << symbolIndices.size()
             << " relocations";
    return false;
  }

  for (size_t i = 0; i < numEntries; ++i) {
    size_t entryOff = headerSize + i * header.entrySize;
    const uint8_t *p = data.data() + entryOff + 8;
    FunctionResourceInfo info;
    info.numArchVGPR = read32le(p);
    info.numAccVGPR = read32le(p + 4);
    info.numSGPR = read32le(p + 8);
    info.numNamedBarrier = read32le(p + 12);
    info.privateSegmentSize = read32le(p + 16);
    uint32_t flags = read32le(p + 20);
    info.usesVCC = flags & 0x1;
    info.usesFlatScratch = (flags >> 1) & 0x1;
    info.hasDynSizedStack = (flags >> 2) & 0x1;

    if (header.entrySize >= 36)
      info.occupancyLDSLimit = read32le(p + 24);

    Symbol &sym = obj->getSymbol(symbolIndices[i]);
    if (sym.getName().empty())
      continue;

    LLVM_DEBUG(dbgs() << "  resource: " << sym.getName()
                      << " vgpr=" << info.numArchVGPR
                      << " agpr=" << info.numAccVGPR << " sgpr=" << info.numSGPR
                      << " scratch=" << info.privateSegmentSize << " vcc="
                      << info.usesVCC << " flat=" << info.usesFlatScratch
                      << " dynstack=" << info.hasDynSizedStack << "\n");
    CGNode &node = cg.getOrCreate(&sym);
    node.localRes = info;
    node.hasLocalRes = true;
    if (node.isKernel)
      node.occupancyLDSLimit = info.occupancyLDSLimit;
  }

  return true;
}

//===----------------------------------------------------------------------===//
// LDS resolution
//===----------------------------------------------------------------------===//

// Single BFS from each kernel collecting all transitive reachability info:
// LDS variable indices and named barrier indices.
static void computeKernelReachability(AMDGPUCallGraph &cg) {
  for (CGNode *kernel : cg.kernels()) {
    SmallVector<CGNode *, 16> worklist;
    DenseSet<CGNode *> visited;
    worklist.push_back(kernel);
    visited.insert(kernel);

    while (!worklist.empty()) {
      CGNode *node = worklist.pop_back_val();
      for (CGNode *callee : node->callees) {
        if (visited.insert(callee).second)
          worklist.push_back(callee);
      }
    }

    for (CGNode *node : visited) {
      for (size_t idx : node->ldsUseIndices)
        kernel->reachableLDS.insert(idx);
      for (size_t idx : node->barrierUseIndices)
        kernel->reachableBarriers.insert(idx);
    }
  }
}

// Reorder shared-tier LDS indices to minimize total wasted LDS across kernels.
//
// Each kernel's hardware LDS allocation spans from offset 0 to the end of its
// last-used variable. Variables placed before a kernel's last-used variable but
// not used by that kernel are wasted. A naive sort by size/alignment ignores
// the kernel-variable usage graph.
//
// This greedy builds the ordering from the tail: at each step it places the
// variable used by the fewest "active" kernels (those whose span is not yet
// determined) at the current highest position. When a variable is placed,
// every active kernel using it has its span fixed and exits the active set.
//
// Effect: variables shared by many kernels settle at low offsets (every kernel
// allocates that prefix anyway), while variables used by few kernels sit at
// high offsets where only those kernels pay the cost.
static void orderSharedTierByUsage(SmallVectorImpl<size_t> &sharedTier,
                                   ArrayRef<LDSSymbolInfo> ldsSymbols,
                                   ArrayRef<CGNode *> groupKernels) {
  size_t n = sharedTier.size();
  if (n <= 1)
    return;

  llvm::sort(sharedTier);
  DenseSet<size_t> sharedSet(sharedTier.begin(), sharedTier.end());

  DenseMap<size_t, SmallVector<CGNode *, 4>> varToKernels;
  for (CGNode *k : groupKernels)
    for (size_t idx : k->reachableLDS)
      if (sharedSet.count(idx))
        varToKernels[idx].push_back(k);

  DenseSet<CGNode *> activeKernels;
  for (CGNode *k : groupKernels)
    activeKernels.insert(k);

  DenseMap<size_t, unsigned> useCount;
  for (size_t idx : sharedTier) {
    auto it = varToKernels.find(idx);
    useCount[idx] = it != varToKernels.end() ? it->second.size() : 0;
  }

  DenseSet<size_t> remaining(sharedTier.begin(), sharedTier.end());
  SmallVector<size_t> ordered(n);

  for (size_t pos = n; pos > 0; --pos) {
    size_t best = 0;
    bool found = false;
    for (size_t idx : sharedTier) {
      if (!remaining.count(idx))
        continue;
      if (!found) {
        best = idx;
        found = true;
        continue;
      }
      unsigned uc = useCount[idx], bestUc = useCount[best];
      if (uc < bestUc) {
        best = idx;
      } else if (uc == bestUc) {
        uint64_t sz = ldsSymbols[idx].size, bestSz = ldsSymbols[best].size;
        if (sz > bestSz)
          best = idx;
        else if (sz == bestSz &&
                 compareLDSSymbol(ldsSymbols[best], ldsSymbols[idx]))
          best = idx;
      }
    }

    ordered[pos - 1] = best;
    remaining.erase(best);

    auto it = varToKernels.find(best);
    if (it != varToKernels.end()) {
      for (CGNode *k : it->second) {
        if (!activeKernels.erase(k))
          continue;
        for (size_t w : k->reachableLDS)
          if (remaining.count(w))
            --useCount[w];
      }
    }
  }

  sharedTier = std::move(ordered);
}

// Assign offsets using grouped allocation. Kernels with disjoint LDS usage
// form independent groups, each allocated from offset 0. Within each group,
// shared-tier LDS (global-scope and callee-scope) is placed first, and
// kernel-tier LDS (owned by a single kernel) is placed last.
static void assignGroupedOffsets(
    SmallVectorImpl<LDSSymbolInfo> &ldsSymbols, AMDGPUCallGraph &cg,
    const DenseMap<size_t, SmallVector<CGNode *, 2>> &ldsToUsers) {
  if (!cg.hasLDSUses()) {
    assignUniversalOffsets(ldsSymbols);
    return;
  }

  auto isKernelTier = [&](size_t ldsIdx) {
    auto it = ldsToUsers.find(ldsIdx);
    if (it == ldsToUsers.end())
      return false;
    return it->second.size() == 1 && it->second[0]->isKernel;
  };

  // Group kernels via union-find: kernels sharing any reachable LDS symbol
  // are merged into the same group.
  EquivalenceClasses<CGNode *> groups;
  for (CGNode *k : cg.kernels())
    groups.insert(k);

  for (size_t ldsIdx = 0, e = ldsSymbols.size(); ldsIdx < e; ++ldsIdx) {
    SmallVector<CGNode *, 4> reachingKernels;
    for (CGNode *k : cg.kernels()) {
      if (k->reachableLDS.count(ldsIdx))
        reachingKernels.push_back(k);
    }
    for (size_t i = 1; i < reachingKernels.size(); ++i)
      groups.unionSets(reachingKernels[0], reachingKernels[i]);
  }

  auto idxCmp = [&](size_t a, size_t b) {
    return compareLDSSymbol(ldsSymbols[a], ldsSymbols[b]);
  };

  DenseSet<size_t> assigned;
  [[maybe_unused]] unsigned groupIdx = 0;

  for (auto it = groups.begin(), e = groups.end(); it != e; ++it) {
    if (!(*it)->isLeader())
      continue;

    DenseSet<size_t> groupLDS;
    SmallVector<CGNode *, 4> groupKernels;
    LLVM_DEBUG(dbgs() << "  group " << groupIdx << " kernels:");
    for (auto mi = groups.member_begin(**it); mi != groups.member_end(); ++mi) {
      LLVM_DEBUG(dbgs() << " " << (*mi)->sym->getName());
      groupKernels.push_back(*mi);
      groupLDS.insert((*mi)->reachableLDS.begin(), (*mi)->reachableLDS.end());
    }
    LLVM_DEBUG(dbgs() << "\n");
    ++groupIdx;

    SmallVector<size_t> sharedTier, kernelTierVec;
    for (size_t idx : groupLDS) {
      if (isKernelTier(idx))
        kernelTierVec.push_back(idx);
      else
        sharedTier.push_back(idx);
    }

    orderSharedTierByUsage(sharedTier, ldsSymbols, groupKernels);
    llvm::sort(kernelTierVec, idxCmp);

    LLVM_DEBUG({
      dbgs() << "    shared-tier (" << sharedTier.size() << "):";
      for (size_t idx : sharedTier)
        dbgs() << " " << ldsSymbols[idx].sym->getName();
      dbgs() << "\n    kernel-tier (" << kernelTierVec.size() << "):";
      for (size_t idx : kernelTierVec)
        dbgs() << " " << ldsSymbols[idx].sym->getName();
      dbgs() << "\n";
    });

    uint64_t offset = 0;
    for (size_t idx : sharedTier) {
      offset = alignTo(offset, ldsSymbols[idx].alignment);
      ldsSymbols[idx].assignedOffset = offset;
      offset += ldsSymbols[idx].size;
      assigned.insert(idx);
    }
    for (size_t idx : kernelTierVec) {
      offset = alignTo(offset, ldsSymbols[idx].alignment);
      ldsSymbols[idx].assignedOffset = offset;
      offset += ldsSymbols[idx].size;
      assigned.insert(idx);
    }
  }

  SmallVector<size_t> unclaimed;
  for (size_t i = 0, e = ldsSymbols.size(); i < e; ++i)
    if (!assigned.count(i))
      unclaimed.push_back(i);
  if (!unclaimed.empty()) {
    llvm::sort(unclaimed, idxCmp);
    uint64_t offset = 0;
    for (size_t idx : unclaimed) {
      offset = alignTo(offset, ldsSymbols[idx].alignment);
      ldsSymbols[idx].assignedOffset = offset;
      offset += ldsSymbols[idx].size;
    }
  }
}

static void computeKernelLDSSizes(ArrayRef<LDSSymbolInfo> ldsSymbols,
                                  AMDGPUCallGraph &cg) {
  if (!cg.hasLDSUses()) {
    uint64_t totalSize = 0;
    for (const auto &lds : ldsSymbols)
      totalSize = std::max(totalSize, lds.assignedOffset + lds.size);
    for (CGNode *kernel : cg.kernels())
      kernel->ldsSize = totalSize;
    return;
  }

  for (CGNode *kernel : cg.kernels()) {
    uint64_t maxEnd = 0;
    for (size_t idx : kernel->reachableLDS)
      maxEnd = std::max(maxEnd,
                        ldsSymbols[idx].assignedOffset + ldsSymbols[idx].size);
    kernel->ldsSize = maxEnd;
  }
}

static void
resolveLDS(Ctx &ctx, SmallVectorImpl<LDSSymbolInfo> &ldsSymbols,
           AMDGPUCallGraph &cg,
           const DenseMap<size_t, SmallVector<CGNode *, 2>> &ldsToUsers) {
  LLVM_DEBUG(dbgs() << "AMDGPU LDS: assigning grouped offsets\n");
  assignGroupedOffsets(ldsSymbols, cg, ldsToUsers);
  computeKernelLDSSizes(ldsSymbols, cg);

  // Symbol::overwrite preserves the old symbol's visibility, so for shared-
  // object links (AMDGPU code objects use -shared) we must explicitly force
  // STV_HIDDEN to prevent the symbol from being preemptible, which would cause
  // R_AMDGPU_ABS32_LO relocations to be rejected by the relocation scanner.
  LLVM_DEBUG(dbgs() << "AMDGPU LDS: final symbol assignments:\n");
  for (const LDSSymbolInfo &lds : ldsSymbols) {
    LLVM_DEBUG(dbgs() << "  " << lds.sym->getName() << " -> offset="
                      << lds.assignedOffset << " size=" << lds.size << "\n");
    Defined(ctx, ctx.internalFile, lds.sym->getName(), STB_GLOBAL, STV_HIDDEN,
            STT_NOTYPE, lds.assignedOffset, lds.size, nullptr)
        .overwrite(*lds.sym);
    if (ctx.arg.shared)
      lds.sym->stOther = (lds.sym->stOther & ~3) | STV_HIDDEN;
  }

  LLVM_DEBUG({
    dbgs() << "AMDGPU LDS: per-kernel LDS sizes:\n";
    for (CGNode *kernel : cg.kernels())
      dbgs() << "  " << kernel->sym->getName() << " -> " << kernel->ldsSize
             << " bytes\n";
  });
}

//===----------------------------------------------------------------------===//
// Named barrier resolution
//===----------------------------------------------------------------------===//

static void resolveNamedBarriers(
    Ctx &ctx, SmallVectorImpl<NamedBarrierInfo> &barriers, AMDGPUCallGraph &cg,
    const DenseMap<size_t, SmallVector<CGNode *, 2>> &barToUsers) {
  auto isKernelTier = [&](size_t barIdx) {
    auto it = barToUsers.find(barIdx);
    if (it == barToUsers.end())
      return false;
    return it->second.size() == 1 && it->second[0]->isKernel;
  };

  EquivalenceClasses<CGNode *> groups;
  for (CGNode *k : cg.kernels())
    groups.insert(k);

  for (size_t barIdx = 0, e = barriers.size(); barIdx < e; ++barIdx) {
    SmallVector<CGNode *, 4> reachingKernels;
    for (CGNode *k : cg.kernels()) {
      if (k->reachableBarriers.count(barIdx))
        reachingKernels.push_back(k);
    }
    for (size_t i = 1; i < reachingKernels.size(); ++i)
      groups.unionSets(reachingKernels[0], reachingKernels[i]);
  }

  [[maybe_unused]] unsigned groupIdx = 0;
  for (auto it = groups.begin(), e = groups.end(); it != e; ++it) {
    if (!(*it)->isLeader())
      continue;

    DenseSet<size_t> groupBarriers;
    SmallVector<CGNode *, 4> groupKernels;
    LLVM_DEBUG(dbgs() << "  barrier group " << groupIdx << " kernels:");
    for (auto mi = groups.member_begin(**it); mi != groups.member_end(); ++mi) {
      LLVM_DEBUG(dbgs() << " " << (*mi)->sym->getName());
      groupKernels.push_back(*mi);
      groupBarriers.insert((*mi)->reachableBarriers.begin(),
                           (*mi)->reachableBarriers.end());
    }
    LLVM_DEBUG(dbgs() << "\n");
    ++groupIdx;

    SmallVector<size_t> sharedTier, kernelTier;
    for (size_t idx : groupBarriers) {
      if (isKernelTier(idx))
        kernelTier.push_back(idx);
      else
        sharedTier.push_back(idx);
    }

    llvm::sort(sharedTier, [&](size_t a, size_t b) {
      return barriers[a].sym->getName() < barriers[b].sym->getName();
    });
    llvm::sort(kernelTier, [&](size_t a, size_t b) {
      return barriers[a].sym->getName() < barriers[b].sym->getName();
    });

    uint32_t nextBarId = 1;
    for (size_t idx : sharedTier) {
      barriers[idx].assignedBarId = nextBarId;
      nextBarId += barriers[idx].slotCount;
    }
    for (size_t idx : kernelTier) {
      barriers[idx].assignedBarId = nextBarId;
      nextBarId += barriers[idx].slotCount;
    }

    if (nextBarId - 1 > 31) {
      SmallString<256> kernelList;
      for (size_t i = 0; i < groupKernels.size(); ++i) {
        if (i > 0)
          kernelList += ", ";
        kernelList += groupKernels[i]->sym->getName();
      }
      Err(ctx) << "AMDGPU: named barrier ID overflow (max ID "
               << (nextBarId - 1)
               << " exceeds limit of 31) in kernel group: " << kernelList;
    }
  }

  constexpr uint32_t barScope = 0; // BARRIER_SCOPE_WORKGROUP
  LLVM_DEBUG(dbgs() << "AMDGPU Named Barriers: final assignments:\n");
  for (NamedBarrierInfo &bar : barriers) {
    if (bar.assignedBarId == 0)
      continue;
    uint32_t addr = 0x802000u | (barScope << 9) | (bar.assignedBarId << 4);
    LLVM_DEBUG(dbgs() << "  " << bar.sym->getName()
                      << " -> barId=" << bar.assignedBarId << " addr=0x"
                      << Twine::utohexstr(addr) << "\n");
    Defined(ctx, ctx.internalFile, bar.sym->getName(), STB_GLOBAL, STV_HIDDEN,
            STT_NOTYPE, addr, 0, nullptr)
        .overwrite(*bar.sym);
    if (ctx.arg.shared)
      bar.sym->stOther = (bar.sym->stOther & ~3) | STV_HIDDEN;
  }

  for (CGNode *kernel : cg.kernels()) {
    uint32_t maxBarEnd = 0;
    for (size_t idx : kernel->reachableBarriers) {
      uint32_t end = barriers[idx].assignedBarId + barriers[idx].slotCount - 1;
      maxBarEnd = std::max(maxBarEnd, end);
    }
    kernel->numNamedBarrier = maxBarEnd;
    LLVM_DEBUG(dbgs() << "  " << kernel->sym->getName()
                      << " numNamedBarrier=" << maxBarEnd << "\n");
  }
}

//===----------------------------------------------------------------------===//
// LDS-occupancy validation
//===----------------------------------------------------------------------===//

static void validateLDSOccupancy(Ctx &ctx, AMDGPUCallGraph &cg) {
  for (CGNode *kernel : cg.kernels()) {
    if (kernel->occupancyLDSLimit > 0 &&
        kernel->ldsSize > kernel->occupancyLDSLimit) {
      Err(ctx) << "kernel '" << kernel->sym->getName()
               << "': resolved LDS size (" << kernel->ldsSize
               << " bytes) exceeds the occupancy limit ("
               << kernel->occupancyLDSLimit << " bytes)";
    }
  }
}

//===----------------------------------------------------------------------===//
// Resource usage propagation
//===----------------------------------------------------------------------===//

static void propagateResourceUsage(AMDGPUCallGraph &cg) {
  std::function<PropagatedResourceInfo(CGNode *, DenseSet<CGNode *> &)>
      resolve = [&](CGNode *node,
                    DenseSet<CGNode *> &visiting) -> PropagatedResourceInfo {
    if (node->hasPropagatedRes)
      return node->propagatedRes;

    PropagatedResourceInfo result = {};
    if (node->hasLocalRes) {
      const FunctionResourceInfo &info = node->localRes;
      result.numArchVGPR = info.numArchVGPR;
      result.numAccVGPR = info.numAccVGPR;
      result.numSGPR = info.numSGPR;
      result.numNamedBarrier = info.numNamedBarrier;
      result.totalScratchSize = info.privateSegmentSize;
      result.usesVCC = info.usesVCC;
      result.usesFlatScratch = info.usesFlatScratch;
      result.hasDynSizedStack = info.hasDynSizedStack;
    } else {
      result.hasIncompleteRes = true;
    }

    bool isCycle = !visiting.insert(node).second;
    if (isCycle) {
      result.hasDynSizedStack = true;
      node->propagatedRes = result;
      node->hasPropagatedRes = true;
      return result;
    }

    if (!node->callees.empty()) {
      uint32_t maxCalleeScratch = 0;
      for (CGNode *callee : node->callees) {
        PropagatedResourceInfo calleeInfo = resolve(callee, visiting);
        result.numArchVGPR =
            std::max(result.numArchVGPR, calleeInfo.numArchVGPR);
        result.numAccVGPR = std::max(result.numAccVGPR, calleeInfo.numAccVGPR);
        result.numSGPR = std::max(result.numSGPR, calleeInfo.numSGPR);
        result.numNamedBarrier =
            std::max(result.numNamedBarrier, calleeInfo.numNamedBarrier);
        maxCalleeScratch =
            std::max(maxCalleeScratch, calleeInfo.totalScratchSize);
        result.usesVCC |= calleeInfo.usesVCC;
        result.usesFlatScratch |= calleeInfo.usesFlatScratch;
        result.hasDynSizedStack |= calleeInfo.hasDynSizedStack;
        result.hasIncompleteRes |= calleeInfo.hasIncompleteRes;
      }
      uint32_t localScratch =
          node->hasLocalRes ? node->localRes.privateSegmentSize : 0;
      result.totalScratchSize = localScratch + maxCalleeScratch;
    }

    visiting.erase(node);
    node->propagatedRes = result;
    node->hasPropagatedRes = true;
    return result;
  };

  for (CGNode *kernel : cg.kernels()) {
    DenseSet<CGNode *> visiting;
    resolve(kernel, visiting);
    LLVM_DEBUG(dbgs() << "  propagated " << kernel->sym->getName()
                      << ": vgpr=" << kernel->propagatedRes.numArchVGPR
                      << " agpr=" << kernel->propagatedRes.numAccVGPR
                      << " sgpr=" << kernel->propagatedRes.numSGPR
                      << " scratch=" << kernel->propagatedRes.totalScratchSize
                      << " dynstack=" << kernel->propagatedRes.hasDynSizedStack
                      << "\n");
  }
}

static void patchKernelDescriptors(Ctx &ctx, AMDGPUCallGraph &cg,
                                   const ResourceUsageHeader &header,
                                   const MCSubtargetInfo *STI, bool hasLDS,
                                   bool hasBarriers) {
  using namespace llvm::amdhsa;
  bool sgprBlocksAlwaysZero = header.flags & 0x2;
  bool hasAccumOffset = header.flags & 0x1;
  bool hasNamedBarCnt = header.flags & 0x4;

  // Track sections that have been copied to writable memory so we don't
  // allocate redundant copies when multiple KDs share the same section.
  DenseSet<InputSection *> copiedSections;

  for (CGNode *kernel : cg.kernels()) {
    StringRef name = kernel->sym->getName();
    std::string kdName = (name + ".kd").str();
    Symbol *kdSym = ctx.symtab->find(kdName);
    if (!kdSym)
      continue;
    auto *kdDef = dyn_cast<Defined>(kdSym);
    if (!kdDef || !kdDef->section)
      continue;
    auto *isec = dyn_cast<InputSection>(kdDef->section);
    if (!isec)
      continue;

    uint64_t off = kdDef->value;
    if (off + sizeof(kernel_descriptor_t) > isec->size)
      continue;

    // The section content may be in read-only mmap'd memory. Make a writable
    // copy the first time we need to patch a KD in this section.
    if (copiedSections.insert(isec).second) {
      auto *newBuf = ctx.bAlloc.Allocate<uint8_t>(isec->size);
      memcpy(newBuf, isec->content_, isec->size);
      isec->content_ = newBuf;
    }

    auto *buf = const_cast<uint8_t *>(isec->content_) + off;

    if (hasLDS) {
      write32le(buf + GROUP_SEGMENT_FIXED_SIZE_OFFSET, kernel->ldsSize);
      LLVM_DEBUG(dbgs() << "  patched " << name
                        << ".kd group_segment_fixed_size = " << kernel->ldsSize
                        << "\n");
    }

    if (!kernel->hasPropagatedRes)
      continue;

    const PropagatedResourceInfo &info = kernel->propagatedRes;

    if (info.hasIncompleteRes) {
      Err(ctx) << "kernel '" << kernel->sym->getName()
               << "' has incomplete resource usage (callee missing "
                  ".amdgpu.resource_usage entry)";
      continue;
    }

    write32le(buf + PRIVATE_SEGMENT_FIXED_SIZE_OFFSET, info.totalScratchSize);

    uint32_t totalVGPR = AMDGPU::getTotalNumVGPRs(
        AMDGPU::isGFX90A(*STI), info.numAccVGPR, info.numArchVGPR);
    uint32_t totalSGPR =
        info.numSGPR + AMDGPU::IsaInfo::getNumExtraSGPRs(STI, info.usesVCC,
                                                         info.usesFlatScratch);

    // Read the per-kernel ENABLE_WAVEFRONT_SIZE32 bit from the KD -- it
    // affects the VGPR encoding granule on GFX10+.
    uint16_t kcp = read16le(buf + KERNEL_CODE_PROPERTIES_OFFSET);
    bool enableWave32 = kcp & KERNEL_CODE_PROPERTY_ENABLE_WAVEFRONT_SIZE32;

    // Patch compute_pgm_rsrc1: preserve constant bits, replace VGPR/SGPR blocks
    uint32_t rsrc1 = read32le(buf + COMPUTE_PGM_RSRC1_OFFSET);
    uint32_t vgprBlocks =
        AMDGPU::IsaInfo::getEncodedNumVGPRBlocks(STI, totalVGPR, enableWave32);
    uint32_t sgprBlocks =
        sgprBlocksAlwaysZero
            ? 0
            : AMDGPU::IsaInfo::getNumSGPRBlocks(STI, totalSGPR);
    rsrc1 &= ~COMPUTE_PGM_RSRC1_GRANULATED_WORKITEM_VGPR_COUNT;
    rsrc1 |=
        (vgprBlocks << COMPUTE_PGM_RSRC1_GRANULATED_WORKITEM_VGPR_COUNT_SHIFT) &
        COMPUTE_PGM_RSRC1_GRANULATED_WORKITEM_VGPR_COUNT;
    rsrc1 &= ~COMPUTE_PGM_RSRC1_GRANULATED_WAVEFRONT_SGPR_COUNT;
    rsrc1 |= (sgprBlocks
              << COMPUTE_PGM_RSRC1_GRANULATED_WAVEFRONT_SGPR_COUNT_SHIFT) &
             COMPUTE_PGM_RSRC1_GRANULATED_WAVEFRONT_SGPR_COUNT;
    write32le(buf + COMPUTE_PGM_RSRC1_OFFSET, rsrc1);

    // Patch compute_pgm_rsrc2: update scratch enable bit
    uint32_t rsrc2 = read32le(buf + COMPUTE_PGM_RSRC2_OFFSET);
    rsrc2 &= ~COMPUTE_PGM_RSRC2_ENABLE_PRIVATE_SEGMENT;
    if (info.totalScratchSize > 0 || info.hasDynSizedStack)
      rsrc2 |= COMPUTE_PGM_RSRC2_ENABLE_PRIVATE_SEGMENT;
    write32le(buf + COMPUTE_PGM_RSRC2_OFFSET, rsrc2);

    // Patch compute_pgm_rsrc3: update AccumOffset for GFX90A
    if (hasAccumOffset) {
      uint32_t rsrc3 = read32le(buf + COMPUTE_PGM_RSRC3_OFFSET);
      unsigned archGranule = AMDGPU::IsaInfo::getArchVGPRAllocGranule();
      uint32_t accumOffset =
          divideCeil(std::max(info.numArchVGPR, 1u), archGranule) - 1;
      rsrc3 &= ~COMPUTE_PGM_RSRC3_GFX90A_ACCUM_OFFSET;
      rsrc3 |= (accumOffset << COMPUTE_PGM_RSRC3_GFX90A_ACCUM_OFFSET_SHIFT) &
               COMPUTE_PGM_RSRC3_GFX90A_ACCUM_OFFSET;
      write32le(buf + COMPUTE_PGM_RSRC3_OFFSET, rsrc3);
    }

    // Patch compute_pgm_rsrc3: update NAMED_BAR_CNT for GFX1250
    if (hasBarriers && hasNamedBarCnt) {
      uint32_t rsrc3 = read32le(buf + COMPUTE_PGM_RSRC3_OFFSET);
      uint32_t namedBarCnt = divideCeil(kernel->numNamedBarrier, 4);
      rsrc3 &= ~COMPUTE_PGM_RSRC3_GFX125_NAMED_BAR_CNT;
      rsrc3 |= (namedBarCnt << COMPUTE_PGM_RSRC3_GFX125_NAMED_BAR_CNT_SHIFT) &
               COMPUTE_PGM_RSRC3_GFX125_NAMED_BAR_CNT;
      write32le(buf + COMPUTE_PGM_RSRC3_OFFSET, rsrc3);
      LLVM_DEBUG(dbgs() << "  patched " << name
                        << ".kd NAMED_BAR_CNT=" << namedBarCnt << "\n");
    }

    // Patch kernel_code_properties: update USES_DYNAMIC_STACK
    kcp &= ~KERNEL_CODE_PROPERTY_USES_DYNAMIC_STACK;
    if (info.hasDynSizedStack)
      kcp |= KERNEL_CODE_PROPERTY_USES_DYNAMIC_STACK;
    write16le(buf + KERNEL_CODE_PROPERTIES_OFFSET, kcp);

    LLVM_DEBUG(dbgs() << "  patched " << name << ".kd: scratch="
                      << info.totalScratchSize << " vgprBlocks=" << vgprBlocks
                      << " sgprBlocks=" << sgprBlocks
                      << " dynstack=" << info.hasDynSizedStack << "\n");
  }
}

//===----------------------------------------------------------------------===//
// HSA metadata patching
//===----------------------------------------------------------------------===//

template <class ELFT>
static void patchHSAMetadata(Ctx &ctx, AMDGPUCallGraph &cg,
                             const MCSubtargetInfo *STI, bool hasLDS) {
  bool hasRes = false;
  for (CGNode *k : cg.kernels())
    if (k->hasPropagatedRes) {
      hasRes = true;
      break;
    }
  if (!hasLDS && !hasRes)
    return;

  DenseMap<StringRef, CGNode *> nameToKernel;
  for (CGNode *kernel : cg.kernels())
    nameToKernel[kernel->sym->getName()] = kernel;

  for (InputSectionBase *sec : ctx.inputSections) {
    auto *isec = dyn_cast<InputSection>(sec);
    if (!isec || isec->type != SHT_NOTE)
      continue;
    if (isec->name != ".note")
      continue;

    ArrayRef<uint8_t> data = isec->contentMaybeDecompress();
    if (data.size() < 12)
      continue;

    uint32_t nameSize = read32le(data.data());
    uint32_t descSize = read32le(data.data() + 4);
    uint32_t noteType = read32le(data.data() + 8);

    // NT_AMDGPU_METADATA = 32
    if (noteType != 32)
      continue;

    uint32_t nameOff = 12;
    uint32_t namePadded = alignTo(nameSize, 4);
    uint32_t descOff = nameOff + namePadded;

    if (descOff + descSize > data.size())
      continue;

    ArrayRef<uint8_t> msgpackData = data.slice(descOff, descSize);
    msgpack::Document doc;
    if (!doc.readFromBlob(
            StringRef(reinterpret_cast<const char *>(msgpackData.data()),
                      msgpackData.size()),
            false))
      continue;

    msgpack::MapDocNode root = doc.getRoot().getMap();
    msgpack::DocNode kernelsNode = root["amdhsa.kernels"];
    if (kernelsNode.isEmpty())
      continue;

    bool modified = false;
    msgpack::ArrayDocNode kernelsArray = kernelsNode.getArray();
    for (size_t i = 0, e = kernelsArray.size(); i < e; ++i) {
      msgpack::MapDocNode kernMap = kernelsArray[i].getMap();
      msgpack::DocNode nameNode = kernMap[".name"];
      if (nameNode.isEmpty())
        continue;

      StringRef kernName = nameNode.getString();
      auto it = nameToKernel.find(kernName);
      if (it == nameToKernel.end())
        continue;
      CGNode *kernel = it->second;

      if (hasLDS) {
        kernMap[".group_segment_fixed_size"] = doc.getNode(kernel->ldsSize);
        modified = true;
      }

      if (kernel->hasPropagatedRes) {
        const PropagatedResourceInfo &info = kernel->propagatedRes;
        if (!info.hasIncompleteRes) {
          uint32_t totalVGPR = AMDGPU::getTotalNumVGPRs(
              AMDGPU::isGFX90A(*STI), info.numAccVGPR, info.numArchVGPR);
          uint32_t totalSGPR =
              info.numSGPR + AMDGPU::IsaInfo::getNumExtraSGPRs(
                                 STI, info.usesVCC, info.usesFlatScratch);
          kernMap[".sgpr_count"] = doc.getNode(totalSGPR);
          kernMap[".vgpr_count"] = doc.getNode(totalVGPR);
          kernMap[".agpr_count"] = doc.getNode(info.numAccVGPR);
          kernMap[".private_segment_fixed_size"] =
              doc.getNode(info.totalScratchSize);
          kernMap[".uses_dynamic_stack"] = doc.getNode(info.hasDynSizedStack);
          modified = true;
        }
      }
    }

    if (!modified)
      continue;

    std::string newMsgpack;
    doc.writeToBlob(newMsgpack);

    uint32_t newDescSize = newMsgpack.size();
    uint32_t newDescPadded = alignTo(newDescSize, 4);
    uint32_t newSize = nameOff + namePadded + newDescPadded;

    auto *buf = ctx.bAlloc.Allocate<uint8_t>(newSize);
    memset(buf, 0, newSize);
    write32le(buf, nameSize);
    write32le(buf + 4, newDescSize);
    write32le(buf + 8, noteType);
    memcpy(buf + nameOff, data.data() + nameOff, namePadded);
    memcpy(buf + nameOff + namePadded, newMsgpack.data(), newMsgpack.size());

    isec->content_ = buf;
    isec->size = newSize;
  }
}

//===----------------------------------------------------------------------===//
// Main entry point
//===----------------------------------------------------------------------===//

template <class ELFT> void elf::resolveAMDGPUObjectLinking(Ctx &ctx) {
  llvm::TimeTraceScope timeScope("Resolve AMDGPU Object Linking");

  LLVM_DEBUG(dbgs() << "AMDGPU: collecting LDS symbols\n");
  SmallVector<LDSSymbolInfo, 16> ldsSymbols;
  collectLDSSymbols(ctx, ldsSymbols);
  LLVM_DEBUG(dbgs() << "AMDGPU: found " << ldsSymbols.size()
                    << " LDS symbols\n");

  // Build LDS sym->index map once (used by call graph parser).
  DenseMap<Symbol *, size_t> ldsSymToIndex;
  for (size_t i = 0, e = ldsSymbols.size(); i < e; ++i)
    ldsSymToIndex[ldsSymbols[i].sym] = i;

  AMDGPUCallGraph cg;
  ResourceUsageHeader resHeader = {};

  LLVM_DEBUG(dbgs() << "AMDGPU: parsing sections\n");
  bool hasResourceUsage = false;
  for (ELFFileBase *file : ctx.objectFiles) {
    auto *obj = cast<ObjFile<ELFT>>(file);
    parseCallGraphSection(ctx, obj, cg, ldsSymToIndex);
    ResourceUsageHeader objHeader = {};
    if (parseResourceUsageSection(ctx, obj, cg, objHeader)) {
      if (!hasResourceUsage) {
        resHeader = objHeader;
      } else if (objHeader != resHeader) {
        warn(ctx.arg.outputFile +
             ": inconsistent .amdgpu.resource_usage headers across object "
             "files; using header from first object");
      }
      hasResourceUsage = true;
    }
  }
  LLVM_DEBUG(dbgs() << "AMDGPU: building indirect call edges\n");
  cg.buildIndirectEdges();

  // After call graph parsing, partition LDS symbols into regular LDS and
  // named barriers. Named barriers were identified via __amdgpu_named_barrier
  // entries during call graph parsing. The ldsUseIndices in CGNodes reference
  // the original combined ldsSymbols array -- remap them to separate arrays.
  // The reverse maps (index -> direct user nodes) are built in the same pass
  // so we walk the graph nodes only once.
  SmallVector<NamedBarrierInfo, 4> barriers;
  DenseMap<size_t, SmallVector<CGNode *, 2>> ldsToUsers, barToUsers;
  {
    // Build old-index -> symbol mapping from the original array.
    SmallVector<Symbol *, 16> oldIdxToSym;
    for (const LDSSymbolInfo &lds : ldsSymbols)
      oldIdxToSym.push_back(lds.sym);

    // Partition into regular LDS and named barriers, building index maps.
    DenseMap<Symbol *, size_t> newLdsSymToIndex, barSymToIndex;
    SmallVector<LDSSymbolInfo, 16> regularLDS;
    for (const LDSSymbolInfo &lds : ldsSymbols) {
      if (cg.isNamedBarrier(lds.sym)) {
        barSymToIndex[lds.sym] = barriers.size();
        barriers.push_back({lds.sym, static_cast<uint32_t>(lds.size / 16)});
      } else {
        newLdsSymToIndex[lds.sym] = regularLDS.size();
        regularLDS.push_back(lds);
      }
    }
    ldsSymbols = std::move(regularLDS);

    // Remap CGNode indices: split ldsUseIndices into new ldsUseIndices
    // (regular LDS) and barrierUseIndices (named barriers). Also build
    // reverse maps (index -> direct user nodes) in the same pass.
    for (auto &[sym, node] : cg) {
      SmallVector<size_t, 2> newLds;
      for (size_t oldIdx : node->ldsUseIndices) {
        Symbol *s = oldIdxToSym[oldIdx];
        auto ldsIt = newLdsSymToIndex.find(s);
        if (ldsIt != newLdsSymToIndex.end()) {
          newLds.push_back(ldsIt->second);
          ldsToUsers[ldsIt->second].push_back(node);
        } else {
          auto barIt = barSymToIndex.find(s);
          if (barIt != barSymToIndex.end()) {
            node->barrierUseIndices.push_back(barIt->second);
            barToUsers[barIt->second].push_back(node);
            cg.setHasBarrierUses();
          }
        }
      }
      node->ldsUseIndices = std::move(newLds);
    }
  }

  LLVM_DEBUG(dbgs() << "AMDGPU: " << ldsSymbols.size() << " regular LDS, "
                    << barriers.size() << " named barriers\n");
  LLVM_DEBUG(dbgs() << "AMDGPU: " << cg.kernels().size() << " kernels\n");
  LLVM_DEBUG(if (hasResourceUsage) dbgs()
             << "AMDGPU: has resource usage data\n");

  if (ldsSymbols.empty() && barriers.empty() && !hasResourceUsage) {
    LLVM_DEBUG(dbgs() << "AMDGPU: nothing to resolve\n");
    return;
  }

  // Construct MCSubtargetInfo from merged ELF e_flags for target-aware
  // resource computation (VGPR totals, extra SGPRs, etc.).
  uint32_t eflags = ctx.arg.eflags;
  StringRef cpu = AMDGPU::getArchNameFromElfMach(eflags & ELF::EF_AMDGPU_MACH);
  std::string features;
  if ((eflags & ELF::EF_AMDGPU_FEATURE_XNACK_V4) ==
      ELF::EF_AMDGPU_FEATURE_XNACK_ON_V4)
    features = "+xnack";

  if (ctx.arg.osabi != ELF::ELFOSABI_AMDGPU_HSA) {
    Err(ctx) << "AMDGPU object linking is only supported for amdhsa (OSABI "
             << ctx.arg.osabi << ")";
    return;
  }

  std::string error;
  Triple triple("amdgcn-amd-amdhsa");
  const Target *target = TargetRegistry::lookupTarget(triple, error);
  if (!target) {
    Err(ctx) << "AMDGPU: failed to look up target: " << error;
    return;
  }
  std::unique_ptr<MCSubtargetInfo> STI(
      target->createMCSubtargetInfo(triple, cpu, features));

  bool hasLDS = !ldsSymbols.empty();
  bool hasBarriers = !barriers.empty();

  if ((cg.hasLDSUses() || cg.hasBarrierUses()) && !cg.kernels().empty()) {
    LLVM_DEBUG(dbgs() << "AMDGPU: computing kernel reachability\n");
    computeKernelReachability(cg);
  }

  if (hasLDS)
    resolveLDS(ctx, ldsSymbols, cg, ldsToUsers);

  if (hasBarriers && !cg.kernels().empty())
    resolveNamedBarriers(ctx, barriers, cg, barToUsers);

  if (hasLDS && !cg.kernels().empty())
    validateLDSOccupancy(ctx, cg);

  if (hasResourceUsage && !cg.kernels().empty()) {
    LLVM_DEBUG(dbgs() << "AMDGPU: propagating resource usage\n");
    propagateResourceUsage(cg);
  }

  LLVM_DEBUG(dbgs() << "AMDGPU: patching kernel descriptors\n");
  patchKernelDescriptors(ctx, cg, resHeader, STI.get(), hasLDS, hasBarriers);

  LLVM_DEBUG(dbgs() << "AMDGPU: patching HSA metadata\n");
  patchHSAMetadata<ELFT>(ctx, cg, STI.get(), hasLDS);
}

template void elf::resolveAMDGPUObjectLinking<ELF32LE>(Ctx &);
template void elf::resolveAMDGPUObjectLinking<ELF32BE>(Ctx &);
template void elf::resolveAMDGPUObjectLinking<ELF64LE>(Ctx &);
template void elf::resolveAMDGPUObjectLinking<ELF64BE>(Ctx &);
