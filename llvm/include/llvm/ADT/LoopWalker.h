//===- ADT/LoopWalker.h - Iterate loop skipping subloops -------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
///
/// This provides an iterator over the successors of a block with two properties:
/// 1. It skips backedges.
/// 2. At the header of a subloop, it skips over the entire subloop by treating
///    its exit blocks as successors of the header.
///
/// The iterator also treats the function body as a special loop. This is useful
/// for locating SCCs that are not inside any loop.
///
//===----------------------------------------------------------------------===//

#ifndef LLVM_ADT_LOOPWALKER_H
#define LLVM_ADT_LOOPWALKER_H

#include "llvm/Analysis/LoopInfo.h"

namespace llvm {

template <class LoopInfoT>
struct LoopInfoTraits {
};

template <>
struct LoopInfoTraits<LoopInfo> {
  using BlockT = BasicBlock;
  using LoopT = Loop;
};

template <class LoopInfoT>
struct LoopWalker {
  using LoopT = typename LoopInfoTraits<LoopInfoT>::LoopT;
  using BlockT = typename LoopInfoTraits<LoopInfoT>::BlockT;

  const LoopInfoT *LI;
  const LoopT *L;
  BlockT *BB;

  LoopWalker(uintptr_t i) {
    LI = nullptr;
    L = nullptr;
    BB = reinterpret_cast<BlockT*>(i);
  }

  LoopWalker(const LoopInfoT *LI, BlockT *BB)
      : LI(LI), BB(BB) {
    L = LI->getLoopFor(BB);
  }

  LoopWalker(const LoopInfoT *LI, const LoopT *L, BlockT *BB) : LI(LI), L(L), BB(BB) {}

  bool operator==(const LoopWalker &x) const {
    return x.BB == BB;
  }

  bool operator!=(const LoopWalker &x) const {
    return !(*this == x);
  }

  bool isIncomingPred(BlockT *Pred) {
    auto PredLoop = LI->getLoopFor(Pred);
    return !PredLoop || PredLoop->contains(L);
  }

  class child_iterator : public iterator_facade_base<
                                  LoopWalker::child_iterator, std::forward_iterator_tag,
                                  LoopWalker> {
    friend LoopWalker;
    using BlockT = typename LoopWalker::BlockT;

    const LoopInfoT *LI;
    const LoopT *L;
    BlockT *BB;

    SmallVector<BlockT*, 8> Children;

    bool allowSuccessor(BlockT *Succ) {
      if (L && Succ == L->getHeader()) return false;
      auto ImmLoop = LI->getLoopFor(Succ);
      if (ImmLoop == L) return true;
      return ImmLoop
          && ImmLoop->getParentLoop() == L
          && ImmLoop->getHeader() == Succ;
    }

    child_iterator() = default;

    child_iterator(LoopWalker &G) : LI(G.LI), L(G.L), BB(G.BB) {
      auto ImmLoop = LI->getLoopFor(BB);
      if (ImmLoop != L) {
        assert(ImmLoop->getParentLoop() == L);
        ImmLoop->getUniqueExitBlocks(Children);

        Children.erase(std::remove_if(Children.begin(), Children.end(),
                                      [&] (BlockT *X) {
                                        return !allowSuccessor(X);
                                      }),
                       Children.end());
      } else {
        for (auto Succ : successors(BB)) {
          if (!allowSuccessor(Succ)) continue;
          Children.push_back(Succ);
        }
      }
    }

  public:
    bool operator==(const child_iterator &x) const {
      return x.Children == Children;
    }

    child_iterator &operator++() {
      Children.pop_back();
      return *this;
    }

    child_iterator operator++(int I) {
      child_iterator copy(*this);
      ++(*this);
      return copy;
    }

    LoopWalker operator*() const {
      assert(!Children.empty());
      return {LI, L, Children.back()};
    }
  };

  child_iterator begin() {
    return {*this};
  }

  child_iterator end() {
    return {};
  }
};

template <class LoopInfoT>
struct DenseMapInfo<LoopWalker<LoopInfoT>> {
  using KeyT = LoopWalker<LoopInfoT>;
  static inline KeyT getEmptyKey() { return {~1U}; }
  static inline KeyT getTombstoneKey() { return {~2U}; }

  static unsigned getHashValue(const KeyT &Key) {
    return static_cast<unsigned>(hash_value(Key.BB));
  }

  static bool isEqual(const KeyT &LHS, const KeyT &RHS) {
    return LHS == RHS;
  }
};

template<class LoopInfoT>
struct GraphTraits<LoopWalker<LoopInfoT>> {
  using NodeRef = LoopWalker<LoopInfoT>;
  using ChildIteratorType = typename NodeRef::child_iterator;

  static NodeRef getEntryNode(const NodeRef &G) {
    return G;
  }

  static ChildIteratorType child_begin(NodeRef &G) {
    return G.begin();
  }

  static ChildIteratorType child_end(NodeRef &G) {
    return G.end();
  }
};

} // end namespace llvm

#endif // LLVM_ADT_LOOPWALKER_H
