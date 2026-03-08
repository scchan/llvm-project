# REQUIRES: amdgpu

## Test size-based tie-breaking when shared-tier variables have equal use
## counts. The greedy algorithm breaks ties by placing larger variables at
## higher offsets.
##
## Variables (all external linkage -> global-scope -> shared tier):
##   big:   64 bytes align 4->16*, used by K1, K2 (2 users)
##   small: 8 bytes align 4, used by K1, K2       (2 users)
##   (* superAlignLDSGlobals bumps alignment to 16 for vars >= 16 bytes)
##
## Both have use_count=2. Greedy from tail:
##   Position 2: tie, break by size -> big (64>8) placed at position 2.
##     K1, K2 fixed.
##   Position 1: small left.
##   Result: [small, big]
##
## Layout: small(8,a4)@0x00, big(64,a16)@0x10

# RUN: split-file %s %t
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/tu1.ll -o %t/tu1.o
# RUN: ld.lld %t/tu1.o -o %t/out
# RUN: llvm-readelf -s %t/out | FileCheck %s --check-prefix=SYM

## small at lower offset, big at higher offset
# SYM-DAG: 0000000000000000 {{.*}} small
# SYM-DAG: 0000000000000010 {{.*}} big

#--- tu1.ll
@big = addrspace(3) global [16 x i32] poison, align 4
@small = addrspace(3) global [2 x i32] poison, align 4

define amdgpu_kernel void @K1(i32 %idx) {
  %pb = getelementptr [16 x i32], ptr addrspace(3) @big, i32 0, i32 %idx
  store i32 1, ptr addrspace(3) %pb
  %ps = getelementptr [2 x i32], ptr addrspace(3) @small, i32 0, i32 %idx
  store i32 2, ptr addrspace(3) %ps
  ret void
}

define amdgpu_kernel void @K2(i32 %idx) {
  %pb = getelementptr [16 x i32], ptr addrspace(3) @big, i32 0, i32 %idx
  store i32 3, ptr addrspace(3) %pb
  %ps = getelementptr [2 x i32], ptr addrspace(3) @small, i32 0, i32 %idx
  store i32 4, ptr addrspace(3) %ps
  ret void
}
