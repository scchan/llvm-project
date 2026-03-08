# REQUIRES: amdgpu

## Test that usage frequency drives shared-tier placement. The variable used
## by the most kernels should be placed at the lowest offset regardless of
## its size.
##
## Variables (all external linkage -> global-scope -> shared tier):
##   S1: 16 bytes align 4->16*, used by K1, K2     (2 users)
##   S2: 8 bytes align 4, used by K1, K2, K3       (3 users, smallest!)
##   S3: 32 bytes align 4->16*, used by K1, K2     (2 users)
##   (* superAlignLDSGlobals bumps alignment to 16 for vars >= 16 bytes)
##
## Greedy from tail:
##   Position 3: use_count S1=2, S2=3, S3=2. Min=2, tie S1(16) vs S3(32).
##     Pick S3 (larger). K1,K2 fixed. S1->0, S2->1.
##   Position 2: use_count S1=0, S2=1. Min=0 -> S1.
##   Position 1: S2 left.
##   Result: [S2, S1, S3]
##
## Layout: S2(8,a4)@0x00, S1(16,a16)@0x10, S3(32,a16)@0x20
##
## Per-kernel sizes:
##   K1: reaches all -> 64 = 0x40
##   K2: same -> 64 = 0x40
##   K3: reaches S2(0..8) -> 8 = 0x08 (zero waste!)
##
## A naive size-desc sort [S3,S1,S2] would give K3 size = 64 (waste = 56).

# RUN: split-file %s %t
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/tu1.ll -o %t/tu1.o
# RUN: ld.lld %t/tu1.o -o %t/out
# RUN: llvm-readelf -s %t/out | FileCheck %s --check-prefix=SYM
# RUN: llvm-readobj --notes %t/out | FileCheck %s --check-prefix=META

## S2 (most shared, 3 users) at lowest offset despite being smallest
# SYM-DAG: 0000000000000000 {{.*}} S2
# SYM-DAG: 0000000000000010 {{.*}} S1
# SYM-DAG: 0000000000000020 {{.*}} S3

## K3 uses only S2: minimal size
# META-DAG: .group_segment_fixed_size: 8
## K1 and K2 use all three
# META-DAG: .group_segment_fixed_size: 64
# META-DAG: .group_segment_fixed_size: 64

#--- tu1.ll
@S1 = addrspace(3) global [4 x i32] poison, align 4
@S2 = addrspace(3) global [2 x i32] poison, align 4
@S3 = addrspace(3) global [8 x i32] poison, align 4

define amdgpu_kernel void @K1(i32 %idx) {
  %p1 = getelementptr [4 x i32], ptr addrspace(3) @S1, i32 0, i32 %idx
  store i32 1, ptr addrspace(3) %p1
  %p2 = getelementptr [2 x i32], ptr addrspace(3) @S2, i32 0, i32 %idx
  store i32 2, ptr addrspace(3) %p2
  %p3 = getelementptr [8 x i32], ptr addrspace(3) @S3, i32 0, i32 %idx
  store i32 3, ptr addrspace(3) %p3
  ret void
}

define amdgpu_kernel void @K2(i32 %idx) {
  %p1 = getelementptr [4 x i32], ptr addrspace(3) @S1, i32 0, i32 %idx
  store i32 4, ptr addrspace(3) %p1
  %p2 = getelementptr [2 x i32], ptr addrspace(3) @S2, i32 0, i32 %idx
  store i32 5, ptr addrspace(3) %p2
  %p3 = getelementptr [8 x i32], ptr addrspace(3) @S3, i32 0, i32 %idx
  store i32 6, ptr addrspace(3) %p3
  ret void
}

define amdgpu_kernel void @K3(i32 %idx) {
  %p2 = getelementptr [2 x i32], ptr addrspace(3) @S2, i32 0, i32 %idx
  store i32 7, ptr addrspace(3) %p2
  ret void
}
