# REQUIRES: amdgpu

## Test that multiple independent groups each have their shared-tier ordering
## optimized independently, and each group allocates from offset 0.
##
## Group 1 (K1, K2 share A and B):
##   A: 8 bytes align 4, used by K1, K2, K3     (3 users)
##   B: 16 bytes align 4->16*, used by K1, K2   (2 users)
##   C: 32 bytes align 4->16*, used by K1, K2   (2 users)
##
## Group 2 (K4, K5 share D):
##   D: 4 bytes align 4, used by K4, K5  (2 users)
##   E: 8 bytes align 4, used by K4, K5  (2 users)
##
## Groups are independent (no shared LDS between them).
##
## Group 1 greedy: [A, B, C] (A@0x00, B@0x10, C@0x20)
##   K3 uses only A -> size = 8
##
## Group 2 greedy: both D and E have use_count=2.
##   Tie-break by size: E(8)>D(4). E placed at tail.
##   Result: [D, E] (D@0x00, E@0x08)
##   (* superAlignLDSGlobals bumps alignment to 16 for vars >= 16 bytes,
##      and E to align 8 since it is 8 bytes)

# RUN: split-file %s %t
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/tu1.ll -o %t/tu1.o
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/tu2.ll -o %t/tu2.o
# RUN: ld.lld %t/tu1.o %t/tu2.o -o %t/out
# RUN: llvm-readelf -s %t/out | FileCheck %s --check-prefix=SYM
# RUN: llvm-readobj --notes %t/out | FileCheck %s --check-prefix=META

## Group 1: A most shared, at offset 0
# SYM-DAG: 0000000000000000 {{.*}} A
# SYM-DAG: 0000000000000010 {{.*}} B
# SYM-DAG: 0000000000000020 {{.*}} C

## Group 2: D at offset 0 (independent group), E at offset 8 (align 8)
# SYM-DAG: 0000000000000000 {{.*}} D
# SYM-DAG: 0000000000000008 {{.*}} E

## K3 uses only A -> 8 bytes
# META-DAG: .group_segment_fixed_size: 8
## K1 and K2 use all of group 1 -> 64 bytes
# META-DAG: .group_segment_fixed_size: 64
# META-DAG: .group_segment_fixed_size: 64
## K4 and K5 use all of group 2 -> 16 bytes (D@0..4, E@8..16)
# META-DAG: .group_segment_fixed_size: 16
# META-DAG: .group_segment_fixed_size: 16

#--- tu1.ll
@A = addrspace(3) global [2 x i32] poison, align 4
@B = addrspace(3) global [4 x i32] poison, align 4
@C = addrspace(3) global [8 x i32] poison, align 4

define amdgpu_kernel void @K1(i32 %idx) {
  %pa = getelementptr [2 x i32], ptr addrspace(3) @A, i32 0, i32 %idx
  store i32 1, ptr addrspace(3) %pa
  %pb = getelementptr [4 x i32], ptr addrspace(3) @B, i32 0, i32 %idx
  store i32 2, ptr addrspace(3) %pb
  %pc = getelementptr [8 x i32], ptr addrspace(3) @C, i32 0, i32 %idx
  store i32 3, ptr addrspace(3) %pc
  ret void
}

define amdgpu_kernel void @K2(i32 %idx) {
  %pa = getelementptr [2 x i32], ptr addrspace(3) @A, i32 0, i32 %idx
  store i32 4, ptr addrspace(3) %pa
  %pb = getelementptr [4 x i32], ptr addrspace(3) @B, i32 0, i32 %idx
  store i32 5, ptr addrspace(3) %pb
  %pc = getelementptr [8 x i32], ptr addrspace(3) @C, i32 0, i32 %idx
  store i32 6, ptr addrspace(3) %pc
  ret void
}

define amdgpu_kernel void @K3(i32 %idx) {
  %pa = getelementptr [2 x i32], ptr addrspace(3) @A, i32 0, i32 %idx
  store i32 7, ptr addrspace(3) %pa
  ret void
}

#--- tu2.ll
@D = addrspace(3) global [1 x i32] poison, align 4
@E = addrspace(3) global [2 x i32] poison, align 4

define amdgpu_kernel void @K4(i32 %idx) {
  %pd = getelementptr [1 x i32], ptr addrspace(3) @D, i32 0, i32 0
  store i32 8, ptr addrspace(3) %pd
  %pe = getelementptr [2 x i32], ptr addrspace(3) @E, i32 0, i32 %idx
  store i32 9, ptr addrspace(3) %pe
  ret void
}

define amdgpu_kernel void @K5(i32 %idx) {
  %pd = getelementptr [1 x i32], ptr addrspace(3) @D, i32 0, i32 0
  store i32 10, ptr addrspace(3) %pd
  %pe = getelementptr [2 x i32], ptr addrspace(3) @E, i32 0, i32 %idx
  store i32 11, ptr addrspace(3) %pe
  ret void
}
