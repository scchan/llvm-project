# REQUIRES: amdgpu

## Test shared-tier ordering with nested usage subsets. The greedy algorithm
## should produce zero waste by placing the most-shared variable at the lowest
## offset.
##
## Variables (all external linkage -> global-scope -> shared tier):
##   A: 8 bytes align 4, used by K1, K2, K3    (3 users)
##   B: 16 bytes align 4->16*, used by K1, K2  (2 users)
##   C: 32 bytes align 4->16*, used by K1, K2  (2 users)
##   (* superAlignLDSGlobals bumps alignment to 16 for vars >= 16 bytes)
##
## Greedy from tail:
##   Position 3: use_count A=3, B=2, C=2. Min=2, tie -> C (larger, 32>16).
##     K1 and K2 fixed. use_count A->1, B->0.
##   Position 2: use_count A=1, B=0. Min=0 -> B.
##   Position 1: A left.
##   Result: [A, B, C]
##
## Layout: A(8,a4)@0x00, B(16,a16)@0x10, C(32,a16)@0x20
##
## Per-kernel sizes:
##   K1: reaches A(0..8), B(16..32), C(32..64) -> 64 = 0x40
##   K2: same -> 64 = 0x40
##   K3: reaches A(0..8) -> 8 = 0x08 (zero waste!)
##
## A naive size-desc sort [C,B,A] would give K3 size = 64 (waste = 56).

# RUN: split-file %s %t
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/tu1.ll -o %t/tu1.o
# RUN: ld.lld %t/tu1.o -o %t/out
# RUN: llvm-readelf -s %t/out | FileCheck %s --check-prefix=SYM
# RUN: llvm-readobj --notes %t/out | FileCheck %s --check-prefix=META

## A (most shared, 3 users) at lowest offset
# SYM-DAG: 0000000000000000 {{.*}} A
## B at offset 0x10 (aligned to 16)
# SYM-DAG: 0000000000000010 {{.*}} B
## C at offset 0x20
# SYM-DAG: 0000000000000020 {{.*}} C

## K3 should have minimal LDS size (only uses A, 8 bytes)
# META-DAG: .group_segment_fixed_size: 8
## K1 and K2 use all three: 64 bytes
# META-DAG: .group_segment_fixed_size: 64
# META-DAG: .group_segment_fixed_size: 64

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
