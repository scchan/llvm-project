# REQUIRES: amdgpu

## Test shared-tier ordering with 4 kernels and 4 shared-tier variables with
## a complex overlapping usage pattern.
##
## Variables (all external linkage -> global-scope -> shared tier):
##   V1: 4 bytes align 4, used by K1, K2, K3, K4 (4 users)
##   V2: 8 bytes align 4, used by K1, K2, K3     (3 users)
##   V3: 16 bytes align 4->16*, used by K1, K2   (2 users)
##   V4: 32 bytes align 4->16*, used by K1, K3   (2 users)
##   (* superAlignLDSGlobals bumps alignment to 16 for vars >= 16 bytes)
##
## Greedy from tail:
##   Position 4: use_count V1=4, V2=3, V3=2, V4=2. Min=2, tie V3(16) vs V4(32).
##     Pick V4 (larger). K1,K3 use V4 -> fixed.
##     Update: V1: 4-2=2, V2: 3-2=1, V3: 2-1=1.
##   Position 3: use_count V1=2, V2=1, V3=1. Min=1, tie V2(8) vs V3(16).
##     Pick V3 (larger). K2 uses V3 -> fixed.
##     Update: V1: 2-1=1, V2: 1-1=0.
##   Position 2: use_count V1=1, V2=0. Min=0 -> V2.
##   Position 1: V1 left.
##   Result: [V1, V2, V3, V4]
##
## Layout: V1(4,a4)@0x00, V2(8,a8)@0x08, V3(16,a16)@0x10, V4(32,a16)@0x20
##   (superAlignLDSGlobals also bumps V2 to align 8)
##
## Per-kernel sizes:
##   K1: all -> max(4, 16, 32, 64) = 64 = 0x40
##   K2: V1,V2,V3 -> max(4, 16, 32) = 32 = 0x20
##   K3: V1,V2,V4 -> max(4, 16, 64) = 64 = 0x40
##   K4: V1 -> 4 = 0x04

# RUN: split-file %s %t
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/tu1.ll -o %t/tu1.o
# RUN: ld.lld %t/tu1.o -o %t/out
# RUN: llvm-readelf -s %t/out | FileCheck %s --check-prefix=SYM
# RUN: llvm-readobj --notes %t/out | FileCheck %s --check-prefix=META

## V1 (4 users) at lowest offset
# SYM-DAG: 0000000000000000 {{.*}} V1
## V2 (was 3 users, placed early after dynamic updates; aligned to 8)
# SYM-DAG: 0000000000000008 {{.*}} V2
## V3 (2 users)
# SYM-DAG: 0000000000000010 {{.*}} V3
## V4 (2 users, largest) at highest offset
# SYM-DAG: 0000000000000020 {{.*}} V4

## K4 uses only V1: minimal size = 4
# META-DAG: .group_segment_fixed_size: 4
## K2 uses V1,V2,V3: size = 32
# META-DAG: .group_segment_fixed_size: 32
## K1 uses all: size = 64
# META-DAG: .group_segment_fixed_size: 64
## K3 uses V1,V2,V4: size = 64
# META-DAG: .group_segment_fixed_size: 64

#--- tu1.ll
@V1 = addrspace(3) global [1 x i32] poison, align 4
@V2 = addrspace(3) global [2 x i32] poison, align 4
@V3 = addrspace(3) global [4 x i32] poison, align 4
@V4 = addrspace(3) global [8 x i32] poison, align 4

define amdgpu_kernel void @K1(i32 %idx) {
  %p1 = getelementptr [1 x i32], ptr addrspace(3) @V1, i32 0, i32 0
  store i32 1, ptr addrspace(3) %p1
  %p2 = getelementptr [2 x i32], ptr addrspace(3) @V2, i32 0, i32 %idx
  store i32 2, ptr addrspace(3) %p2
  %p3 = getelementptr [4 x i32], ptr addrspace(3) @V3, i32 0, i32 %idx
  store i32 3, ptr addrspace(3) %p3
  %p4 = getelementptr [8 x i32], ptr addrspace(3) @V4, i32 0, i32 %idx
  store i32 4, ptr addrspace(3) %p4
  ret void
}

define amdgpu_kernel void @K2(i32 %idx) {
  %p1 = getelementptr [1 x i32], ptr addrspace(3) @V1, i32 0, i32 0
  store i32 5, ptr addrspace(3) %p1
  %p2 = getelementptr [2 x i32], ptr addrspace(3) @V2, i32 0, i32 %idx
  store i32 6, ptr addrspace(3) %p2
  %p3 = getelementptr [4 x i32], ptr addrspace(3) @V3, i32 0, i32 %idx
  store i32 7, ptr addrspace(3) %p3
  ret void
}

define amdgpu_kernel void @K3(i32 %idx) {
  %p1 = getelementptr [1 x i32], ptr addrspace(3) @V1, i32 0, i32 0
  store i32 8, ptr addrspace(3) %p1
  %p2 = getelementptr [2 x i32], ptr addrspace(3) @V2, i32 0, i32 %idx
  store i32 9, ptr addrspace(3) %p2
  %p4 = getelementptr [8 x i32], ptr addrspace(3) @V4, i32 0, i32 %idx
  store i32 10, ptr addrspace(3) %p4
  ret void
}

define amdgpu_kernel void @K4(i32 %idx) {
  %p1 = getelementptr [1 x i32], ptr addrspace(3) @V1, i32 0, i32 0
  store i32 11, ptr addrspace(3) %p1
  ret void
}
