# REQUIRES: amdgpu

## Test that shared-tier ordering is optimized while kernel-tier variables
## are correctly appended after the shared tier.
##
## Variables:
##   shared_a: 8 bytes align 4, external, used by K1, K2, K3  (shared, 3 users)
##   shared_b: 32 bytes align 4->16*, external, used by K1, K2 (shared, 2 users)
##   k1_priv:  16 bytes align 4->16*, internal, used by K1     (kernel tier)
##   (* superAlignLDSGlobals bumps alignment to 16 for vars >= 16 bytes)
##
## Greedy shared tier from tail:
##   Position 2: use_count shared_a=3, shared_b=2. Min=2 -> shared_b.
##     K1,K2 fixed. shared_a->1.
##   Position 1: shared_a left.
##   Result: [shared_a, shared_b]
##
## Layout:
##   Shared: shared_a(8,a4)@0x00, shared_b(32,a16)@0x10
##   Kernel: __amdgpu_lds.K1(16,a16)@0x30
##
## Per-kernel sizes:
##   K1: shared_a(0..8), shared_b(16..48), K1's struct(48..64) -> 64 = 0x40
##   K2: shared_a(0..8), shared_b(16..48) -> 48 = 0x30
##   K3: shared_a(0..8) -> 8 = 0x08 (zero waste!)

# RUN: split-file %s %t
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/tu1.ll -o %t/tu1.o
# RUN: ld.lld %t/tu1.o -o %t/out
# RUN: llvm-readelf -s %t/out | FileCheck %s --check-prefix=SYM
# RUN: llvm-readobj --notes %t/out | FileCheck %s --check-prefix=META

## Shared tier: shared_a first (most shared), shared_b after
# SYM-DAG: 0000000000000000 {{.*}} shared_a
# SYM-DAG: 0000000000000010 {{.*}} shared_b
## Kernel tier appended after shared tier
# SYM-DAG: 0000000000000030 {{.*}} __amdgpu_lds.K1

## K3 (uses only shared_a) has minimal size
# META-DAG: .group_segment_fixed_size: 8
## K2 (uses shared_a + shared_b)
# META-DAG: .group_segment_fixed_size: 48
## K1 (uses shared_a + shared_b + k1_priv)
# META-DAG: .group_segment_fixed_size: 64

#--- tu1.ll
@shared_a = addrspace(3) global [2 x i32] poison, align 4
@shared_b = addrspace(3) global [8 x i32] poison, align 4
@k1_priv = internal addrspace(3) global [4 x i32] poison, align 4

define amdgpu_kernel void @K1(i32 %idx) {
  %pa = getelementptr [2 x i32], ptr addrspace(3) @shared_a, i32 0, i32 %idx
  store i32 1, ptr addrspace(3) %pa
  %pb = getelementptr [8 x i32], ptr addrspace(3) @shared_b, i32 0, i32 %idx
  store i32 2, ptr addrspace(3) %pb
  %pk = getelementptr [4 x i32], ptr addrspace(3) @k1_priv, i32 0, i32 0
  store i32 3, ptr addrspace(3) %pk
  ret void
}

define amdgpu_kernel void @K2(i32 %idx) {
  %pa = getelementptr [2 x i32], ptr addrspace(3) @shared_a, i32 0, i32 %idx
  store i32 4, ptr addrspace(3) %pa
  %pb = getelementptr [8 x i32], ptr addrspace(3) @shared_b, i32 0, i32 %idx
  store i32 5, ptr addrspace(3) %pb
  ret void
}

define amdgpu_kernel void @K3(i32 %idx) {
  %pa = getelementptr [2 x i32], ptr addrspace(3) @shared_a, i32 0, i32 %idx
  store i32 6, ptr addrspace(3) %pa
  ret void
}
