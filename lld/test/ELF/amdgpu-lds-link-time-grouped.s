# REQUIRES: amdgpu

## Test grouped LDS allocation with independent kernel groups and tier ordering.
##
## TU1 has:
##   - func: uses @lds_callee (callee-scope, internal, 64 bytes)
##   - K1: uses @lds_global (global-scope, external, 32 bytes),
##         uses @lds_k1 (kernel-scope, internal, 16 bytes), calls func
##   - K2: uses @lds_global, calls func (no kernel-scope LDS)
##
## TU2 has:
##   - K3: uses @lds_k3 (kernel-scope, internal, 128 bytes)
##
## Grouping:
##   K1, K2 share lds_callee and lds_global -> Group 1
##   K3 is independent -> Group 2
##
## Group 1 tier classification:
##   Shared tier: __amdgpu_lds.func (callee-scope, user=func not a kernel)
##                lds_global (global-scope, users=K1,K2)
##   Kernel tier: __amdgpu_lds.K1 (kernel-scope, user=K1 a kernel)
##
## Group 1 layout (shared-tier ordered by greedy waste minimization,
## both shared vars have use_count=2, tie-broken by size -- larger at
## higher offset):
##   Shared: lds_global (align 16, size 32) @ 0x00
##           __amdgpu_lds.func (align 16, size 64) @ 0x20
##   Kernel: __amdgpu_lds.K1 (align 16, size 16) @ 0x60
##
## Group 2 layout (starts from offset 0):
##   __amdgpu_lds.K3 (align 16, size 128) @ 0x00
##
## Per-kernel sizes:
##   K1: reaches lds_global(0..32), func's struct(32..96), K1's struct(96..112) -> 0x70
##   K2: reaches lds_global(0..32), func's struct(32..96) -> 0x60
##   K3: reaches K3's struct(0..128) -> 0x80

# RUN: split-file %s %t
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/tu1.ll -o %t/tu1.o
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/tu2.ll -o %t/tu2.o
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/tu3.ll -o %t/tu3.o
# RUN: ld.lld %t/tu1.o %t/tu2.o %t/tu3.o -o %t/out
# RUN: llvm-readelf -s %t/out | FileCheck %s --check-prefix=SYM
# RUN: llvm-readobj --notes %t/out | FileCheck %s --check-prefix=META

## LDS symbol offsets (Group 1 shared tier first, kernel tier last)
# SYM-DAG: 0000000000000000 {{.*}} lds_global
# SYM-DAG: 0000000000000020 {{.*}} __amdgpu_lds.func
# SYM-DAG: 0000000000000060 {{.*}} __amdgpu_lds.K1

## Group 2 allocates from offset 0 independently
# SYM-DAG: 0000000000000000 {{.*}} __amdgpu_lds.K3

## Per-kernel LDS sizes patched into the kernel descriptor and HSA metadata
# META-DAG: .group_segment_fixed_size: 112
# META-DAG: .group_segment_fixed_size: 96
# META-DAG: .group_segment_fixed_size: 128

#--- tu1.ll
; Global-scope LDS (external linkage, used by K1 and K2).
@lds_global = addrspace(3) global [8 x i32] poison, align 4

; Callee-scope LDS (internal linkage, used by func only).
@lds_callee = internal addrspace(3) global [16 x i32] poison, align 4

; Kernel-scope LDS (internal linkage, used by K1 only).
@lds_k1 = internal addrspace(3) global [4 x i32] poison, align 4

declare void @extern_func()

define void @func() {
  %p = getelementptr [16 x i32], ptr addrspace(3) @lds_callee, i32 0, i32 0
  store i32 1, ptr addrspace(3) %p
  call void @extern_func()
  ret void
}

define amdgpu_kernel void @K1(i32 %idx) {
  %p1 = getelementptr [8 x i32], ptr addrspace(3) @lds_global, i32 0, i32 %idx
  store i32 2, ptr addrspace(3) %p1
  %p2 = getelementptr [4 x i32], ptr addrspace(3) @lds_k1, i32 0, i32 0
  store i32 3, ptr addrspace(3) %p2
  call void @func()
  ret void
}

define amdgpu_kernel void @K2(i32 %idx) {
  %p = getelementptr [8 x i32], ptr addrspace(3) @lds_global, i32 0, i32 %idx
  store i32 4, ptr addrspace(3) %p
  call void @func()
  ret void
}

#--- tu2.ll
; Kernel-scope LDS (internal linkage, used by K3 only).
@lds_k3 = internal addrspace(3) global [32 x i32] poison, align 4

define amdgpu_kernel void @K3(i32 %idx) {
  %p = getelementptr [32 x i32], ptr addrspace(3) @lds_k3, i32 0, i32 %idx
  store i32 5, ptr addrspace(3) %p
  ret void
}

#--- tu3.ll
define void @extern_func() {
  ret void
}
