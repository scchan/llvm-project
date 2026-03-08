# REQUIRES: amdgpu

## End-to-end IR-to-linked-binary instruction verification for link-time LDS.
## Two TUs share an LDS symbol (__lds_shared) across translation units and
## TU2 also has a private LDS symbol (__lds_private). This tests the full
## pipeline from compiler output through linking, checking:
##   1) Pre-link: relocations in object files (R_AMDGPU_ABS32_LO)
##   2) Pre-link: placeholder 0 in address-computation instructions
##   3) Post-link: resolved offsets patched into instructions
##   4) LDS load/store instructions remain intact through linking
##
## LDS layout (alignment desc, size desc):
##   __lds_shared  (align=16, size=256) -> offset 0x000
##   __lds_private (align=4,  size=128) -> offset 0x100
##
## TU1: kernel_a stores 42 to __lds_shared[idx].
## TU2: kernel_b reads __lds_shared[idx], increments it, writes it back,
##      and stores 99 to __lds_private[idx].

# RUN: split-file %s %t
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -amdgpu-enable-lower-module-lds=0 -filetype=obj %t/tu1.ll -o %t/tu1.o
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -amdgpu-enable-lower-module-lds=0 -filetype=obj %t/tu2.ll -o %t/tu2.o

## Pre-link: verify relocations target the LDS symbols.
# RUN: llvm-objdump -d -r %t/tu1.o | FileCheck %s --check-prefix=PRE1
# RUN: llvm-objdump -d -r %t/tu2.o | FileCheck %s --check-prefix=PRE2

## Link.
# RUN: ld.lld %t/tu1.o %t/tu2.o -o %t/out

## Post-link: verify resolved instructions.
# RUN: llvm-objdump -d %t/out | FileCheck %s --check-prefix=POST

## === Pre-link TU1: kernel_a ===
## The compiler emits s_lshl2_add_u32 to compute byte offset (idx << 2) + base.
## The LDS base is a placeholder 0 with a relocation.

# PRE1-LABEL: <kernel_a>:
# PRE1:      s_lshl2_add_u32 s0, s0, lit(0x0)
# PRE1-NEXT:   {{.*}} R_AMDGPU_ABS32_LO __lds_shared
# PRE1:      ds_write_b32 v{{[0-9]+}}, v{{[0-9]+}}

## === Pre-link TU2: kernel_b ===
## Two LDS accesses: __lds_shared and __lds_private, both with relocations.

# PRE2-LABEL: <kernel_b>:
## First access: __lds_shared (s_add_i32 with relocation).
# PRE2:      s_add_i32 s{{[0-9]+}}, s0, lit(0x0)
# PRE2-NEXT:   {{.*}} R_AMDGPU_ABS32_LO __lds_shared
# PRE2:      ds_read_b32 v{{[0-9]+}}, v{{[0-9]+}}
## Second access: __lds_private (s_add_i32 with relocation).
# PRE2:      s_add_i32 s0, s0, lit(0x0)
# PRE2-NEXT:   {{.*}} R_AMDGPU_ABS32_LO __lds_private
# PRE2:      ds_write_b32 v{{[0-9]+}}, v{{[0-9]+}}
## Increment and write-back to __lds_shared.
# PRE2:      v_add_u32_e32 v{{[0-9]+}}, 1, v{{[0-9]+}}
# PRE2:      ds_write_b32 v{{[0-9]+}}, v{{[0-9]+}}

## === Post-link: resolved offsets ===

## kernel_a: __lds_shared resolved to offset 0.
# POST-LABEL: <kernel_a>:
# POST:      s_lshl2_add_u32 s0, s0, lit(0x0)
# POST:      ds_write_b32 v{{[0-9]+}}, v{{[0-9]+}}

## kernel_b: __lds_shared at offset 0, __lds_private at offset 0x100.
# POST-LABEL: <kernel_b>:
## __lds_shared base = 0 (unchanged from placeholder).
# POST:      s_add_i32 s{{[0-9]+}}, s0, lit(0x0)
# POST:      ds_read_b32 v{{[0-9]+}}, v{{[0-9]+}}
## __lds_private base = 0x100 (resolved from placeholder 0).
# POST:      s_add_i32 s0, s0, 0x100
# POST:      ds_write_b32 v{{[0-9]+}}, v{{[0-9]+}}
## Increment + write-back.
# POST:      v_add_u32_e32 v{{[0-9]+}}, 1, v{{[0-9]+}}
# POST:      ds_write_b32 v{{[0-9]+}}, v{{[0-9]+}}

#--- tu1.ll
@__lds_shared = external addrspace(3) global [64 x i32], align 16

define amdgpu_kernel void @kernel_a(i32 %idx) #0 {
  %gep = getelementptr [64 x i32], ptr addrspace(3) @__lds_shared, i32 0, i32 %idx
  store i32 42, ptr addrspace(3) %gep
  ret void
}

attributes #0 = { "amdgpu-link-time-lds" }

#--- tu2.ll
@__lds_private = external addrspace(3) global [32 x i32], align 4
@__lds_shared = external addrspace(3) global [64 x i32], align 16

define amdgpu_kernel void @kernel_b(i32 %idx) #0 {
  %gep1 = getelementptr [32 x i32], ptr addrspace(3) @__lds_private, i32 0, i32 %idx
  store i32 99, ptr addrspace(3) %gep1
  %gep2 = getelementptr [64 x i32], ptr addrspace(3) @__lds_shared, i32 0, i32 %idx
  %val = load i32, ptr addrspace(3) %gep2
  %sum = add i32 %val, 1
  store i32 %sum, ptr addrspace(3) %gep2
  ret void
}

attributes #0 = { "amdgpu-link-time-lds" }
