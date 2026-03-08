# REQUIRES: amdgpu

## Test that the linker computes per-kernel LDS sizes correctly when
## kernels have disjoint LDS usage. With grouped allocation, independent
## kernel groups each allocate from offset 0.
##
## TU1: kernel_a uses lds_a (256 bytes, align 16)
## TU2: kernel_b uses lds_b (128 bytes, align 4)
##
## These are independent groups, so each allocates from offset 0:
##   Group 1: lds_a at offset 0 -> kernel_a size = 0x100
##   Group 2: lds_b at offset 0 -> kernel_b size = 0x080

# RUN: split-file %s %t
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/tu1.ll -o %t/tu1.o
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/tu2.ll -o %t/tu2.o

## Link.
# RUN: ld.lld %t/tu1.o %t/tu2.o -o %t/out

## Verify per-kernel LDS sizes via kernel descriptor patching and HSA metadata.
# RUN: llvm-readobj --notes %t/out | FileCheck %s

## kernel_a: lds_a at offset 0, size 256 -> group_segment_fixed_size = 256
# CHECK:      .group_segment_fixed_size: 256
# CHECK:      .name:           kernel_a

## kernel_b: lds_b at offset 0, size 128 -> group_segment_fixed_size = 128
# CHECK:      .group_segment_fixed_size: 128
# CHECK:      .name:           kernel_b

#--- tu1.ll
@lds_a = addrspace(3) global [64 x i32] poison, align 16

define amdgpu_kernel void @kernel_a(i32 %idx) {
  %gep = getelementptr [64 x i32], ptr addrspace(3) @lds_a, i32 0, i32 %idx
  store i32 42, ptr addrspace(3) %gep
  ret void
}

#--- tu2.ll
@lds_b = addrspace(3) global [32 x i32] poison, align 4

define amdgpu_kernel void @kernel_b(i32 %idx) {
  %gep = getelementptr [32 x i32], ptr addrspace(3) @lds_b, i32 0, i32 %idx
  store i32 99, ptr addrspace(3) %gep
  ret void
}
