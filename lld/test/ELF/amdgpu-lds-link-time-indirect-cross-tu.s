# REQUIRES: amdgpu

## Test cross-TU address-taken: the function is defined in TU1 but its address
## is taken in TU2. The linker should match the indirect call in TU2 with the
## function from TU1 via prototype matching.
##
## TU1: defines target_func (uses lds_var)
## TU2: defines kern which passes target_func as a pointer to caller
##      defines caller which makes an indirect call

# RUN: split-file %s %t
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/tu1.ll -o %t/tu1.o
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/tu2.ll -o %t/tu2.o
# RUN: ld.lld %t/tu1.o %t/tu2.o -o %t/out
# RUN: llvm-readobj --notes %t/out | FileCheck %s --check-prefix=META

## Kernel LDS size should include lds_var (128 bytes).
# META: .group_segment_fixed_size: 128

#--- tu1.ll
@lds_var = addrspace(3) global [32 x i32] poison, align 4

define void @target_func(i32 %x) {
  %p = getelementptr [32 x i32], ptr addrspace(3) @lds_var, i32 0, i32 %x
  store i32 42, ptr addrspace(3) %p
  ret void
}

#--- tu2.ll
declare void @target_func(i32)

define void @caller(ptr %fptr, i32 %x) {
  call void %fptr(i32 %x)
  ret void
}

define amdgpu_kernel void @kern(i32 %x) {
  call void @caller(ptr @target_func, i32 %x)
  ret void
}
