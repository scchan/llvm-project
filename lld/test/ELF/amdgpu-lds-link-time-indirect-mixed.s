# REQUIRES: amdgpu

## Test a function called both directly and indirectly. The LDS should be
## reachable through both paths. The kernel's LDS size should include the
## function's LDS regardless of which path discovers it.
##
## Call graph:
##   kern -> target_func (direct call)
##   kern -> caller --(indirect)--> target_func
##   target_func -> lds_var

# RUN: split-file %s %t
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/tu1.ll -o %t/tu1.o
# RUN: ld.lld %t/tu1.o -o %t/out
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

define void @caller(ptr %fptr, i32 %x) {
  call void %fptr(i32 %x)
  ret void
}

define amdgpu_kernel void @kern(i32 %x) {
  ; Direct call
  call void @target_func(i32 %x)
  ; Indirect call through function pointer
  call void @caller(ptr @target_func, i32 %x)
  ret void
}
