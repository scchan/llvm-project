# REQUIRES: amdgpu

## Test that resource usage (VGPR/SGPR/scratch) propagates correctly through
## indirect call edges. The kernel should pick up the resource requirements
## of the indirectly-called function.
##
## Call graph: kern -> caller --(indirect)--> heavy_func
## heavy_func uses significant VGPRs (via inline asm) and scratch.

# RUN: split-file %s %t
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/tu1.ll -o %t/tu1.o
# RUN: ld.lld %t/tu1.o -o %t/out
# RUN: llvm-readobj --notes %t/out | FileCheck %s --check-prefix=META

## The kernel should have non-trivial resource usage propagated from heavy_func.
## Check that private_segment_fixed_size is non-zero (scratch from heavy_func).
# META: .private_segment_fixed_size:
# META-NOT: .private_segment_fixed_size: 0

#--- tu1.ll
define void @heavy_func(i32 %x) {
  %buf = alloca [64 x i32], addrspace(5)
  %p = getelementptr [64 x i32], ptr addrspace(5) %buf, i32 0, i32 %x
  store volatile i32 %x, ptr addrspace(5) %p
  ret void
}

define void @caller(ptr %fptr, i32 %x) {
  call void %fptr(i32 %x)
  ret void
}

define amdgpu_kernel void @kern(i32 %x) {
  call void @caller(ptr @heavy_func, i32 %x)
  ret void
}
