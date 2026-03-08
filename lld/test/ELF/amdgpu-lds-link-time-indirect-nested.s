# REQUIRES: amdgpu

## Test nested indirect calls (C++ virtual method pattern): an address-taken
## function itself makes an indirect call to another function. Both functions
## use LDS. The linker must discover all LDS through the indirect call chain
## and assign sequential non-overlapping offsets.
##
## Call graph:
##   kern -> caller --(indirect)--> outer_target --(indirect)--> inner_target
##   outer_target -> lds_outer (128 bytes)
##   inner_target -> lds_inner (64 bytes)
##
## Both indirect calls: void(i32) -> encoding "vi"
## Both targets are address-taken with encoding "vi"
##
## All LDS must be assigned unique offsets (no slot reuse).

# RUN: split-file %s %t
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/tu1.ll -o %t/tu1.o
# RUN: ld.lld %t/tu1.o -o %t/out
# RUN: llvm-readelf -s %t/out | FileCheck %s --check-prefix=SYM
# RUN: llvm-readobj --notes %t/out | FileCheck %s --check-prefix=META

## Both LDS variables resolved with non-overlapping offsets.
# SYM-DAG: {{[0-9a-f]+}} {{.*}} lds_outer
# SYM-DAG: {{[0-9a-f]+}} {{.*}} lds_inner

## Kernel LDS size includes both: lds_outer (128) + lds_inner (64) = 192.
# META: .group_segment_fixed_size: 192

#--- tu1.ll
@lds_outer = addrspace(3) global [32 x i32] poison, align 4
@lds_inner = addrspace(3) global [16 x i32] poison, align 4

define void @inner_target(i32 %x) {
  %p = getelementptr [16 x i32], ptr addrspace(3) @lds_inner, i32 0, i32 %x
  store i32 1, ptr addrspace(3) %p
  ret void
}

define void @outer_target(i32 %x) {
  %p = getelementptr [32 x i32], ptr addrspace(3) @lds_outer, i32 0, i32 %x
  store i32 2, ptr addrspace(3) %p
  call void @dispatch(ptr @inner_target, i32 %x)
  ret void
}

define void @dispatch(ptr %fptr, i32 %x) {
  call void %fptr(i32 %x)
  ret void
}

define void @caller(ptr %fptr, i32 %x) {
  call void %fptr(i32 %x)
  ret void
}

define amdgpu_kernel void @kern(i32 %x) {
  call void @caller(ptr @outer_target, i32 %x)
  ret void
}
