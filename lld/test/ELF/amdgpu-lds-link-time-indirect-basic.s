# REQUIRES: amdgpu

## Test basic indirect call LDS resolution: kernel calls a function that makes
## an indirect call to an LDS-using function. The linker should discover the
## LDS variable through the indirect call edge (prototype matching) and assign
## it an offset. The kernel's LDS size should include the indirectly-reachable
## LDS.
##
## Call graph: my_kernel -> indirect_caller --(indirect)--> target_func -> lds_var
##
## target_func: void(i32) -> prototype encoding "vi"
## indirect_caller: makes indirect call with encoding "vi"
## target_func: address-taken (passed as ptr to indirect_caller)

# RUN: split-file %s %t
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/tu1.ll -o %t/tu1.o
# RUN: ld.lld %t/tu1.o -o %t/out
# RUN: llvm-readelf -s %t/out | FileCheck %s --check-prefix=SYM
# RUN: llvm-readobj --notes %t/out | FileCheck %s --check-prefix=META

## LDS variable should be resolved with an offset.
# SYM: 0000000000000000 {{.*}} lds_var

## Kernel descriptor should have non-zero LDS size (128 bytes for [32 x i32]).
# META: .group_segment_fixed_size: 128

#--- tu1.ll
@lds_var = addrspace(3) global [32 x i32] poison, align 4

define void @target_func(i32 %x) {
  %p = getelementptr [32 x i32], ptr addrspace(3) @lds_var, i32 0, i32 %x
  store i32 42, ptr addrspace(3) %p
  ret void
}

define void @indirect_caller(ptr %fptr, i32 %x) {
  call void %fptr(i32 %x)
  ret void
}

define amdgpu_kernel void @my_kernel(i32 %x) {
  call void @indirect_caller(ptr @target_func, i32 %x)
  ret void
}
