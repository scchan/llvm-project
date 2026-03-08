# REQUIRES: amdgpu

## Test indirect call with multiple potential callees. Two address-taken
## functions have the same prototype. Both should be considered potential
## callees of the indirect call site, and LDS from both should be reachable.
##
## Call graph:
##   my_kernel -> caller --(indirect)--> {target_a, target_b}
##   target_a -> lds_a (64 bytes)
##   target_b -> lds_b (32 bytes)
##
## Both targets: void(i32) -> encoding "vi"

# RUN: split-file %s %t
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/tu1.ll -o %t/tu1.o
# RUN: ld.lld %t/tu1.o -o %t/out
# RUN: llvm-readelf -s %t/out | FileCheck %s --check-prefix=SYM
# RUN: llvm-readobj --notes %t/out | FileCheck %s --check-prefix=META

## Both LDS variables should be resolved.
# SYM-DAG: {{[0-9a-f]+}} {{.*}} lds_a
# SYM-DAG: {{[0-9a-f]+}} {{.*}} lds_b

## Kernel's LDS size should include both lds_a (256 bytes) and lds_b (128 bytes).
## lds_a: align=4, size=256 -> offset 0, end 256
## lds_b: align=4, size=128 -> offset 256, end 384
# META: .group_segment_fixed_size: 384

#--- tu1.ll
@lds_a = addrspace(3) global [64 x i32] poison, align 4
@lds_b = addrspace(3) global [32 x i32] poison, align 4

define void @target_a(i32 %x) {
  %p = getelementptr [64 x i32], ptr addrspace(3) @lds_a, i32 0, i32 %x
  store i32 1, ptr addrspace(3) %p
  ret void
}

define void @target_b(i32 %x) {
  %p = getelementptr [32 x i32], ptr addrspace(3) @lds_b, i32 0, i32 %x
  store i32 2, ptr addrspace(3) %p
  ret void
}

define void @caller(ptr %fptr, i32 %x) {
  call void %fptr(i32 %x)
  ret void
}

define amdgpu_kernel void @my_kernel(i32 %x) {
  call void @caller(ptr @target_a, i32 %x)
  call void @caller(ptr @target_b, i32 %x)
  ret void
}
