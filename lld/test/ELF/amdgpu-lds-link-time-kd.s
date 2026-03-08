# REQUIRES: amdgpu

## Test that lld patches the kernel descriptor's group_segment_fixed_size field
## with the resolved per-kernel LDS size.

# RUN: split-file %s %t
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/a.ll -o %t/a.o
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/b.ll -o %t/b.o
# RUN: ld.lld %t/a.o %t/b.o -o %t/out

## Verify LDS symbol offset is assigned.
# RUN: llvm-readelf -s %t/out | FileCheck %s --check-prefix=SYM

## Verify group_segment_fixed_size in HSA metadata is patched to 256 (0x100).
# RUN: llvm-readobj --notes %t/out | FileCheck %s --check-prefix=META

## LDS layout:
##   lds_data: align=16, size=256 -> offset 0
## Total LDS = 256 = 0x100

# SYM: 0000000000000000 {{.*}} lds_data

# META: .group_segment_fixed_size: 256
# META: .name: my_kernel

#--- a.ll
@lds_data = addrspace(3) global [64 x i32] poison, align 16

declare void @helper()

define amdgpu_kernel void @my_kernel(i32 %idx) {
  %gep = getelementptr [64 x i32], ptr addrspace(3) @lds_data, i32 0, i32 %idx
  store i32 42, ptr addrspace(3) %gep
  call void @helper()
  ret void
}

#--- b.ll
define void @helper() {
  ret void
}
