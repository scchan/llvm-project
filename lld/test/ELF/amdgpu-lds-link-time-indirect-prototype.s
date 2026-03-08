# REQUIRES: amdgpu

## Test prototype-based filtering: only address-taken functions matching the
## indirect call's prototype should be considered as potential callees.
##
## target_match: void(i32) -> encoding "vi" -- matches the indirect call
## target_nomatch: i32(i32, i32) -> encoding "iii" -- does NOT match
##
## Only lds_match should be reachable from the kernel through the indirect edge.
## lds_nomatch should NOT be reachable (its function has a different prototype).

# RUN: split-file %s %t
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/tu1.ll -o %t/tu1.o
# RUN: ld.lld %t/tu1.o -o %t/out
# RUN: llvm-readobj --notes %t/out | FileCheck %s --check-prefix=META

## Kernel's LDS size should only include lds_match (128 bytes), not lds_nomatch.
# META: .group_segment_fixed_size: 128

#--- tu1.ll
@lds_match = addrspace(3) global [32 x i32] poison, align 4
@lds_nomatch = addrspace(3) global [64 x i32] poison, align 4

define void @target_match(i32 %x) {
  %p = getelementptr [32 x i32], ptr addrspace(3) @lds_match, i32 0, i32 %x
  store i32 1, ptr addrspace(3) %p
  ret void
}

define i32 @target_nomatch(i32 %a, i32 %b) {
  %p = getelementptr [64 x i32], ptr addrspace(3) @lds_nomatch, i32 0, i32 %a
  store i32 2, ptr addrspace(3) %p
  ret i32 %a
}

; This indirect call has prototype void(i32) -> "vi", matching target_match only.
define void @caller(ptr %fptr, i32 %x) {
  call void %fptr(i32 %x)
  ret void
}

; Take address of both functions.
define void @addr_taker() {
  %p = alloca ptr, addrspace(5)
  store volatile ptr @target_match, ptr addrspace(5) %p
  store volatile ptr @target_nomatch, ptr addrspace(5) %p
  ret void
}

define amdgpu_kernel void @my_kernel(i32 %x) {
  call void @caller(ptr @target_match, i32 %x)
  call void @addr_taker()
  ret void
}
