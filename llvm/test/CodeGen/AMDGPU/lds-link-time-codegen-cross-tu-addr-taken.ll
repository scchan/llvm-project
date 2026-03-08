; RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -amdgpu-enable-lower-module-lds=0 -filetype=obj < %s | llvm-readobj -r - | FileCheck %s

; Test that address-taken on a declaration (cross-TU scenario) emits
; address-taken and prototype entries. The function is defined in another TU
; but its address is taken here.

declare void @external_func(i32)

define void @taker(ptr %p) {
  store ptr @external_func, ptr %p
  ret void
}

define amdgpu_kernel void @kern() #0 {
  %p = alloca ptr, addrspace(5)
  call void @taker(ptr addrspace(5) %p)
  ret void
}

attributes #0 = { "amdgpu-link-time-lds" }

; CHECK: .rela.amdgpu.callgraph {
; CHECK-DAG: R_AMDGPU_ABS64 external_func
; CHECK-DAG: R_AMDGPU_ABS64 __amdgpu_address_taken
; CHECK-DAG: R_AMDGPU_ABS64 __amdgpu_proto.{{[0-9A-F]+}}
; CHECK: }
