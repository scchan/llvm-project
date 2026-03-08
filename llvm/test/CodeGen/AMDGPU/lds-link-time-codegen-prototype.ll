; RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -amdgpu-enable-lower-module-lds=0 -filetype=obj < %s | llvm-readobj -r - | FileCheck %s

; Test type ID generation for various function signatures. The type ID is
; the MD5 hash of the full LLVM IR FunctionType string, giving precise
; per-type matching (e.g. float(float) and i32(i32) get distinct IDs).

define void @void_void() {
  ret void
}

define i32 @i32_i32(i32 %x) {
  ret i32 %x
}

define void @void_ptr_i32(ptr %p, i32 %x) {
  ret void
}

define i64 @i64_i64_i64(i64 %a, i64 %b) {
  ret i64 %a
}

define float @float_float(float %x) {
  ret float %x
}

; Take the address of each function so they appear in the prototype metadata.
define void @taker() {
  %p0 = alloca ptr, addrspace(5)
  store volatile ptr @void_void, ptr addrspace(5) %p0
  store volatile ptr @i32_i32, ptr addrspace(5) %p0
  store volatile ptr @void_ptr_i32, ptr addrspace(5) %p0
  store volatile ptr @i64_i64_i64, ptr addrspace(5) %p0
  store volatile ptr @float_float, ptr addrspace(5) %p0
  ret void
}

define amdgpu_kernel void @kern() #0 {
  call void @taker()
  ret void
}

attributes #0 = { "amdgpu-link-time-lds" }

; All five address-taken functions have distinct FunctionTypes, so each gets
; a unique __amdgpu_proto.<hash> entry (float(float) and i32(i32) are now
; distinguished, unlike the old bit-width-based encoding).
; CHECK: .rela.amdgpu.callgraph {
; CHECK-DAG: R_AMDGPU_ABS64 __amdgpu_proto.{{[0-9A-F]+}}
; CHECK-DAG: R_AMDGPU_ABS64 __amdgpu_proto.{{[0-9A-F]+}}
; CHECK-DAG: R_AMDGPU_ABS64 __amdgpu_proto.{{[0-9A-F]+}}
; CHECK-DAG: R_AMDGPU_ABS64 __amdgpu_proto.{{[0-9A-F]+}}
; CHECK-DAG: R_AMDGPU_ABS64 __amdgpu_proto.{{[0-9A-F]+}}
; CHECK-DAG: R_AMDGPU_ABS64 __amdgpu_address_taken
; CHECK: }
