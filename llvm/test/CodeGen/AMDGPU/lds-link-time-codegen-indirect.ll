; RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -amdgpu-enable-lower-module-lds=0 -filetype=obj < %s | llvm-readobj -r --sections - | FileCheck %s

; Test that the .amdgpu.callgraph section includes address-taken, indirect
; call, and prototype entries for functions involved in indirect calling.
;
; @callee_vi: void(i32) -- address taken, prototype type ID (MD5 hash of FunctionType)
; @caller:    has indirect call to void(i32) -- icall type ID
; @my_kernel: kernel that passes @callee_vi as a function pointer to @caller

define void @callee_vi(i32 %x) {
  ret void
}

define void @caller(ptr %fptr) {
  call void %fptr(i32 1)
  ret void
}

define amdgpu_kernel void @my_kernel() #0 {
  call void @caller(ptr @callee_vi)
  ret void
}

attributes #0 = { "amdgpu-link-time-lds" }

; CHECK:      Section {
; CHECK:        Name: .amdgpu.callgraph
; CHECK:        Type: SHT_PROGBITS
; CHECK:        Flags [
; CHECK:          SHF_EXCLUDE
; CHECK:        ]

; Kernel entry + direct call + address-taken + indirect call + prototype.
; CHECK:      Section {{.*}} .rela.amdgpu.callgraph {
; CHECK-DAG:    R_AMDGPU_ABS64 my_kernel
; CHECK-DAG:    R_AMDGPU_ABS64 caller
; CHECK-DAG:    R_AMDGPU_ABS64 callee_vi
; CHECK-DAG:    R_AMDGPU_ABS64 __amdgpu_address_taken
; CHECK-DAG:    R_AMDGPU_ABS64 __amdgpu_icall.{{[0-9A-F]+}}
; CHECK-DAG:    R_AMDGPU_ABS64 __amdgpu_proto.{{[0-9A-F]+}}
; CHECK:      }
