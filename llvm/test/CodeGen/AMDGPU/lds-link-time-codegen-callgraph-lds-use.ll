; RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj < %s | llvm-readobj -r --sections - | FileCheck %s

; Test that the .amdgpu.callgraph section includes LDS-use entries alongside
; kernel entries and call edges. The kernel directly uses an external-linkage
; LDS variable (global-scope), and calls a helper that calls an external.
;
; Expected entries in .amdgpu.callgraph:
;   - Kernel entry: (my_kernel, my_kernel)
;   - Call edges: (my_kernel, helper), (helper, extern_func)
;   - LDS-use entry: (my_kernel, lds_var) — global-scope, not wrapped in struct

@lds_var = addrspace(3) global [32 x float] poison, align 4

declare void @extern_func()

; CHECK:      Section {
; CHECK:        Name: .amdgpu.callgraph
; CHECK:        Type: SHT_PROGBITS
; CHECK:        Flags [
; CHECK:          SHF_EXCLUDE
; CHECK:        ]

; CHECK:      Section {{.*}} .rela.amdgpu.callgraph {
; CHECK-DAG:    R_AMDGPU_ABS64 my_kernel
; CHECK-DAG:    R_AMDGPU_ABS64 helper
; CHECK-DAG:    R_AMDGPU_ABS64 extern_func
; CHECK-DAG:    R_AMDGPU_ABS64 lds_var
; CHECK:      }

define void @helper() {
  call void @extern_func()
  ret void
}

define amdgpu_kernel void @my_kernel() {
  %gep = getelementptr [32 x float], ptr addrspace(3) @lds_var, i32 0, i32 0
  store float 1.0, ptr addrspace(3) %gep
  call void @helper()
  ret void
}
