; RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -amdgpu-enable-lower-module-lds=0 -filetype=obj < %s | llvm-readobj -r --sections - | FileCheck %s

; Test that the .amdgpu.callgraph section is emitted with correct relocations
; when kernels have the "amdgpu-link-time-lds" attribute.
;
; The helper function does NOT use LDS (to avoid AMDGPUAlwaysInlinePass
; force-inlining it when -amdgpu-enable-lower-module-lds=0). It just calls
; an external function, which is sufficient to generate a call edge.

declare void @extern_func()

; The .amdgpu.callgraph section should exist with SHF_EXCLUDE.
; CHECK:      Section {
; CHECK:        Name: .amdgpu.callgraph
; CHECK:        Type: SHT_PROGBITS
; CHECK:        Flags [
; CHECK:          SHF_EXCLUDE
; CHECK:        ]

; Relocations for the callgraph section.
; Kernel entry is a self-referencing pair: (my_kernel, my_kernel).
; Call edges: (helper, extern_func), (my_kernel, helper).
; CHECK:      Section {{.*}} .rela.amdgpu.callgraph {
; CHECK-DAG:    R_AMDGPU_ABS64 my_kernel
; CHECK-DAG:    R_AMDGPU_ABS64 helper
; CHECK-DAG:    R_AMDGPU_ABS64 extern_func
; CHECK:      }

define void @helper() {
  call void @extern_func()
  ret void
}

define amdgpu_kernel void @my_kernel() #0 {
  call void @helper()
  ret void
}

attributes #0 = { "amdgpu-link-time-lds" }
