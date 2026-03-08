; RUN: opt -S -mtriple=amdgcn-amd-amdhsa -passes=amdgpu-lower-module-lds -amdgpu-enable-object-linking < %s | FileCheck %s

; Only the kernel itself directly uses LDS (no device function uses LDS).
; The LDS variable has external linkage -> global-scope -> standalone declaration.

@lds_var = addrspace(3) global [32 x float] poison, align 4

declare void @extern_func()

; Global-scope: remains as external declaration.
; CHECK: @lds_var = external addrspace(3) global [32 x float]
; No per-function struct (variable is global-scope).
; CHECK-NOT: @__amdgpu_lds.my_kernel
; CHECK-NOT: @__amdgpu_lds.device_func

; CHECK-LABEL: define void @device_func()
; CHECK: call void @extern_func()

; CHECK-LABEL: define amdgpu_kernel void @my_kernel()
; CHECK: getelementptr [32 x float], ptr addrspace(3) @lds_var
; CHECK: call void @device_func()
; CHECK: attributes #{{[0-9]+}} {{.*}}"amdgpu-link-time-lds"

; Per-function LDS ownership metadata.
; CHECK: !{ptr @my_kernel, ptr addrspace(3) @lds_var}

define void @device_func() {
  call void @extern_func()
  ret void
}

define amdgpu_kernel void @my_kernel() {
  %gep = getelementptr [32 x float], ptr addrspace(3) @lds_var, i32 0, i32 0
  store float 1.0, ptr addrspace(3) %gep
  call void @device_func()
  ret void
}
