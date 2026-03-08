; RUN: opt -S -mtriple=amdgcn-amd-amdhsa -amdgpu-lower-module-lds -amdgpu-enable-object-linking < %s | FileCheck %s
; RUN: opt -S -mtriple=amdgcn-amd-amdhsa -passes=amdgpu-lower-module-lds -amdgpu-enable-object-linking < %s | FileCheck %s

; Test that link-time LDS mode converts external-linkage LDS variables to
; standalone external declarations (global-scope LDS) instead of wrapping
; them into per-function structs.

@lds_a = addrspace(3) global [64 x i32] poison, align 16
@lds_b = addrspace(3) global [32 x float] poison, align 4

declare void @extern_func()

; Global-scope LDS variables become external declarations.
; CHECK-DAG: @lds_a = external addrspace(3) global [64 x i32]
; CHECK-DAG: @lds_b = external addrspace(3) global [32 x float]
; No per-function LDS structs (all variables are global-scope).
; CHECK-NOT: @__amdgpu_lds.device_func
; CHECK-NOT: @__amdgpu_lds.kernel_func

; Uses remain as direct references to the original variables.
; CHECK-LABEL: define void @device_func()
; CHECK: getelementptr [64 x i32], ptr addrspace(3) @lds_a
; CHECK: store i32 1, ptr addrspace(3) %gep

; CHECK-LABEL: define amdgpu_kernel void @kernel_func()
; CHECK: getelementptr [32 x float], ptr addrspace(3) @lds_b
; CHECK: store float 2.0{{.*}}, ptr addrspace(3) %gep

; Kernels should be marked with the link-time LDS attribute.
; CHECK: attributes #{{[0-9]+}} {{.*}}"amdgpu-link-time-lds"

; Per-function LDS ownership metadata for global-scope variables.
; CHECK-DAG: !{ptr @device_func, ptr addrspace(3) @lds_a}
; CHECK-DAG: !{ptr @kernel_func, ptr addrspace(3) @lds_b}

define void @device_func() {
  %gep = getelementptr [64 x i32], ptr addrspace(3) @lds_a, i32 0, i32 0
  store i32 1, ptr addrspace(3) %gep
  call void @extern_func()
  ret void
}

define amdgpu_kernel void @kernel_func() {
  %gep = getelementptr [32 x float], ptr addrspace(3) @lds_b, i32 0, i32 0
  store float 2.0, ptr addrspace(3) %gep
  call void @device_func()
  ret void
}
