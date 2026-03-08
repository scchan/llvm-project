; RUN: opt -S -mtriple=amdgcn-amd-amdhsa -passes=amdgpu-lower-module-lds -amdgpu-enable-object-linking < %s | FileCheck %s

; Two kernels share a device function that uses LDS and calls an external.
; Each kernel also has its own external-linkage LDS variable.
; All variables are global-scope (external linkage) -> standalone declarations.

@lds_shared = addrspace(3) global [64 x i32] poison, align 16
@lds_kernel_a = addrspace(3) global [32 x float] poison, align 4
@lds_kernel_b = addrspace(3) global [16 x i64] poison, align 8

declare void @extern_func()

; All become external declarations.
; CHECK-DAG: @lds_shared = external addrspace(3) global [64 x i32]
; CHECK-DAG: @lds_kernel_a = external addrspace(3) global [32 x float]
; CHECK-DAG: @lds_kernel_b = external addrspace(3) global [16 x i64]
; No per-function structs.
; CHECK-NOT: @__amdgpu_lds.shared_func
; CHECK-NOT: @__amdgpu_lds.kernel_a
; CHECK-NOT: @__amdgpu_lds.kernel_b

; CHECK-LABEL: define void @shared_func()
; CHECK: getelementptr [64 x i32], ptr addrspace(3) @lds_shared
; CHECK: call void @extern_func()

; CHECK-LABEL: define amdgpu_kernel void @kernel_a()
; CHECK: getelementptr [32 x float], ptr addrspace(3) @lds_kernel_a
; CHECK: call void @shared_func()

; CHECK-LABEL: define amdgpu_kernel void @kernel_b()
; CHECK: getelementptr [16 x i64], ptr addrspace(3) @lds_kernel_b
; CHECK: call void @shared_func()

; Both kernels should be marked.
; CHECK-DAG: attributes #{{[0-9]+}} {{.*}}"amdgpu-link-time-lds"

; Per-function LDS ownership metadata for global-scope vars.
; CHECK-DAG: !{ptr @shared_func, ptr addrspace(3) @lds_shared}
; CHECK-DAG: !{ptr @kernel_a, ptr addrspace(3) @lds_kernel_a}
; CHECK-DAG: !{ptr @kernel_b, ptr addrspace(3) @lds_kernel_b}

define void @shared_func() {
  %gep = getelementptr [64 x i32], ptr addrspace(3) @lds_shared, i32 0, i32 0
  store i32 1, ptr addrspace(3) %gep
  call void @extern_func()
  ret void
}

define amdgpu_kernel void @kernel_a() {
  %gep = getelementptr [32 x float], ptr addrspace(3) @lds_kernel_a, i32 0, i32 0
  store float 1.0, ptr addrspace(3) %gep
  call void @shared_func()
  ret void
}

define amdgpu_kernel void @kernel_b() {
  %gep = getelementptr [16 x i64], ptr addrspace(3) @lds_kernel_b, i32 0, i32 0
  store i64 1, ptr addrspace(3) %gep
  call void @shared_func()
  ret void
}
