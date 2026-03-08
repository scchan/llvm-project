; RUN: opt -S -mtriple=amdgcn-amd-amdhsa -passes=amdgpu-lower-module-lds -amdgpu-enable-object-linking < %s | FileCheck %s

; Transitive call chain: kernel -> mid_func -> leaf_func.
; Only leaf_func uses LDS. mid_func calls an external. The LDS variable
; has external linkage -> global-scope -> standalone declaration.

@lds_var = addrspace(3) global [64 x i32] poison, align 16

declare void @extern_func()

; Global-scope: remains as external declaration.
; CHECK: @lds_var = external addrspace(3) global [64 x i32]
; No per-function struct.
; CHECK-NOT: @__amdgpu_lds.leaf_func

; CHECK-LABEL: define void @leaf_func()
; CHECK: getelementptr [64 x i32], ptr addrspace(3) @lds_var

; mid_func does not use LDS directly — should have no LDS struct.
; CHECK-LABEL: define void @mid_func()
; CHECK-NOT: @__amdgpu_lds.mid_func
; CHECK: call void @leaf_func()
; CHECK: call void @extern_func()

; CHECK-LABEL: define amdgpu_kernel void @top_kernel()
; CHECK: call void @mid_func()
; CHECK: attributes #{{[0-9]+}} {{.*}}"amdgpu-link-time-lds"

; Metadata: leaf_func uses lds_var.
; CHECK: !{ptr @leaf_func, ptr addrspace(3) @lds_var}

define void @leaf_func() {
  %gep = getelementptr [64 x i32], ptr addrspace(3) @lds_var, i32 0, i32 0
  store i32 42, ptr addrspace(3) %gep
  ret void
}

define void @mid_func() {
  call void @leaf_func()
  call void @extern_func()
  ret void
}

define amdgpu_kernel void @top_kernel() {
  call void @mid_func()
  ret void
}
