; RUN: opt -S -mtriple=amdgcn-amd-amdhsa -passes=amdgpu-lower-module-lds -amdgpu-enable-object-linking < %s | FileCheck %s

; A single device function uses three external-linkage LDS variables with
; different sizes and alignments. All are global-scope -> standalone
; declarations (not wrapped into a struct).

@lds_small = addrspace(3) global [4 x i8] poison, align 1
@lds_medium = addrspace(3) global [64 x i32] poison, align 16
@lds_large = addrspace(3) global [128 x i64] poison, align 8

declare void @extern_func()

; All become external declarations.
; CHECK-DAG: @lds_small = external addrspace(3) global [4 x i8]
; CHECK-DAG: @lds_medium = external addrspace(3) global [64 x i32]
; CHECK-DAG: @lds_large = external addrspace(3) global [128 x i64]
; No per-function struct.
; CHECK-NOT: @__amdgpu_lds.device_func

; Uses remain as direct references.
; CHECK-LABEL: define void @device_func()
; CHECK: getelementptr [4 x i8], ptr addrspace(3) @lds_small
; CHECK: store
; CHECK: getelementptr [64 x i32], ptr addrspace(3) @lds_medium
; CHECK: store
; CHECK: getelementptr [128 x i64], ptr addrspace(3) @lds_large
; CHECK: store

; CHECK: attributes #{{[0-9]+}} {{.*}}"amdgpu-link-time-lds"

; Per-function metadata for each (function, variable) pair.
; CHECK-DAG: !{ptr @device_func, ptr addrspace(3) @lds_small}
; CHECK-DAG: !{ptr @device_func, ptr addrspace(3) @lds_medium}
; CHECK-DAG: !{ptr @device_func, ptr addrspace(3) @lds_large}

define void @device_func() {
  %gep1 = getelementptr [4 x i8], ptr addrspace(3) @lds_small, i32 0, i32 0
  store i8 1, ptr addrspace(3) %gep1
  %gep2 = getelementptr [64 x i32], ptr addrspace(3) @lds_medium, i32 0, i32 0
  store i32 2, ptr addrspace(3) %gep2
  %gep3 = getelementptr [128 x i64], ptr addrspace(3) @lds_large, i32 0, i32 0
  store i64 3, ptr addrspace(3) %gep3
  call void @extern_func()
  ret void
}

define amdgpu_kernel void @my_kernel() {
  call void @device_func()
  ret void
}
