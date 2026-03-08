; RUN: opt -S -mtriple=amdgcn-amd-amdhsa -passes=amdgpu-lower-module-lds -amdgpu-enable-object-linking < %s | FileCheck %s

; No LDS variables in the module. The pass should be a no-op: no attribute
; is added and no LDS structs are created.

declare void @extern_func()

; CHECK-NOT: @__amdgpu_lds
; CHECK-NOT: "amdgpu-link-time-lds"

; CHECK-LABEL: define void @device_func(i32 %x)
; CHECK: call void @extern_func()

; CHECK-LABEL: define amdgpu_kernel void @my_kernel()
; CHECK: call void @device_func(i32 0)

define void @device_func(i32 %x) {
  call void @extern_func()
  ret void
}

define amdgpu_kernel void @my_kernel() {
  call void @device_func(i32 0)
  ret void
}
