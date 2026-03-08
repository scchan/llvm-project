; RUN: not --crash opt -S -mtriple=amdgcn-amd-amdhsa -passes=amdgpu-lower-module-lds -amdgpu-enable-object-linking < %s 2>&1 | FileCheck %s

; Dynamic LDS (extern __shared__ with zero size) is not supported with
; link-time LDS. The pass should report a fatal error when both regular
; and dynamic LDS are present.

@regular_lds = addrspace(3) global [64 x i32] poison, align 16
@dynamic_lds = external addrspace(3) global [0 x i32]

declare void @extern_func()

; CHECK: LLVM ERROR: dynamic LDS (extern __shared__) is not supported with -amdgpu-enable-object-linking

define amdgpu_kernel void @my_kernel() {
  %gep1 = getelementptr [64 x i32], ptr addrspace(3) @regular_lds, i32 0, i32 0
  store i32 1, ptr addrspace(3) %gep1
  %gep2 = getelementptr [0 x i32], ptr addrspace(3) @dynamic_lds, i32 0, i32 0
  store i32 2, ptr addrspace(3) %gep2
  call void @extern_func()
  ret void
}
