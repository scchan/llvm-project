; RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx1250 -amdgpu-enable-object-linking < %s | FileCheck %s

; Verify object linking codegen for named barriers on GFX1250:
; 1. Barrier instructions use M0-based forms with relocation references
; 2. compute_pgm_rsrc3 NAMED_BAR_CNT = 0 (linker patches it)
; 3. Resource usage: NumNamedBarrier = 0
; 4. Call graph section contains __amdgpu_named_barrier entries
; 5. Named barrier is emitted as an SHN_AMDGPU_LDS symbol (.amdgpu_lds)

@bar = internal addrspace(3) global [2 x target("amdgcn.named.barrier", 0)] poison

; M0-based barrier forms using relocation
; CHECK-LABEL: kernel:
; CHECK:       bar@abs32@lo
; CHECK:       s_barrier_signal m0
; CHECK:       s_barrier_join m0
; CHECK:       s_barrier_wait 1

; kernel.kd: group_segment_fixed_size=0, private_segment_fixed_size=0
; CHECK-LABEL: kernel.kd:
; CHECK:       .long 0{{$}}
; CHECK-NEXT:  .long 0{{$}}

; NumNamedBarrier = 0 in resource usage
; CHECK:      .set kernel.num_named_barrier, 0

; Call graph entries include the named barrier marker
; CHECK:      .section .amdgpu.callgraph
; CHECK:      __amdgpu_named_barrier

; LDS symbol declaration
; CHECK:      .amdgpu_lds bar, 32, 4

define amdgpu_kernel void @kernel() {
  call void @llvm.amdgcn.s.barrier.signal.var(ptr addrspace(3) @bar, i32 3)
  call void @llvm.amdgcn.s.barrier.join(ptr addrspace(3) @bar)
  call void @llvm.amdgcn.s.barrier.wait(i16 1)
  call void @helper()
  ret void
}

declare void @helper()
declare void @llvm.amdgcn.s.barrier.signal.var(ptr addrspace(3), i32) #0
declare void @llvm.amdgcn.s.barrier.join(ptr addrspace(3)) #0
declare void @llvm.amdgcn.s.barrier.wait(i16) #0

attributes #0 = { convergent nounwind }
