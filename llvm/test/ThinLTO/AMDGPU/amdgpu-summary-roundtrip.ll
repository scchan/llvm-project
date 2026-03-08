; Verify that the AMDGPU_SUMMARY block round-trips through bitcode.
; RUN: opt -mtriple=amdgcn-amd-amdhsa -module-summary %s -o %t.bc
; RUN: llvm-bcanalyzer -dump %t.bc | FileCheck %s --check-prefix=BLOCK

; BLOCK: <AMDGPU_SUMMARY_BLOCK
; BLOCK-NEXT: <AMDGPU_SUMMARY_VERSION op0=1/>
; BLOCK-NEXT: <AMDGPU_SUMMARY_ENTRY {{.*}} op1=1 op2=64 op3=256 op4=2 op5=8 op6=16 op7=16 op8=1/>
; BLOCK-NEXT: <AMDGPU_SUMMARY_ENTRY {{.*}} op1=0 op2=1 op3=1024 op4=1 op5=10
; BLOCK-NEXT: </AMDGPU_SUMMARY_BLOCK>

target datalayout = "e-p:64:64-p1:64:64-p2:32:32-p3:32:32-p4:64:64-p5:32:32-p6:32:32-p7:160:256:256:32-p8:128:128-p9:192:256:256:32-i64:64-v16:16-v24:32-v32:32-v48:64-v96:128-v192:256-v256:256-v512:512-v1024:1024-v2048:2048-n32:64-S32-A5-G1-ni:7:8:9"
target triple = "amdgcn-amd-amdhsa"

define amdgpu_kernel void @kernel(ptr %p) #0 {
  call void @device_func(ptr %p)
  ret void
}

define void @device_func(ptr %p) {
  store i32 42, ptr %p
  ret void
}

attributes #0 = { "amdgpu-flat-work-group-size"="64,256" "amdgpu-waves-per-eu"="2,8" "amdgpu-max-num-workgroups"="16,16,1" }
