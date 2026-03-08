# REQUIRES: amdgpu

## Test link-time resource usage propagation for AMDGPU.
## The linker parses .amdgpu.resource_usage and .amdgpu.callgraph sections,
## propagates resource usage across the call graph, and patches the kernel
## descriptor and HSA metadata with the propagated values.

# RUN: split-file %s %t

## --- GFX900 test ---
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/a.ll -o %t/a.o
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/b.ll -o %t/b.o
# RUN: ld.lld %t/a.o %t/b.o -o %t/out

## Verify the linker patches HSA metadata after resource propagation.
# RUN: llvm-readobj --notes %t/out | FileCheck %s

## kernel calls helper (defined in b.ll). After propagation, the kernel's
## metadata should reflect the max of both functions' register usage.
# CHECK:      .name: kernel
# CHECK:      .sgpr_count:
# CHECK:      .vgpr_count:

## --- GFX90A test ---
## Test that on GFX90A the linker correctly accounts for extra SGPRs
## and uses the proper VGPR total computation (GFX90A alignment rule).
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx90a -amdgpu-enable-object-linking -filetype=obj %t/a90a.ll -o %t/a90a.o
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx90a -amdgpu-enable-object-linking -filetype=obj %t/b90a.ll -o %t/b90a.o
# RUN: ld.lld %t/a90a.o %t/b90a.o -o %t/out90a
# RUN: llvm-readobj --notes %t/out90a | FileCheck %s --check-prefix=GFX90A

## After propagation, the kernel should have SGPRs with extras accounted for
## and VGPR count from the callee.
# GFX90A:      .name: kernel90a
# GFX90A:      .sgpr_count:
# GFX90A:      .vgpr_count:

#--- a.ll
define amdgpu_kernel void @kernel(i32 %x) {
entry:
  call void @helper()
  ret void
}

declare void @helper()

#--- b.ll
define void @helper() {
entry:
  ret void
}

#--- a90a.ll
define amdgpu_kernel void @kernel90a(float %x) {
entry:
  call void @mfma_helper(float %x)
  ret void
}

declare void @mfma_helper(float)

#--- b90a.ll
define void @mfma_helper(float %x) {
entry:
  %v = call <4 x float> @llvm.amdgcn.mfma.f32.4x4x1f32(float %x, float %x, <4 x float> zeroinitializer, i32 0, i32 0, i32 0)
  %e = extractelement <4 x float> %v, i32 0
  call void asm sideeffect "", "~{v[0:7]}"()
  ret void
}

declare <4 x float> @llvm.amdgcn.mfma.f32.4x4x1f32(float, float, <4 x float>, i32 immarg, i32 immarg, i32 immarg)
