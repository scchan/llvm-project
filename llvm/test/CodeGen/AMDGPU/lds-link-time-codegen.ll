; RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-lower-module-lds=0 < %s | FileCheck -check-prefixes=ASM %s
; RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-lower-module-lds=0 -filetype=obj < %s | llvm-readobj -r --syms - | FileCheck -check-prefixes=ELF %s

; Test that on AMDHSA, external LDS declarations with the "amdgpu-link-time-lds"
; attribute produce @abs32@lo relocations, SHN_AMDGPU_LDS symbols, and a
; placeholder in HSA metadata — all driven purely by IR properties, without
; requiring the -amdgpu-enable-object-linking flag.
; The kernel descriptor uses a literal 0 for group_segment_fixed_size because
; the linker patches it via direct binary patching rather than a symbolic
; relocation.

@__amdgpu_lds.func = external addrspace(3) global [256 x i8], align 16

; ASM-LABEL: {{^}}test_kernel:
; ASM: __amdgpu_lds.func@abs32@lo
; ASM: .amdhsa_group_segment_fixed_size 0
; ASM: .globl __amdgpu_lds.func
; ASM: .amdgpu_lds __amdgpu_lds.func, 256, 16
; ASM: .group_segment_fixed_size: 0

; ELF:      Relocations [
; ELF:        Section {{.*}} .rela.text {
; ELF:          R_AMDGPU_ABS32_LO __amdgpu_lds.func
; ELF:        }
; ELF:      ]

; ELF:      Symbol {
; ELF:        Name: __amdgpu_lds.func
; ELF-NEXT:   Value: 0x10
; ELF-NEXT:   Size: 256
; ELF-NEXT:   Binding: Global
; ELF-NEXT:   Type: Object
; ELF-NEXT:   Other: 0
; ELF-NEXT:   Section: Processor Specific (0xFF00)
; ELF-NEXT: }

define amdgpu_kernel void @test_kernel(i32 %idx) #0 {
  %gep = getelementptr [256 x i8], ptr addrspace(3) @__amdgpu_lds.func, i32 0, i32 %idx
  store i8 42, ptr addrspace(3) %gep
  ret void
}

attributes #0 = { "amdgpu-link-time-lds" }
