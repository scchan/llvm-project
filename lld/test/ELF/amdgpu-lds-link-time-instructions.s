# REQUIRES: amdgpu

## End-to-end instruction verification for link-time LDS resolution.
## Checks the full relocation-to-resolution flow:
##   1) Pre-link: object files contain R_AMDGPU_ABS32_LO relocations and
##      placeholder 0 literals in the load-address instructions.
##   2) Post-link: the linker patches those instructions with resolved offsets,
##      and the ds_read/ds_write instructions remain intact.
##
## LDS layout after linking (alignment desc, size desc):
##   lds_arr  (align=16, size=64) -> offset 0x00
##   lds_buf  (align=4,  size=32) -> offset 0x40
##
## TU a.s: kernel that writes lds_arr[idx] = 42 and reads lds_buf[idx].
## TU b.s: kernel that writes lds_buf[idx] = 99.

# RUN: split-file %s %t
# RUN: llvm-mc -filetype=obj -triple=amdgcn-amd-amdhsa -mcpu=gfx900 %t/a.s -o %t/a.o
# RUN: llvm-mc -filetype=obj -triple=amdgcn-amd-amdhsa -mcpu=gfx900 %t/b.s -o %t/b.o

## Pre-link: relocations in the object files.
# RUN: llvm-objdump -d -r %t/a.o | FileCheck %s --check-prefix=PRE-A
# RUN: llvm-objdump -d -r %t/b.o | FileCheck %s --check-prefix=PRE-B

## Link.
# RUN: ld.lld %t/a.o %t/b.o -o %t/out

## Post-link: resolved instructions in the linked binary.
# RUN: llvm-objdump -d %t/out | FileCheck %s --check-prefix=POST

## === Pre-link TU a: two LDS references (lds_arr and lds_buf) ===

# PRE-A-LABEL: <use_lds_a>:
## Load base of lds_arr — placeholder 0 with relocation.
# PRE-A:      s_mov_b32 s0, lit(0x0)
# PRE-A-NEXT:   {{.*}} R_AMDGPU_ABS32_LO lds_arr
## Compute byte address and store to LDS.
# PRE-A:      v_add_u32_e32 v1, s0, v0
# PRE-A:      ds_write_b8 v1, v2

## Load base of lds_buf — placeholder 0 with relocation.
# PRE-A:      s_mov_b32 s1, lit(0x0)
# PRE-A-NEXT:   {{.*}} R_AMDGPU_ABS32_LO lds_buf
## Compute byte address and read from LDS.
# PRE-A:      v_add_u32_e32 v0, s1, v0
# PRE-A:      ds_read_u8 v0, v0

## === Pre-link TU b: one LDS reference (lds_buf) ===

# PRE-B-LABEL: <use_lds_b>:
## Load base of lds_buf — placeholder 0 with relocation.
# PRE-B:      s_mov_b32 s0, lit(0x0)
# PRE-B-NEXT:   {{.*}} R_AMDGPU_ABS32_LO lds_buf
## Compute byte address and store to LDS.
# PRE-B:      v_add_u32_e32 v1, s0, v0
# PRE-B:      ds_write_b8 v1, v2

## === Post-link: relocated instructions resolved ===

## lds_arr at offset 0x00 — s_mov_b32 resolved to 0.
# POST-LABEL: <use_lds_a>:
# POST:      s_mov_b32 s0, lit(0x0)
# POST:      v_add_u32_e32 v1, s0, v0
# POST:      ds_write_b8 v1, v2
## lds_buf at offset 0x40 — s_mov_b32 patched to 0x40 (literal encoding).
# POST:      s_mov_b32 s1, lit(0x40)
# POST:      v_add_u32_e32 v0, s1, v0
# POST:      ds_read_u8 v0, v0

## In use_lds_b, lds_buf also resolved to 0x40 (same cross-TU symbol).
# POST-LABEL: <use_lds_b>:
# POST:      s_mov_b32 s0, lit(0x40)
# POST:      v_add_u32_e32 v1, s0, v0
# POST:      ds_write_b8 v1, v2

#--- a.s
	.text
	.globl use_lds_a
	.p2align 8
	.type use_lds_a,@function
use_lds_a:
	; Load base address of lds_arr (relocation target).
	s_mov_b32 s0, lds_arr@abs32@lo
	; v0 = byte index (from caller), compute lds_arr + idx.
	v_add_u32_e32 v1, s0, v0
	; Store i8 42 to lds_arr[idx].
	v_mov_b32_e32 v2, 42
	ds_write_b8 v1, v2

	; Load base address of lds_buf (relocation target).
	s_mov_b32 s1, lds_buf@abs32@lo
	; Compute lds_buf + idx.
	v_add_u32_e32 v0, s1, v0
	; Load i8 from lds_buf[idx].
	ds_read_u8 v0, v0
	s_endpgm
.Luse_lds_a_end:
	.size use_lds_a, .Luse_lds_a_end-use_lds_a

	.globl lds_arr
	.amdgpu_lds lds_arr, 64, 16

#--- b.s
	.text
	.globl use_lds_b
	.p2align 8
	.type use_lds_b,@function
use_lds_b:
	; Load base address of lds_buf (relocation target).
	s_mov_b32 s0, lds_buf@abs32@lo
	; Compute lds_buf + idx.
	v_add_u32_e32 v1, s0, v0
	; Store i8 99 to lds_buf[idx].
	v_mov_b32_e32 v2, 99
	ds_write_b8 v1, v2
	s_endpgm
.Luse_lds_b_end:
	.size use_lds_b, .Luse_lds_b_end-use_lds_b

	.globl lds_buf
	.amdgpu_lds lds_buf, 32, 4
