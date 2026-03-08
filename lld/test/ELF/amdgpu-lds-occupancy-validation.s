# REQUIRES: amdgpu

## Test link-time LDS-occupancy validation for AMDGPU.
## The backend computes the maximum LDS size and emits it as
## OccupancyLDSLimit in .amdgpu.resource_usage.
##
## - With explicit amdgpu-waves-per-eu: the limit is derived from occupancy:
##     wavesPerWG = ceil(flatWGSizeMax / waveSize)
##     minWGs     = ceil(wavesPerEUMin * eusPerCU / wavesPerWG)
##     limit      = totalLDS / minWGs
## - Without explicit amdgpu-waves-per-eu: the limit is the hardware LDS
##   size (totalLDS). Implicit occupancy is not enforced at link time because
##   per-TU implicit occupancy is stale once LDS from multiple TUs is combined.
##
## Target: gfx900 (totalLDS=65536, waveSize=64, eusPerCU=4)

# RUN: split-file %s %t

## --- Negative test: LDS too large for declared occupancy ---
## kernel_fail: waves-per-eu=8,10, flat-wg-size=1,1024
##   wavesPerWG = ceil(1024 / 64) = 16
##   minWGs     = ceil(8 * 4 / 16) = 2
##   limit      = 65536 / 2 = 32768
## Kernel uses 65536 bytes of LDS (> 32768) -> should error.
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/fail_k.ll -o %t/fail_k.o
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/fail_h.ll -o %t/fail_h.o
# RUN: not ld.lld %t/fail_k.o %t/fail_h.o -o /dev/null 2>&1 | FileCheck %s --check-prefix=FAIL

# FAIL: error: kernel 'kernel_fail': resolved LDS size (65536 bytes) exceeds the occupancy limit (32768 bytes)

## --- Positive test: LDS fits within occupancy budget ---
## kernel_pass: waves-per-eu=2,10, flat-wg-size=1,1024
##   wavesPerWG = ceil(1024 / 64) = 16
##   minWGs     = ceil(2 * 4 / 16) = 1
##   limit      = 65536 / 1 = 65536
## Kernel uses 4096 bytes of LDS (<= 65536) -> should pass.
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/pass_k.ll -o %t/pass_k.o
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/pass_h.ll -o %t/pass_h.o
# RUN: ld.lld %t/pass_k.o %t/pass_h.o -o %t/pass_out
# RUN: llvm-readobj --notes %t/pass_out | FileCheck %s --check-prefix=PASS

# PASS: .name: kernel_pass

## --- No-constraint test: kernel without amdgpu-waves-per-eu ---
## Without an explicit occupancy attribute, OccupancyLDSLimit = totalLDS
## (hardware limit = 65536). The kernel uses exactly 65536 bytes -> should pass.
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/noattr_k.ll -o %t/noattr_k.o
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/noattr_h.ll -o %t/noattr_h.o
# RUN: ld.lld %t/noattr_k.o %t/noattr_h.o -o %t/noattr_out
# RUN: llvm-readobj --notes %t/noattr_out | FileCheck %s --check-prefix=NOATTR

# NOATTR: .name: kernel_noattr

## --- Hardware-limit test: no explicit occupancy, LDS exceeds hardware ---
## Without amdgpu-waves-per-eu, OccupancyLDSLimit = 65536 (hardware limit).
## Kernel reaches two LDS symbols: 65536 bytes (kernel tier, align 16) and
## 4 bytes (shared tier, align 4). The shared tier is placed at offset 0,
## and the kernel tier at offset 16 (aligned), giving a total of 65552 bytes
## (> 65536) -> should error.
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/hwlimit_k.ll -o %t/hwlimit_k.o
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/hwlimit_f.ll -o %t/hwlimit_f.o
# RUN: not ld.lld %t/hwlimit_k.o %t/hwlimit_f.o -o /dev/null 2>&1 | FileCheck %s --check-prefix=HWLIMIT

# HWLIMIT: error: kernel 'kernel_hwlimit': resolved LDS size (65552 bytes) exceeds the occupancy limit (65536 bytes)

## --- Zero-LDS test: kernel with occupancy constraint but no LDS ---
## No LDS usage, so LDS cannot constrain occupancy -> should pass.
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/zerolds_k.ll -o %t/zerolds_k.o
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx900 -amdgpu-enable-object-linking -filetype=obj %t/zerolds_h.ll -o %t/zerolds_h.o
# RUN: ld.lld %t/zerolds_k.o %t/zerolds_h.o -o %t/zerolds_out
# RUN: llvm-readobj --notes %t/zerolds_out | FileCheck %s --check-prefix=ZEROLDS

# ZEROLDS: .name: kernel_zerolds

#--- fail_k.ll
@big_lds = addrspace(3) global [16384 x i32] poison, align 16

define amdgpu_kernel void @kernel_fail(i32 %idx) #0 {
  %gep = getelementptr [16384 x i32], ptr addrspace(3) @big_lds, i32 0, i32 %idx
  store i32 1, ptr addrspace(3) %gep
  call void @fail_helper()
  ret void
}

declare void @fail_helper()

attributes #0 = { "amdgpu-flat-work-group-size"="1,1024" "amdgpu-waves-per-eu"="8,10" }
#--- fail_h.ll
define void @fail_helper() {
  ret void
}
#--- pass_k.ll
@small_lds = addrspace(3) global [1024 x i32] poison, align 16

define amdgpu_kernel void @kernel_pass(i32 %idx) #0 {
  %gep = getelementptr [1024 x i32], ptr addrspace(3) @small_lds, i32 0, i32 %idx
  store i32 1, ptr addrspace(3) %gep
  call void @pass_helper()
  ret void
}

declare void @pass_helper()

attributes #0 = { "amdgpu-flat-work-group-size"="1,1024" "amdgpu-waves-per-eu"="2,10" }

#--- pass_h.ll
define void @pass_helper() {
  ret void
}
#--- noattr_k.ll
@noattr_lds = addrspace(3) global [16384 x i32] poison, align 16

define amdgpu_kernel void @kernel_noattr(i32 %idx) {
  %gep = getelementptr [16384 x i32], ptr addrspace(3) @noattr_lds, i32 0, i32 %idx
  store i32 1, ptr addrspace(3) %gep
  call void @noattr_helper()
  ret void
}

declare void @noattr_helper()

#--- noattr_h.ll
define void @noattr_helper() {
  ret void
}
#--- hwlimit_k.ll
@hwlimit_lds_a = addrspace(3) global [16384 x i32] poison, align 4

define amdgpu_kernel void @kernel_hwlimit(i32 %idx) {
  %gep = getelementptr [16384 x i32], ptr addrspace(3) @hwlimit_lds_a, i32 0, i32 %idx
  store i32 1, ptr addrspace(3) %gep
  call void @hwlimit_func()
  ret void
}

declare void @hwlimit_func()

#--- hwlimit_f.ll
@hwlimit_lds_b = addrspace(3) global [1 x i32] poison, align 4

define void @hwlimit_func() {
  store i32 2, ptr addrspace(3) @hwlimit_lds_b
  ret void
}
#--- zerolds_k.ll
define amdgpu_kernel void @kernel_zerolds(i32 %x) #0 {
  call void @zerolds_helper()
  ret void
}

declare void @zerolds_helper()

attributes #0 = { "amdgpu-flat-work-group-size"="1,1024" "amdgpu-waves-per-eu"="8,10" }

#--- zerolds_h.ll
define void @zerolds_helper() {
  ret void
}
