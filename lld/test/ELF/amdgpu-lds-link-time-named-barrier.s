# REQUIRES: amdgpu

## Test that lld patches compute_pgm_rsrc3.NAMED_BAR_CNT with the cross-TU
## propagated named-barrier count for GFX1250.
##
## TU A: kern_a uses 1 named barrier, calls external helper.
## TU B: helper uses 5 named barriers, kern_b also uses 5.
## After linking, kern_a gets max(1, 5) = 5 barriers -> NamedBarCnt = ceil(5/4) = 2.
## NAMED_BAR_CNT occupies bits [14:16] of compute_pgm_rsrc3.
## Expected: 2 << 14 = 0x8000 for both kern_a and kern_b.

# RUN: split-file %s %t
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx1250 -amdgpu-enable-object-linking -filetype=obj %t/a.ll -o %t/a.o
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx1250 -amdgpu-enable-object-linking -filetype=obj %t/b.ll -o %t/b.o
# RUN: ld.lld %t/a.o %t/b.o -o %t/out

## Extract .rodata (contains 64-byte kernel descriptors) and check
## compute_pgm_rsrc3 at offset 44 from each KD start.
# RUN: llvm-objcopy --dump-section=.rodata=%t/rodata %t/out
# RUN: python3 -c "                                           \
# RUN:   import struct, sys;                                   \
# RUN:   data = open(sys.argv[1], 'rb').read();               \
# RUN:   rsrc3_a = struct.unpack_from('<I', data, 44)[0];     \
# RUN:   rsrc3_b = struct.unpack_from('<I', data, 108)[0];    \
# RUN:   nbc_a = (rsrc3_a >> 14) & 7;                         \
# RUN:   nbc_b = (rsrc3_b >> 14) & 7;                         \
# RUN:   print(f'NAMED_BAR_CNT_A={nbc_a}');                   \
# RUN:   print(f'NAMED_BAR_CNT_B={nbc_b}');                   \
# RUN: " %t/rodata | FileCheck %s

# CHECK: NAMED_BAR_CNT_A=2
# CHECK: NAMED_BAR_CNT_B=2

#--- a.ll
@bar_a = internal addrspace(3) global target("amdgcn.named.barrier", 0) poison

define amdgpu_kernel void @kern_a() {
  call void @llvm.amdgcn.s.barrier.signal.var(ptr addrspace(3) @bar_a, i32 3)
  call void @llvm.amdgcn.s.barrier.join(ptr addrspace(3) @bar_a)
  call void @llvm.amdgcn.s.barrier.wait(i16 1)
  call void @helper()
  ret void
}

declare void @helper()
declare void @llvm.amdgcn.s.barrier.signal.var(ptr addrspace(3), i32) #0
declare void @llvm.amdgcn.s.barrier.join(ptr addrspace(3)) #0
declare void @llvm.amdgcn.s.barrier.wait(i16) #0

attributes #0 = { convergent nounwind }

#--- b.ll
@bar_b = internal addrspace(3) global [5 x target("amdgcn.named.barrier", 0)] poison

define void @helper() {
  call void @llvm.amdgcn.s.barrier.signal.var(ptr addrspace(3) @bar_b, i32 5)
  call void @llvm.amdgcn.s.barrier.join(ptr addrspace(3) @bar_b)
  call void @llvm.amdgcn.s.barrier.wait(i16 1)
  ret void
}

define amdgpu_kernel void @kern_b() {
  call void @llvm.amdgcn.s.barrier.signal.var(ptr addrspace(3) @bar_b, i32 7)
  call void @llvm.amdgcn.s.barrier.join(ptr addrspace(3) @bar_b)
  call void @llvm.amdgcn.s.barrier.wait(i16 1)
  ret void
}

declare void @llvm.amdgcn.s.barrier.signal.var(ptr addrspace(3), i32) #0
declare void @llvm.amdgcn.s.barrier.join(ptr addrspace(3)) #0
declare void @llvm.amdgcn.s.barrier.wait(i16) #0

attributes #0 = { convergent nounwind }
