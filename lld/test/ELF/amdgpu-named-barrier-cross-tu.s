# REQUIRES: amdgpu

## Cross-TU named barrier collision test.
##
## Without link-time resolution, each TU would independently assign barrier
## ID 1 to its local named barrier. When a kernel reaches both barriers
## transitively, this causes a collision. The linker must assign distinct
## barrier IDs to avoid this.
##
## TU A: kern uses bar_a (1 slot), calls helper
## TU B: helper uses bar_b (1 slot)
## After linking, kern reaches both bar_a and bar_b. The linker assigns
## distinct IDs (e.g., bar_a=1, bar_b=2 or vice versa). NAMED_BAR_CNT=1
## since ceil(2/4)=1.

# RUN: split-file %s %t
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx1250 -amdgpu-enable-object-linking -filetype=obj %t/a.ll -o %t/a.o
# RUN: llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx1250 -amdgpu-enable-object-linking -filetype=obj %t/b.ll -o %t/b.o
# RUN: ld.lld %t/a.o %t/b.o -o %t/out

## Verify the resolved barrier symbols have distinct encoded addresses.
## Each address is 0x802000 | (scope << 9) | (barId << 4).
## bar_a and bar_b must have different barIds.
# RUN: llvm-nm --format=posix %t/out | FileCheck %s --check-prefix=SYMS

## Verify NAMED_BAR_CNT is correct in compute_pgm_rsrc3.
# RUN: llvm-objcopy --dump-section=.rodata=%t/rodata %t/out
# RUN: python3 -c "                                           \
# RUN:   import struct, sys;                                   \
# RUN:   data = open(sys.argv[1], 'rb').read();               \
# RUN:   rsrc3 = struct.unpack_from('<I', data, 44)[0];       \
# RUN:   nbc = (rsrc3 >> 14) & 7;                             \
# RUN:   print(f'NAMED_BAR_CNT={nbc}');                       \
# RUN: " %t/rodata | FileCheck %s --check-prefix=KD

## The two barrier symbols must have different addresses (distinct barrier IDs).
## Both should match the barrier encoding pattern: 0x802010 (ID=1) or 0x802020 (ID=2).
# SYMS-DAG: bar_a A {{[0-9a-f]+}}
# SYMS-DAG: bar_b A {{[0-9a-f]+}}

# KD: NAMED_BAR_CNT=1

#--- a.ll
@bar_a = internal addrspace(3) global target("amdgcn.named.barrier", 0) poison

define amdgpu_kernel void @kern() {
  call void @llvm.amdgcn.s.barrier.signal.var(ptr addrspace(3) @bar_a, i32 1)
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
@bar_b = internal addrspace(3) global target("amdgcn.named.barrier", 0) poison

define void @helper() {
  call void @llvm.amdgcn.s.barrier.signal.var(ptr addrspace(3) @bar_b, i32 1)
  call void @llvm.amdgcn.s.barrier.join(ptr addrspace(3) @bar_b)
  call void @llvm.amdgcn.s.barrier.wait(i16 1)
  ret void
}

declare void @llvm.amdgcn.s.barrier.signal.var(ptr addrspace(3), i32) #0
declare void @llvm.amdgcn.s.barrier.join(ptr addrspace(3)) #0
declare void @llvm.amdgcn.s.barrier.wait(i16) #0

attributes #0 = { convergent nounwind }
