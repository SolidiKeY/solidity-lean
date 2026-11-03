import Solidity.Yul.Words

set_option Elab.async false

/-! Kernel controls generated from integer-oracle vectors (generator not on master).
Integer-oracle vectors are finite tests, not universal opcode agreement proofs. -/
namespace Solidity.Yul.Checks.Bytes

theorem v0000 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 0 else word 0)).val = 0 := by decide +kernel
theorem v0001 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 0 else word 1)).val = 0 := by decide +kernel
theorem v0002 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 0 else word 2)).val = 0 := by decide +kernel
theorem v0003 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 0 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 127 := by decide +kernel
theorem v0004 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 0 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 128 := by decide +kernel
theorem v0005 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 0 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 128 := by decide +kernel
theorem v0006 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 0 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0007 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 0 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0008 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 0 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 0 := by decide +kernel
theorem v0009 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 0 else word 0)).val = 0 := by decide +kernel
theorem v0010 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 0 else word 1)).val = 1 := by decide +kernel
theorem v0011 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 0 else word 2)).val = 2 := by decide +kernel
theorem v0012 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 0 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0013 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 0 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0014 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 0 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0015 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 0 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0016 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 0 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0017 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 0 else word 127)).val = 127 := by decide +kernel
theorem v0018 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 0 else word 128)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639808 := by decide +kernel
theorem v0019 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 0 else word 129)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639809 := by decide +kernel
theorem v0020 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 1 else word 0)).val = 0 := by decide +kernel
theorem v0021 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 1 else word 1)).val = 0 := by decide +kernel
theorem v0022 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 1 else word 2)).val = 0 := by decide +kernel
theorem v0023 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 1 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0024 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 1 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0025 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 1 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0026 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 1 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0027 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 1 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0028 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 1 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 1 := by decide +kernel
theorem v0029 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 1 else word 0)).val = 0 := by decide +kernel
theorem v0030 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 1 else word 1)).val = 1 := by decide +kernel
theorem v0031 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 1 else word 2)).val = 2 := by decide +kernel
theorem v0032 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 1 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0033 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 1 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0034 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 1 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0035 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 1 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0036 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 1 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0037 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 1 else word 32767)).val = 32767 := by decide +kernel
theorem v0038 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 1 else word 32768)).val = 115792089237316195423570985008687907853269984665640564039457584007913129607168 := by decide +kernel
theorem v0039 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 1 else word 32769)).val = 115792089237316195423570985008687907853269984665640564039457584007913129607169 := by decide +kernel
theorem v0040 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 2 else word 0)).val = 0 := by decide +kernel
theorem v0041 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 2 else word 1)).val = 0 := by decide +kernel
theorem v0042 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 2 else word 2)).val = 0 := by decide +kernel
theorem v0043 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 2 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0044 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 2 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0045 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 2 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0046 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 2 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0047 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 2 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0048 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 2 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 2 := by decide +kernel
theorem v0049 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 2 else word 0)).val = 0 := by decide +kernel
theorem v0050 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 2 else word 1)).val = 1 := by decide +kernel
theorem v0051 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 2 else word 2)).val = 2 := by decide +kernel
theorem v0052 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 2 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0053 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 2 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0054 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 2 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0055 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 2 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0056 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 2 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0057 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 2 else word 8388607)).val = 8388607 := by decide +kernel
theorem v0058 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 2 else word 8388608)).val = 115792089237316195423570985008687907853269984665640564039457584007913121251328 := by decide +kernel
theorem v0059 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 2 else word 8388609)).val = 115792089237316195423570985008687907853269984665640564039457584007913121251329 := by decide +kernel
theorem v0060 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 3 else word 0)).val = 0 := by decide +kernel
theorem v0061 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 3 else word 1)).val = 0 := by decide +kernel
theorem v0062 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 3 else word 2)).val = 0 := by decide +kernel
theorem v0063 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 3 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0064 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 3 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0065 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 3 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0066 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 3 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0067 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 3 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0068 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 3 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 3 := by decide +kernel
theorem v0069 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 3 else word 0)).val = 0 := by decide +kernel
theorem v0070 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 3 else word 1)).val = 1 := by decide +kernel
theorem v0071 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 3 else word 2)).val = 2 := by decide +kernel
theorem v0072 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 3 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0073 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 3 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0074 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 3 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0075 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 3 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0076 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 3 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0077 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 3 else word 2147483647)).val = 2147483647 := by decide +kernel
theorem v0078 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 3 else word 2147483648)).val = 115792089237316195423570985008687907853269984665640564039457584007910982156288 := by decide +kernel
theorem v0079 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 3 else word 2147483649)).val = 115792089237316195423570985008687907853269984665640564039457584007910982156289 := by decide +kernel
theorem v0080 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 4 else word 0)).val = 0 := by decide +kernel
theorem v0081 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 4 else word 1)).val = 0 := by decide +kernel
theorem v0082 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 4 else word 2)).val = 0 := by decide +kernel
theorem v0083 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 4 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0084 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 4 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0085 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 4 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0086 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 4 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0087 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 4 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0088 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 4 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 4 := by decide +kernel
theorem v0089 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 4 else word 0)).val = 0 := by decide +kernel
theorem v0090 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 4 else word 1)).val = 1 := by decide +kernel
theorem v0091 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 4 else word 2)).val = 2 := by decide +kernel
theorem v0092 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 4 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0093 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 4 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0094 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 4 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0095 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 4 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0096 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 4 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0097 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 4 else word 549755813887)).val = 549755813887 := by decide +kernel
theorem v0098 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 4 else word 549755813888)).val = 115792089237316195423570985008687907853269984665640564039457584007363373826048 := by decide +kernel
theorem v0099 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 4 else word 549755813889)).val = 115792089237316195423570985008687907853269984665640564039457584007363373826049 := by decide +kernel
theorem v0100 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 5 else word 0)).val = 0 := by decide +kernel
theorem v0101 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 5 else word 1)).val = 0 := by decide +kernel
theorem v0102 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 5 else word 2)).val = 0 := by decide +kernel
theorem v0103 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 5 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0104 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 5 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0105 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 5 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0106 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 5 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0107 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 5 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0108 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 5 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 5 := by decide +kernel
theorem v0109 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 5 else word 0)).val = 0 := by decide +kernel
theorem v0110 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 5 else word 1)).val = 1 := by decide +kernel
theorem v0111 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 5 else word 2)).val = 2 := by decide +kernel
theorem v0112 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 5 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0113 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 5 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0114 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 5 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0115 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 5 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0116 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 5 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0117 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 5 else word 140737488355327)).val = 140737488355327 := by decide +kernel
theorem v0118 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 5 else word 140737488355328)).val = 115792089237316195423570985008687907853269984665640564039457583867175641284608 := by decide +kernel
theorem v0119 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 5 else word 140737488355329)).val = 115792089237316195423570985008687907853269984665640564039457583867175641284609 := by decide +kernel
theorem v0120 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 6 else word 0)).val = 0 := by decide +kernel
theorem v0121 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 6 else word 1)).val = 0 := by decide +kernel
theorem v0122 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 6 else word 2)).val = 0 := by decide +kernel
theorem v0123 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 6 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0124 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 6 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0125 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 6 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0126 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 6 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0127 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 6 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0128 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 6 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 6 := by decide +kernel
theorem v0129 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 6 else word 0)).val = 0 := by decide +kernel
theorem v0130 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 6 else word 1)).val = 1 := by decide +kernel
theorem v0131 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 6 else word 2)).val = 2 := by decide +kernel
theorem v0132 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 6 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0133 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 6 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0134 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 6 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0135 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 6 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0136 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 6 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0137 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 6 else word 36028797018963967)).val = 36028797018963967 := by decide +kernel
theorem v0138 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 6 else word 36028797018963968)).val = 115792089237316195423570985008687907853269984665640564039457547979116110675968 := by decide +kernel
theorem v0139 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 6 else word 36028797018963969)).val = 115792089237316195423570985008687907853269984665640564039457547979116110675969 := by decide +kernel
theorem v0140 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 7 else word 0)).val = 0 := by decide +kernel
theorem v0141 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 7 else word 1)).val = 0 := by decide +kernel
theorem v0142 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 7 else word 2)).val = 0 := by decide +kernel
theorem v0143 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 7 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0144 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 7 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0145 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 7 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0146 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 7 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0147 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 7 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0148 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 7 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 7 := by decide +kernel
theorem v0149 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 7 else word 0)).val = 0 := by decide +kernel
theorem v0150 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 7 else word 1)).val = 1 := by decide +kernel
theorem v0151 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 7 else word 2)).val = 2 := by decide +kernel
theorem v0152 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 7 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0153 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 7 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0154 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 7 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0155 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 7 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0156 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 7 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0157 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 7 else word 9223372036854775807)).val = 9223372036854775807 := by decide +kernel
theorem v0158 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 7 else word 9223372036854775808)).val = 115792089237316195423570985008687907853269984665640564039448360635876274864128 := by decide +kernel
theorem v0159 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 7 else word 9223372036854775809)).val = 115792089237316195423570985008687907853269984665640564039448360635876274864129 := by decide +kernel
theorem v0160 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 8 else word 0)).val = 0 := by decide +kernel
theorem v0161 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 8 else word 1)).val = 0 := by decide +kernel
theorem v0162 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 8 else word 2)).val = 0 := by decide +kernel
theorem v0163 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 8 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0164 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 8 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0165 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 8 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0166 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 8 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0167 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 8 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0168 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 8 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 8 := by decide +kernel
theorem v0169 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 8 else word 0)).val = 0 := by decide +kernel
theorem v0170 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 8 else word 1)).val = 1 := by decide +kernel
theorem v0171 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 8 else word 2)).val = 2 := by decide +kernel
theorem v0172 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 8 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0173 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 8 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0174 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 8 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0175 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 8 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0176 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 8 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0177 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 8 else word 2361183241434822606847)).val = 2361183241434822606847 := by decide +kernel
theorem v0178 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 8 else word 2361183241434822606848)).val = 115792089237316195423570985008687907853269984665640564037096400766478307033088 := by decide +kernel
theorem v0179 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 8 else word 2361183241434822606849)).val = 115792089237316195423570985008687907853269984665640564037096400766478307033089 := by decide +kernel
theorem v0180 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 9 else word 0)).val = 0 := by decide +kernel
theorem v0181 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 9 else word 1)).val = 0 := by decide +kernel
theorem v0182 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 9 else word 2)).val = 0 := by decide +kernel
theorem v0183 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 9 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0184 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 9 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0185 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 9 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0186 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 9 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0187 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 9 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0188 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 9 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 9 := by decide +kernel
theorem v0189 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 9 else word 0)).val = 0 := by decide +kernel
theorem v0190 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 9 else word 1)).val = 1 := by decide +kernel
theorem v0191 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 9 else word 2)).val = 2 := by decide +kernel
theorem v0192 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 9 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0193 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 9 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0194 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 9 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0195 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 9 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0196 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 9 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0197 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 9 else word 604462909807314587353087)).val = 604462909807314587353087 := by decide +kernel
theorem v0198 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 9 else word 604462909807314587353088)).val = 115792089237316195423570985008687907853269984665640563434994674200598542286848 := by decide +kernel
theorem v0199 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 9 else word 604462909807314587353089)).val = 115792089237316195423570985008687907853269984665640563434994674200598542286849 := by decide +kernel
theorem v0200 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 10 else word 0)).val = 0 := by decide +kernel
theorem v0201 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 10 else word 1)).val = 0 := by decide +kernel
theorem v0202 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 10 else word 2)).val = 0 := by decide +kernel
theorem v0203 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 10 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0204 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 10 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0205 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 10 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0206 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 10 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0207 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 10 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0208 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 10 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 10 := by decide +kernel
theorem v0209 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 10 else word 0)).val = 0 := by decide +kernel
theorem v0210 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 10 else word 1)).val = 1 := by decide +kernel
theorem v0211 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 10 else word 2)).val = 2 := by decide +kernel
theorem v0212 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 10 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0213 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 10 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0214 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 10 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0215 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 10 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0216 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 10 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0217 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 10 else word 154742504910672534362390527)).val = 154742504910672534362390527 := by decide +kernel
theorem v0218 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 10 else word 154742504910672534362390528)).val = 115792089237316195423570985008687907853269984665640409296952673335378767249408 := by decide +kernel
theorem v0219 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 10 else word 154742504910672534362390529)).val = 115792089237316195423570985008687907853269984665640409296952673335378767249409 := by decide +kernel
theorem v0220 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 11 else word 0)).val = 0 := by decide +kernel
theorem v0221 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 11 else word 1)).val = 0 := by decide +kernel
theorem v0222 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 11 else word 2)).val = 0 := by decide +kernel
theorem v0223 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 11 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0224 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 11 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0225 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 11 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0226 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 11 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0227 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 11 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0228 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 11 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 11 := by decide +kernel
theorem v0229 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 11 else word 0)).val = 0 := by decide +kernel
theorem v0230 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 11 else word 1)).val = 1 := by decide +kernel
theorem v0231 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 11 else word 2)).val = 2 := by decide +kernel
theorem v0232 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 11 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0233 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 11 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0234 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 11 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0235 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 11 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0236 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 11 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0237 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 11 else word 39614081257132168796771975167)).val = 39614081257132168796771975167 := by decide +kernel
theorem v0238 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 11 else word 39614081257132168796771975168)).val = 115792089237316195423570985008687907853269984665600949958200451839116357664768 := by decide +kernel
theorem v0239 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 11 else word 39614081257132168796771975169)).val = 115792089237316195423570985008687907853269984665600949958200451839116357664769 := by decide +kernel
theorem v0240 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 12 else word 0)).val = 0 := by decide +kernel
theorem v0241 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 12 else word 1)).val = 0 := by decide +kernel
theorem v0242 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 12 else word 2)).val = 0 := by decide +kernel
theorem v0243 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 12 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0244 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 12 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0245 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 12 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0246 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 12 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0247 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 12 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0248 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 12 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 12 := by decide +kernel
theorem v0249 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 12 else word 0)).val = 0 := by decide +kernel
theorem v0250 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 12 else word 1)).val = 1 := by decide +kernel
theorem v0251 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 12 else word 2)).val = 2 := by decide +kernel
theorem v0252 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 12 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0253 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 12 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0254 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 12 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0255 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 12 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0256 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 12 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0257 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 12 else word 10141204801825835211973625643007)).val = 10141204801825835211973625643007 := by decide +kernel
theorem v0258 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 12 else word 10141204801825835211973625643008)).val = 115792089237316195423570985008687907853269984655499359237631748795939503996928 := by decide +kernel
theorem v0259 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 12 else word 10141204801825835211973625643009)).val = 115792089237316195423570985008687907853269984655499359237631748795939503996929 := by decide +kernel
theorem v0260 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 13 else word 0)).val = 0 := by decide +kernel
theorem v0261 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 13 else word 1)).val = 0 := by decide +kernel
theorem v0262 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 13 else word 2)).val = 0 := by decide +kernel
theorem v0263 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 13 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0264 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 13 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0265 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 13 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0266 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 13 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0267 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 13 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0268 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 13 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 13 := by decide +kernel
theorem v0269 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 13 else word 0)).val = 0 := by decide +kernel
theorem v0270 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 13 else word 1)).val = 1 := by decide +kernel
theorem v0271 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 13 else word 2)).val = 2 := by decide +kernel
theorem v0272 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 13 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0273 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 13 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0274 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 13 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0275 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 13 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0276 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 13 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0277 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 13 else word 2596148429267413814265248164610047)).val = 2596148429267413814265248164610047 := by decide +kernel
theorem v0278 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 13 else word 2596148429267413814265248164610048)).val = 115792089237316195423570985008687907853269982069492134772043769742664965029888 := by decide +kernel
theorem v0279 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 13 else word 2596148429267413814265248164610049)).val = 115792089237316195423570985008687907853269982069492134772043769742664965029889 := by decide +kernel
theorem v0280 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 14 else word 0)).val = 0 := by decide +kernel
theorem v0281 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 14 else word 1)).val = 0 := by decide +kernel
theorem v0282 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 14 else word 2)).val = 0 := by decide +kernel
theorem v0283 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 14 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0284 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 14 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0285 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 14 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0286 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 14 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0287 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 14 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0288 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 14 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 14 := by decide +kernel
theorem v0289 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 14 else word 0)).val = 0 := by decide +kernel
theorem v0290 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 14 else word 1)).val = 1 := by decide +kernel
theorem v0291 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 14 else word 2)).val = 2 := by decide +kernel
theorem v0292 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 14 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0293 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 14 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0294 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 14 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0295 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 14 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0296 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 14 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0297 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 14 else word 664613997892457936451903530140172287)).val = 664613997892457936451903530140172287 := by decide +kernel
theorem v0298 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 14 else word 664613997892457936451903530140172288)).val = 115792089237316195423570985008687907853269320051642671581521132104382989467648 := by decide +kernel
theorem v0299 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 14 else word 664613997892457936451903530140172289)).val = 115792089237316195423570985008687907853269320051642671581521132104382989467649 := by decide +kernel
theorem v0300 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 15 else word 0)).val = 0 := by decide +kernel
theorem v0301 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 15 else word 1)).val = 0 := by decide +kernel
theorem v0302 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 15 else word 2)).val = 0 := by decide +kernel
theorem v0303 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 15 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0304 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 15 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0305 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 15 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0306 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 15 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0307 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 15 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0308 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 15 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 15 := by decide +kernel
theorem v0309 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 15 else word 0)).val = 0 := by decide +kernel
theorem v0310 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 15 else word 1)).val = 1 := by decide +kernel
theorem v0311 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 15 else word 2)).val = 2 := by decide +kernel
theorem v0312 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 15 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0313 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 15 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0314 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 15 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0315 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 15 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0316 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 15 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0317 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 15 else word 170141183460469231731687303715884105727)).val = 170141183460469231731687303715884105727 := by decide +kernel
theorem v0318 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 15 else word 170141183460469231731687303715884105728)).val = 115792089237316195423570985008687907853099843482180094807725896704197245534208 := by decide +kernel
theorem v0319 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 15 else word 170141183460469231731687303715884105729)).val = 115792089237316195423570985008687907853099843482180094807725896704197245534209 := by decide +kernel
theorem v0320 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 16 else word 0)).val = 0 := by decide +kernel
theorem v0321 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 16 else word 1)).val = 0 := by decide +kernel
theorem v0322 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 16 else word 2)).val = 0 := by decide +kernel
theorem v0323 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 16 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0324 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 16 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0325 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 16 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0326 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 16 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0327 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 16 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0328 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 16 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 16 := by decide +kernel
theorem v0329 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 16 else word 0)).val = 0 := by decide +kernel
theorem v0330 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 16 else word 1)).val = 1 := by decide +kernel
theorem v0331 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 16 else word 2)).val = 2 := by decide +kernel
theorem v0332 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 16 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0333 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 16 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0334 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 16 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0335 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 16 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0336 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 16 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0337 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 16 else word 43556142965880123323311949751266331066367)).val = 43556142965880123323311949751266331066367 := by decide +kernel
theorem v0338 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 16 else word 43556142965880123323311949751266331066368)).val = 115792089237316195423570985008687907809713841699760440716145634256646798573568 := by decide +kernel
theorem v0339 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 16 else word 43556142965880123323311949751266331066369)).val = 115792089237316195423570985008687907809713841699760440716145634256646798573569 := by decide +kernel
theorem v0340 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 17 else word 0)).val = 0 := by decide +kernel
theorem v0341 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 17 else word 1)).val = 0 := by decide +kernel
theorem v0342 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 17 else word 2)).val = 0 := by decide +kernel
theorem v0343 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 17 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0344 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 17 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0345 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 17 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0346 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 17 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0347 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 17 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0348 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 17 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 17 := by decide +kernel
theorem v0349 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 17 else word 0)).val = 0 := by decide +kernel
theorem v0350 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 17 else word 1)).val = 1 := by decide +kernel
theorem v0351 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 17 else word 2)).val = 2 := by decide +kernel
theorem v0352 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 17 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0353 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 17 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0354 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 17 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0355 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 17 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0356 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 17 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0357 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 17 else word 11150372599265311570767859136324180752990207)).val = 11150372599265311570767859136324180752990207 := by decide +kernel
theorem v0358 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 17 else word 11150372599265311570767859136324180752990208)).val = 115792089237316195423570985008687896702897385400328993271598447683732376649728 := by decide +kernel
theorem v0359 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 17 else word 11150372599265311570767859136324180752990209)).val = 115792089237316195423570985008687896702897385400328993271598447683732376649729 := by decide +kernel
theorem v0360 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 18 else word 0)).val = 0 := by decide +kernel
theorem v0361 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 18 else word 1)).val = 0 := by decide +kernel
theorem v0362 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 18 else word 2)).val = 0 := by decide +kernel
theorem v0363 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 18 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0364 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 18 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0365 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 18 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0366 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 18 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0367 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 18 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0368 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 18 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 18 := by decide +kernel
theorem v0369 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 18 else word 0)).val = 0 := by decide +kernel
theorem v0370 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 18 else word 1)).val = 1 := by decide +kernel
theorem v0371 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 18 else word 2)).val = 2 := by decide +kernel
theorem v0372 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 18 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0373 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 18 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0374 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 18 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0375 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 18 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0376 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 18 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0377 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 18 else word 2854495385411919762116571938898990272765493247)).val = 2854495385411919762116571938898990272765493247 := by decide +kernel
theorem v0378 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 18 else word 2854495385411919762116571938898990272765493248)).val = 115792089237316195423570985008685053357884572745878447467518685017640364146688 := by decide +kernel
theorem v0379 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 18 else word 2854495385411919762116571938898990272765493249)).val = 115792089237316195423570985008685053357884572745878447467518685017640364146689 := by decide +kernel
theorem v0380 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 19 else word 0)).val = 0 := by decide +kernel
theorem v0381 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 19 else word 1)).val = 0 := by decide +kernel
theorem v0382 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 19 else word 2)).val = 0 := by decide +kernel
theorem v0383 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 19 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0384 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 19 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0385 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 19 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0386 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 19 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0387 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 19 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0388 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 19 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 19 := by decide +kernel
theorem v0389 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 19 else word 0)).val = 0 := by decide +kernel
theorem v0390 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 19 else word 1)).val = 1 := by decide +kernel
theorem v0391 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 19 else word 2)).val = 2 := by decide +kernel
theorem v0392 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 19 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0393 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 19 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0394 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 19 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0395 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 19 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0396 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 19 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0397 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 19 else word 730750818665451459101842416358141509827966271487)).val = 730750818665451459101842416358141509827966271487 := by decide +kernel
theorem v0398 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 19 else word 730750818665451459101842416358141509827966271488)).val = 115792089237316195423570985007957157034604533206538721623099442498085163368448 := by decide +kernel
theorem v0399 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 19 else word 730750818665451459101842416358141509827966271489)).val = 115792089237316195423570985007957157034604533206538721623099442498085163368449 := by decide +kernel
theorem v0400 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 20 else word 0)).val = 0 := by decide +kernel
theorem v0401 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 20 else word 1)).val = 0 := by decide +kernel
theorem v0402 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 20 else word 2)).val = 0 := by decide +kernel
theorem v0403 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 20 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0404 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 20 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0405 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 20 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0406 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 20 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0407 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 20 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0408 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 20 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 20 := by decide +kernel
theorem v0409 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 20 else word 0)).val = 0 := by decide +kernel
theorem v0410 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 20 else word 1)).val = 1 := by decide +kernel
theorem v0411 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 20 else word 2)).val = 2 := by decide +kernel
theorem v0412 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 20 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0413 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 20 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0414 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 20 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0415 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 20 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0416 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 20 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0417 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 20 else word 187072209578355573530071658587684226515959365500927)).val = 187072209578355573530071658587684226515959365500927 := by decide +kernel
theorem v0418 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 20 else word 187072209578355573530071658587684226515959365500928)).val = 115792089237316195423570984821615698274914411135568905451773357491953764139008 := by decide +kernel
theorem v0419 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 20 else word 187072209578355573530071658587684226515959365500929)).val = 115792089237316195423570984821615698274914411135568905451773357491953764139009 := by decide +kernel
theorem v0420 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 21 else word 0)).val = 0 := by decide +kernel
theorem v0421 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 21 else word 1)).val = 0 := by decide +kernel
theorem v0422 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 21 else word 2)).val = 0 := by decide +kernel
theorem v0423 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 21 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0424 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 21 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0425 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 21 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0426 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 21 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0427 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 21 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0428 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 21 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 21 := by decide +kernel
theorem v0429 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 21 else word 0)).val = 0 := by decide +kernel
theorem v0430 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 21 else word 1)).val = 1 := by decide +kernel
theorem v0431 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 21 else word 2)).val = 2 := by decide +kernel
theorem v0432 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 21 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0433 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 21 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0434 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 21 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0435 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 21 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0436 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 21 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0437 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 21 else word 47890485652059026823698344598447161988085597568237567)).val = 47890485652059026823698344598447161988085597568237567 := by decide +kernel
theorem v0438 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 21 else word 47890485652059026823698344598447161988085597568237568)).val = 115792089237316195423570937118202255794243160967295965592295595922315561402368 := by decide +kernel
theorem v0439 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 21 else word 47890485652059026823698344598447161988085597568237569)).val = 115792089237316195423570937118202255794243160967295965592295595922315561402369 := by decide +kernel
theorem v0440 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 22 else word 0)).val = 0 := by decide +kernel
theorem v0441 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 22 else word 1)).val = 0 := by decide +kernel
theorem v0442 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 22 else word 2)).val = 0 := by decide +kernel
theorem v0443 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 22 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0444 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 22 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0445 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 22 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0446 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 22 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0447 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 22 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0448 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 22 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 22 := by decide +kernel
theorem v0449 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 22 else word 0)).val = 0 := by decide +kernel
theorem v0450 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 22 else word 1)).val = 1 := by decide +kernel
theorem v0451 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 22 else word 2)).val = 2 := by decide +kernel
theorem v0452 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 22 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0453 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 22 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0454 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 22 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0455 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 22 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0456 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 22 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0457 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 22 else word 12259964326927110866866776217202473468949912977468817407)).val = 12259964326927110866866776217202473468949912977468817407 := by decide +kernel
theorem v0458 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 22 else word 12259964326927110866866776217202473468949912977468817408)).val = 115792089237316195423558725044360980742403117889423361565988634094935660822528 := by decide +kernel
theorem v0459 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 22 else word 12259964326927110866866776217202473468949912977468817409)).val = 115792089237316195423558725044360980742403117889423361565988634094935660822529 := by decide +kernel
theorem v0460 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 23 else word 0)).val = 0 := by decide +kernel
theorem v0461 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 23 else word 1)).val = 0 := by decide +kernel
theorem v0462 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 23 else word 2)).val = 0 := by decide +kernel
theorem v0463 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 23 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0464 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 23 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0465 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 23 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0466 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 23 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0467 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 23 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0468 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 23 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 23 := by decide +kernel
theorem v0469 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 23 else word 0)).val = 0 := by decide +kernel
theorem v0470 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 23 else word 1)).val = 1 := by decide +kernel
theorem v0471 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 23 else word 2)).val = 2 := by decide +kernel
theorem v0472 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 23 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0473 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 23 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0474 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 23 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0475 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 23 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0476 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 23 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0477 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 23 else word 3138550867693340381917894711603833208051177722232017256447)).val = 3138550867693340381917894711603833208051177722232017256447 := by decide +kernel
theorem v0478 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 23 else word 3138550867693340381917894711603833208051177722232017256448)).val = 115792089237316195420432434140994567471352089954036730831406406285681112383488 := by decide +kernel
theorem v0479 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 23 else word 3138550867693340381917894711603833208051177722232017256449)).val = 115792089237316195420432434140994567471352089954036730831406406285681112383489 := by decide +kernel
theorem v0480 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 24 else word 0)).val = 0 := by decide +kernel
theorem v0481 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 24 else word 1)).val = 0 := by decide +kernel
theorem v0482 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 24 else word 2)).val = 0 := by decide +kernel
theorem v0483 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 24 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0484 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 24 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0485 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 24 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0486 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 24 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0487 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 24 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0488 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 24 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 24 := by decide +kernel
theorem v0489 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 24 else word 0)).val = 0 := by decide +kernel
theorem v0490 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 24 else word 1)).val = 1 := by decide +kernel
theorem v0491 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 24 else word 2)).val = 2 := by decide +kernel
theorem v0492 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 24 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0493 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 24 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0494 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 24 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0495 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 24 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0496 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 24 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0497 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 24 else word 803469022129495137770981046170581301261101496891396417650687)).val = 803469022129495137770981046170581301261101496891396417650687 := by decide +kernel
theorem v0498 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 24 else word 803469022129495137770981046170581301261101496891396417650688)).val = 115792089237316194620101962879192770082288938495059262778356087116516711989248 := by decide +kernel
theorem v0499 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 24 else word 803469022129495137770981046170581301261101496891396417650689)).val = 115792089237316194620101962879192770082288938495059262778356087116516711989249 := by decide +kernel
theorem v0500 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 25 else word 0)).val = 0 := by decide +kernel
theorem v0501 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 25 else word 1)).val = 0 := by decide +kernel
theorem v0502 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 25 else word 2)).val = 0 := by decide +kernel
theorem v0503 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 25 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0504 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 25 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0505 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 25 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0506 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 25 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0507 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 25 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0508 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 25 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 25 := by decide +kernel
theorem v0509 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 25 else word 0)).val = 0 := by decide +kernel
theorem v0510 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 25 else word 1)).val = 1 := by decide +kernel
theorem v0511 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 25 else word 2)).val = 2 := by decide +kernel
theorem v0512 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 25 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0513 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 25 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0514 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 25 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0515 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 25 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0516 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 25 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0517 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 25 else word 205688069665150755269371147819668813122841983204197482918576127)).val = 205688069665150755269371147819668813122841983204197482918576127 := by decide +kernel
theorem v0518 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 25 else word 205688069665150755269371147819668813122841983204197482918576128)).val = 115792089237315989735501319857932638482122164996827441197474379810430211063808 := by decide +kernel
theorem v0519 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 25 else word 205688069665150755269371147819668813122841983204197482918576129)).val = 115792089237315989735501319857932638482122164996827441197474379810430211063809 := by decide +kernel
theorem v0520 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 26 else word 0)).val = 0 := by decide +kernel
theorem v0521 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 26 else word 1)).val = 0 := by decide +kernel
theorem v0522 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 26 else word 2)).val = 0 := by decide +kernel
theorem v0523 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 26 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0524 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 26 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0525 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 26 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0526 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 26 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0527 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 26 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0528 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 26 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 26 := by decide +kernel
theorem v0529 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 26 else word 0)).val = 0 := by decide +kernel
theorem v0530 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 26 else word 1)).val = 1 := by decide +kernel
theorem v0531 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 26 else word 2)).val = 2 := by decide +kernel
theorem v0532 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 26 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0533 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 26 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0534 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 26 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0535 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 26 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0536 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 26 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0537 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 26 else word 52656145834278593348959013841835216159447547700274555627155488767)).val = 52656145834278593348959013841835216159447547700274555627155488767 := by decide +kernel
theorem v0538 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 26 else word 52656145834278593348959013841835216159447547700274555627155488768)).val = 115792089237263539277736706415338948839428149449481116491757309452285974151168 := by decide +kernel
theorem v0539 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 26 else word 52656145834278593348959013841835216159447547700274555627155488769)).val = 115792089237263539277736706415338948839428149449481116491757309452285974151169 := by decide +kernel
theorem v0540 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 27 else word 0)).val = 0 := by decide +kernel
theorem v0541 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 27 else word 1)).val = 0 := by decide +kernel
theorem v0542 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 27 else word 2)).val = 0 := by decide +kernel
theorem v0543 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 27 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0544 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 27 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0545 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 27 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0546 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 27 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0547 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 27 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0548 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 27 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 27 := by decide +kernel
theorem v0549 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 27 else word 0)).val = 0 := by decide +kernel
theorem v0550 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 27 else word 1)).val = 1 := by decide +kernel
theorem v0551 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 27 else word 2)).val = 2 := by decide +kernel
theorem v0552 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 27 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0553 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 27 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0554 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 27 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0555 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 27 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0556 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 27 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0557 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 27 else word 13479973333575319897333507543509815336818572211270286240551805124607)).val = 13479973333575319897333507543509815336818572211270286240551805124607 := by decide +kernel
theorem v0558 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 27 else word 13479973333575319897333507543509815336818572211270286240551805124608)).val = 115792089223836222089995665111354400309760169328821991828187297767361324515328 := by decide +kernel
theorem v0559 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 27 else word 13479973333575319897333507543509815336818572211270286240551805124609)).val = 115792089223836222089995665111354400309760169328821991828187297767361324515329 := by decide +kernel
theorem v0560 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 28 else word 0)).val = 0 := by decide +kernel
theorem v0561 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 28 else word 1)).val = 0 := by decide +kernel
theorem v0562 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 28 else word 2)).val = 0 := by decide +kernel
theorem v0563 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 28 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0564 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 28 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0565 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 28 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0566 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 28 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0567 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 28 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0568 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 28 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 28 := by decide +kernel
theorem v0569 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 28 else word 0)).val = 0 := by decide +kernel
theorem v0570 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 28 else word 1)).val = 1 := by decide +kernel
theorem v0571 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 28 else word 2)).val = 2 := by decide +kernel
theorem v0572 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 28 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0573 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 28 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0574 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 28 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0575 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 28 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0576 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 28 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0577 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 28 else word 3450873173395281893717377931138512726225554486085193277581262111899647)).val = 3450873173395281893717377931138512726225554486085193277581262111899647 := by decide +kernel
theorem v0578 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 28 else word 3450873173395281893717377931138512726225554486085193277581262111899648)).val = 115792085786443022028289091291309976714757258440086077954264306426651017740288 := by decide +kernel
theorem v0579 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 28 else word 3450873173395281893717377931138512726225554486085193277581262111899649)).val = 115792085786443022028289091291309976714757258440086077954264306426651017740289 := by decide +kernel
theorem v0580 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 29 else word 0)).val = 0 := by decide +kernel
theorem v0581 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 29 else word 1)).val = 0 := by decide +kernel
theorem v0582 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 29 else word 2)).val = 0 := by decide +kernel
theorem v0583 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 29 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0584 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 29 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0585 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 29 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0586 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 29 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0587 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 29 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0588 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 29 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 29 := by decide +kernel
theorem v0589 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 29 else word 0)).val = 0 := by decide +kernel
theorem v0590 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 29 else word 1)).val = 1 := by decide +kernel
theorem v0591 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 29 else word 2)).val = 2 := by decide +kernel
theorem v0592 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 29 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0593 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 29 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0594 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 29 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0595 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 29 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0596 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 29 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0597 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 29 else word 883423532389192164791648750371459257913741948437809479060803100646309887)).val = 883423532389192164791648750371459257913741948437809479060803100646309887 := by decide +kernel
theorem v0598 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 29 else word 883423532389192164791648750371459257913741948437809479060803100646309888)).val = 115791205813783806231406193359937536394012070923692126229978523204812483330048 := by decide +kernel
theorem v0599 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 29 else word 883423532389192164791648750371459257913741948437809479060803100646309889)).val = 115791205813783806231406193359937536394012070923692126229978523204812483330049 := by decide +kernel
theorem v0600 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 30 else word 0)).val = 0 := by decide +kernel
theorem v0601 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 30 else word 1)).val = 0 := by decide +kernel
theorem v0602 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 30 else word 2)).val = 0 := by decide +kernel
theorem v0603 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 30 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0604 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 30 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0605 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 30 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0606 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 30 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 255 := by decide +kernel
theorem v0607 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 30 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0608 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 30 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 30 := by decide +kernel
theorem v0609 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 30 else word 0)).val = 0 := by decide +kernel
theorem v0610 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 30 else word 1)).val = 1 := by decide +kernel
theorem v0611 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 30 else word 2)).val = 2 := by decide +kernel
theorem v0612 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 30 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0613 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 30 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0614 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 30 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0615 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 30 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0616 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 30 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0617 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 30 else word 226156424291633194186662080095093570025917938800079226639565593765455331327)).val = 226156424291633194186662080095093570025917938800079226639565593765455331327 := by decide +kernel
theorem v0618 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 30 else word 226156424291633194186662080095093570025917938800079226639565593765455331328)).val = 115565932813024562229384322928592814283244066726840484812818018414147674308608 := by decide +kernel
theorem v0619 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 30 else word 226156424291633194186662080095093570025917938800079226639565593765455331329)).val = 115565932813024562229384322928592814283244066726840484812818018414147674308609 := by decide +kernel
theorem v0620 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 31 else word 0)).val = 0 := by decide +kernel
theorem v0621 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 31 else word 1)).val = 1 := by decide +kernel
theorem v0622 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 31 else word 2)).val = 2 := by decide +kernel
theorem v0623 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 31 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 255 := by decide +kernel
theorem v0624 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 31 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0625 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 31 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 1 := by decide +kernel
theorem v0626 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 31 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 254 := by decide +kernel
theorem v0627 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 31 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 255 := by decide +kernel
theorem v0628 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 31 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 31 := by decide +kernel
theorem v0629 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 31 else word 0)).val = 0 := by decide +kernel
theorem v0630 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 31 else word 1)).val = 1 := by decide +kernel
theorem v0631 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 31 else word 2)).val = 2 := by decide +kernel
theorem v0632 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 31 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 57896044618658097711785492504343953926634992332820282019728792003956564819967 := by decide +kernel
theorem v0633 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 31 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 57896044618658097711785492504343953926634992332820282019728792003956564819968 := by decide +kernel
theorem v0634 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 31 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 57896044618658097711785492504343953926634992332820282019728792003956564819969 := by decide +kernel
theorem v0635 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 31 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0636 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 31 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0637 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 31 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 57896044618658097711785492504343953926634992332820282019728792003956564819967 := by decide +kernel
theorem v0638 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 31 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 57896044618658097711785492504343953926634992332820282019728792003956564819968 := by decide +kernel
theorem v0639 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 31 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 57896044618658097711785492504343953926634992332820282019728792003956564819969 := by decide +kernel
theorem v0640 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 32 else word 0)).val = 0 := by decide +kernel
theorem v0641 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 32 else word 1)).val = 0 := by decide +kernel
theorem v0642 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 32 else word 2)).val = 0 := by decide +kernel
theorem v0643 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 32 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 0 := by decide +kernel
theorem v0644 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 32 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0645 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 32 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0646 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 32 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 0 := by decide +kernel
theorem v0647 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 32 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 0 := by decide +kernel
theorem v0648 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 32 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 0 := by decide +kernel
theorem v0649 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 32 else word 0)).val = 0 := by decide +kernel
theorem v0650 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 32 else word 1)).val = 1 := by decide +kernel
theorem v0651 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 32 else word 2)).val = 2 := by decide +kernel
theorem v0652 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 32 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 57896044618658097711785492504343953926634992332820282019728792003956564819967 := by decide +kernel
theorem v0653 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 32 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 57896044618658097711785492504343953926634992332820282019728792003956564819968 := by decide +kernel
theorem v0654 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 32 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 57896044618658097711785492504343953926634992332820282019728792003956564819969 := by decide +kernel
theorem v0655 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 32 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0656 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 32 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0657 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 33 else word 0)).val = 0 := by decide +kernel
theorem v0658 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 33 else word 1)).val = 0 := by decide +kernel
theorem v0659 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 33 else word 2)).val = 0 := by decide +kernel
theorem v0660 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 33 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 0 := by decide +kernel
theorem v0661 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 33 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0662 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 33 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0663 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 33 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 0 := by decide +kernel
theorem v0664 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 33 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 0 := by decide +kernel
theorem v0665 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 33 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 0 := by decide +kernel
theorem v0666 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 33 else word 0)).val = 0 := by decide +kernel
theorem v0667 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 33 else word 1)).val = 1 := by decide +kernel
theorem v0668 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 33 else word 2)).val = 2 := by decide +kernel
theorem v0669 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 33 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 57896044618658097711785492504343953926634992332820282019728792003956564819967 := by decide +kernel
theorem v0670 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 33 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 57896044618658097711785492504343953926634992332820282019728792003956564819968 := by decide +kernel
theorem v0671 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 33 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 57896044618658097711785492504343953926634992332820282019728792003956564819969 := by decide +kernel
theorem v0672 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 33 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0673 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 33 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0674 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 115792089237316195423570985008687907853269984665640564039457584007913129639935 else word 0)).val = 0 := by decide +kernel
theorem v0675 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 115792089237316195423570985008687907853269984665640564039457584007913129639935 else word 1)).val = 0 := by decide +kernel
theorem v0676 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 115792089237316195423570985008687907853269984665640564039457584007913129639935 else word 2)).val = 0 := by decide +kernel
theorem v0677 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 115792089237316195423570985008687907853269984665640564039457584007913129639935 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 0 := by decide +kernel
theorem v0678 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 115792089237316195423570985008687907853269984665640564039457584007913129639935 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel
theorem v0679 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 115792089237316195423570985008687907853269984665640564039457584007913129639935 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 0 := by decide +kernel
theorem v0680 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 115792089237316195423570985008687907853269984665640564039457584007913129639935 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 0 := by decide +kernel
theorem v0681 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 115792089237316195423570985008687907853269984665640564039457584007913129639935 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 0 := by decide +kernel
theorem v0682 : (Pure.eval .«byte» (fun i => if i.val = 0 then word 115792089237316195423570985008687907853269984665640564039457584007913129639935 else word 1780731860627700044960722568376592200742329637303199754547598369979440671)).val = 0 := by decide +kernel
theorem v0683 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 115792089237316195423570985008687907853269984665640564039457584007913129639935 else word 0)).val = 0 := by decide +kernel
theorem v0684 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 115792089237316195423570985008687907853269984665640564039457584007913129639935 else word 1)).val = 1 := by decide +kernel
theorem v0685 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 115792089237316195423570985008687907853269984665640564039457584007913129639935 else word 2)).val = 2 := by decide +kernel
theorem v0686 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 115792089237316195423570985008687907853269984665640564039457584007913129639935 else word 57896044618658097711785492504343953926634992332820282019728792003956564819967)).val = 57896044618658097711785492504343953926634992332820282019728792003956564819967 := by decide +kernel
theorem v0687 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 115792089237316195423570985008687907853269984665640564039457584007913129639935 else word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 57896044618658097711785492504343953926634992332820282019728792003956564819968 := by decide +kernel
theorem v0688 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 115792089237316195423570985008687907853269984665640564039457584007913129639935 else word 57896044618658097711785492504343953926634992332820282019728792003956564819969)).val = 57896044618658097711785492504343953926634992332820282019728792003956564819969 := by decide +kernel
theorem v0689 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 115792089237316195423570985008687907853269984665640564039457584007913129639935 else word 115792089237316195423570985008687907853269984665640564039457584007913129639934)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639934 := by decide +kernel
theorem v0690 : (Pure.eval .«signextend» (fun i => if i.val = 0 then word 115792089237316195423570985008687907853269984665640564039457584007913129639935 else word 115792089237316195423570985008687907853269984665640564039457584007913129639935)).val = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide +kernel
theorem v0691 : (Pure.eval .«clz» (fun _ => word 1)).val = 255 := by decide +kernel
theorem v0692 : (Pure.eval .«clz» (fun _ => word 2)).val = 254 := by decide +kernel
theorem v0693 : (Pure.eval .«clz» (fun _ => word 4)).val = 253 := by decide +kernel
theorem v0694 : (Pure.eval .«clz» (fun _ => word 8)).val = 252 := by decide +kernel
theorem v0695 : (Pure.eval .«clz» (fun _ => word 16)).val = 251 := by decide +kernel
theorem v0696 : (Pure.eval .«clz» (fun _ => word 32)).val = 250 := by decide +kernel
theorem v0697 : (Pure.eval .«clz» (fun _ => word 64)).val = 249 := by decide +kernel
theorem v0698 : (Pure.eval .«clz» (fun _ => word 128)).val = 248 := by decide +kernel
theorem v0699 : (Pure.eval .«clz» (fun _ => word 256)).val = 247 := by decide +kernel
theorem v0700 : (Pure.eval .«clz» (fun _ => word 512)).val = 246 := by decide +kernel
theorem v0701 : (Pure.eval .«clz» (fun _ => word 1024)).val = 245 := by decide +kernel
theorem v0702 : (Pure.eval .«clz» (fun _ => word 2048)).val = 244 := by decide +kernel
theorem v0703 : (Pure.eval .«clz» (fun _ => word 4096)).val = 243 := by decide +kernel
theorem v0704 : (Pure.eval .«clz» (fun _ => word 8192)).val = 242 := by decide +kernel
theorem v0705 : (Pure.eval .«clz» (fun _ => word 16384)).val = 241 := by decide +kernel
theorem v0706 : (Pure.eval .«clz» (fun _ => word 32768)).val = 240 := by decide +kernel
theorem v0707 : (Pure.eval .«clz» (fun _ => word 65536)).val = 239 := by decide +kernel
theorem v0708 : (Pure.eval .«clz» (fun _ => word 131072)).val = 238 := by decide +kernel
theorem v0709 : (Pure.eval .«clz» (fun _ => word 262144)).val = 237 := by decide +kernel
theorem v0710 : (Pure.eval .«clz» (fun _ => word 524288)).val = 236 := by decide +kernel
theorem v0711 : (Pure.eval .«clz» (fun _ => word 1048576)).val = 235 := by decide +kernel
theorem v0712 : (Pure.eval .«clz» (fun _ => word 2097152)).val = 234 := by decide +kernel
theorem v0713 : (Pure.eval .«clz» (fun _ => word 4194304)).val = 233 := by decide +kernel
theorem v0714 : (Pure.eval .«clz» (fun _ => word 8388608)).val = 232 := by decide +kernel
theorem v0715 : (Pure.eval .«clz» (fun _ => word 16777216)).val = 231 := by decide +kernel
theorem v0716 : (Pure.eval .«clz» (fun _ => word 33554432)).val = 230 := by decide +kernel
theorem v0717 : (Pure.eval .«clz» (fun _ => word 67108864)).val = 229 := by decide +kernel
theorem v0718 : (Pure.eval .«clz» (fun _ => word 134217728)).val = 228 := by decide +kernel
theorem v0719 : (Pure.eval .«clz» (fun _ => word 268435456)).val = 227 := by decide +kernel
theorem v0720 : (Pure.eval .«clz» (fun _ => word 536870912)).val = 226 := by decide +kernel
theorem v0721 : (Pure.eval .«clz» (fun _ => word 1073741824)).val = 225 := by decide +kernel
theorem v0722 : (Pure.eval .«clz» (fun _ => word 2147483648)).val = 224 := by decide +kernel
theorem v0723 : (Pure.eval .«clz» (fun _ => word 4294967296)).val = 223 := by decide +kernel
theorem v0724 : (Pure.eval .«clz» (fun _ => word 8589934592)).val = 222 := by decide +kernel
theorem v0725 : (Pure.eval .«clz» (fun _ => word 17179869184)).val = 221 := by decide +kernel
theorem v0726 : (Pure.eval .«clz» (fun _ => word 34359738368)).val = 220 := by decide +kernel
theorem v0727 : (Pure.eval .«clz» (fun _ => word 68719476736)).val = 219 := by decide +kernel
theorem v0728 : (Pure.eval .«clz» (fun _ => word 137438953472)).val = 218 := by decide +kernel
theorem v0729 : (Pure.eval .«clz» (fun _ => word 274877906944)).val = 217 := by decide +kernel
theorem v0730 : (Pure.eval .«clz» (fun _ => word 549755813888)).val = 216 := by decide +kernel
theorem v0731 : (Pure.eval .«clz» (fun _ => word 1099511627776)).val = 215 := by decide +kernel
theorem v0732 : (Pure.eval .«clz» (fun _ => word 2199023255552)).val = 214 := by decide +kernel
theorem v0733 : (Pure.eval .«clz» (fun _ => word 4398046511104)).val = 213 := by decide +kernel
theorem v0734 : (Pure.eval .«clz» (fun _ => word 8796093022208)).val = 212 := by decide +kernel
theorem v0735 : (Pure.eval .«clz» (fun _ => word 17592186044416)).val = 211 := by decide +kernel
theorem v0736 : (Pure.eval .«clz» (fun _ => word 35184372088832)).val = 210 := by decide +kernel
theorem v0737 : (Pure.eval .«clz» (fun _ => word 70368744177664)).val = 209 := by decide +kernel
theorem v0738 : (Pure.eval .«clz» (fun _ => word 140737488355328)).val = 208 := by decide +kernel
theorem v0739 : (Pure.eval .«clz» (fun _ => word 281474976710656)).val = 207 := by decide +kernel
theorem v0740 : (Pure.eval .«clz» (fun _ => word 562949953421312)).val = 206 := by decide +kernel
theorem v0741 : (Pure.eval .«clz» (fun _ => word 1125899906842624)).val = 205 := by decide +kernel
theorem v0742 : (Pure.eval .«clz» (fun _ => word 2251799813685248)).val = 204 := by decide +kernel
theorem v0743 : (Pure.eval .«clz» (fun _ => word 4503599627370496)).val = 203 := by decide +kernel
theorem v0744 : (Pure.eval .«clz» (fun _ => word 9007199254740992)).val = 202 := by decide +kernel
theorem v0745 : (Pure.eval .«clz» (fun _ => word 18014398509481984)).val = 201 := by decide +kernel
theorem v0746 : (Pure.eval .«clz» (fun _ => word 36028797018963968)).val = 200 := by decide +kernel
theorem v0747 : (Pure.eval .«clz» (fun _ => word 72057594037927936)).val = 199 := by decide +kernel
theorem v0748 : (Pure.eval .«clz» (fun _ => word 144115188075855872)).val = 198 := by decide +kernel
theorem v0749 : (Pure.eval .«clz» (fun _ => word 288230376151711744)).val = 197 := by decide +kernel
theorem v0750 : (Pure.eval .«clz» (fun _ => word 576460752303423488)).val = 196 := by decide +kernel
theorem v0751 : (Pure.eval .«clz» (fun _ => word 1152921504606846976)).val = 195 := by decide +kernel
theorem v0752 : (Pure.eval .«clz» (fun _ => word 2305843009213693952)).val = 194 := by decide +kernel
theorem v0753 : (Pure.eval .«clz» (fun _ => word 4611686018427387904)).val = 193 := by decide +kernel
theorem v0754 : (Pure.eval .«clz» (fun _ => word 9223372036854775808)).val = 192 := by decide +kernel
theorem v0755 : (Pure.eval .«clz» (fun _ => word 18446744073709551616)).val = 191 := by decide +kernel
theorem v0756 : (Pure.eval .«clz» (fun _ => word 36893488147419103232)).val = 190 := by decide +kernel
theorem v0757 : (Pure.eval .«clz» (fun _ => word 73786976294838206464)).val = 189 := by decide +kernel
theorem v0758 : (Pure.eval .«clz» (fun _ => word 147573952589676412928)).val = 188 := by decide +kernel
theorem v0759 : (Pure.eval .«clz» (fun _ => word 295147905179352825856)).val = 187 := by decide +kernel
theorem v0760 : (Pure.eval .«clz» (fun _ => word 590295810358705651712)).val = 186 := by decide +kernel
theorem v0761 : (Pure.eval .«clz» (fun _ => word 1180591620717411303424)).val = 185 := by decide +kernel
theorem v0762 : (Pure.eval .«clz» (fun _ => word 2361183241434822606848)).val = 184 := by decide +kernel
theorem v0763 : (Pure.eval .«clz» (fun _ => word 4722366482869645213696)).val = 183 := by decide +kernel
theorem v0764 : (Pure.eval .«clz» (fun _ => word 9444732965739290427392)).val = 182 := by decide +kernel
theorem v0765 : (Pure.eval .«clz» (fun _ => word 18889465931478580854784)).val = 181 := by decide +kernel
theorem v0766 : (Pure.eval .«clz» (fun _ => word 37778931862957161709568)).val = 180 := by decide +kernel
theorem v0767 : (Pure.eval .«clz» (fun _ => word 75557863725914323419136)).val = 179 := by decide +kernel
theorem v0768 : (Pure.eval .«clz» (fun _ => word 151115727451828646838272)).val = 178 := by decide +kernel
theorem v0769 : (Pure.eval .«clz» (fun _ => word 302231454903657293676544)).val = 177 := by decide +kernel
theorem v0770 : (Pure.eval .«clz» (fun _ => word 604462909807314587353088)).val = 176 := by decide +kernel
theorem v0771 : (Pure.eval .«clz» (fun _ => word 1208925819614629174706176)).val = 175 := by decide +kernel
theorem v0772 : (Pure.eval .«clz» (fun _ => word 2417851639229258349412352)).val = 174 := by decide +kernel
theorem v0773 : (Pure.eval .«clz» (fun _ => word 4835703278458516698824704)).val = 173 := by decide +kernel
theorem v0774 : (Pure.eval .«clz» (fun _ => word 9671406556917033397649408)).val = 172 := by decide +kernel
theorem v0775 : (Pure.eval .«clz» (fun _ => word 19342813113834066795298816)).val = 171 := by decide +kernel
theorem v0776 : (Pure.eval .«clz» (fun _ => word 38685626227668133590597632)).val = 170 := by decide +kernel
theorem v0777 : (Pure.eval .«clz» (fun _ => word 77371252455336267181195264)).val = 169 := by decide +kernel
theorem v0778 : (Pure.eval .«clz» (fun _ => word 154742504910672534362390528)).val = 168 := by decide +kernel
theorem v0779 : (Pure.eval .«clz» (fun _ => word 309485009821345068724781056)).val = 167 := by decide +kernel
theorem v0780 : (Pure.eval .«clz» (fun _ => word 618970019642690137449562112)).val = 166 := by decide +kernel
theorem v0781 : (Pure.eval .«clz» (fun _ => word 1237940039285380274899124224)).val = 165 := by decide +kernel
theorem v0782 : (Pure.eval .«clz» (fun _ => word 2475880078570760549798248448)).val = 164 := by decide +kernel
theorem v0783 : (Pure.eval .«clz» (fun _ => word 4951760157141521099596496896)).val = 163 := by decide +kernel
theorem v0784 : (Pure.eval .«clz» (fun _ => word 9903520314283042199192993792)).val = 162 := by decide +kernel
theorem v0785 : (Pure.eval .«clz» (fun _ => word 19807040628566084398385987584)).val = 161 := by decide +kernel
theorem v0786 : (Pure.eval .«clz» (fun _ => word 39614081257132168796771975168)).val = 160 := by decide +kernel
theorem v0787 : (Pure.eval .«clz» (fun _ => word 79228162514264337593543950336)).val = 159 := by decide +kernel
theorem v0788 : (Pure.eval .«clz» (fun _ => word 158456325028528675187087900672)).val = 158 := by decide +kernel
theorem v0789 : (Pure.eval .«clz» (fun _ => word 316912650057057350374175801344)).val = 157 := by decide +kernel
theorem v0790 : (Pure.eval .«clz» (fun _ => word 633825300114114700748351602688)).val = 156 := by decide +kernel
theorem v0791 : (Pure.eval .«clz» (fun _ => word 1267650600228229401496703205376)).val = 155 := by decide +kernel
theorem v0792 : (Pure.eval .«clz» (fun _ => word 2535301200456458802993406410752)).val = 154 := by decide +kernel
theorem v0793 : (Pure.eval .«clz» (fun _ => word 5070602400912917605986812821504)).val = 153 := by decide +kernel
theorem v0794 : (Pure.eval .«clz» (fun _ => word 10141204801825835211973625643008)).val = 152 := by decide +kernel
theorem v0795 : (Pure.eval .«clz» (fun _ => word 20282409603651670423947251286016)).val = 151 := by decide +kernel
theorem v0796 : (Pure.eval .«clz» (fun _ => word 40564819207303340847894502572032)).val = 150 := by decide +kernel
theorem v0797 : (Pure.eval .«clz» (fun _ => word 81129638414606681695789005144064)).val = 149 := by decide +kernel
theorem v0798 : (Pure.eval .«clz» (fun _ => word 162259276829213363391578010288128)).val = 148 := by decide +kernel
theorem v0799 : (Pure.eval .«clz» (fun _ => word 324518553658426726783156020576256)).val = 147 := by decide +kernel
theorem v0800 : (Pure.eval .«clz» (fun _ => word 649037107316853453566312041152512)).val = 146 := by decide +kernel
theorem v0801 : (Pure.eval .«clz» (fun _ => word 1298074214633706907132624082305024)).val = 145 := by decide +kernel
theorem v0802 : (Pure.eval .«clz» (fun _ => word 2596148429267413814265248164610048)).val = 144 := by decide +kernel
theorem v0803 : (Pure.eval .«clz» (fun _ => word 5192296858534827628530496329220096)).val = 143 := by decide +kernel
theorem v0804 : (Pure.eval .«clz» (fun _ => word 10384593717069655257060992658440192)).val = 142 := by decide +kernel
theorem v0805 : (Pure.eval .«clz» (fun _ => word 20769187434139310514121985316880384)).val = 141 := by decide +kernel
theorem v0806 : (Pure.eval .«clz» (fun _ => word 41538374868278621028243970633760768)).val = 140 := by decide +kernel
theorem v0807 : (Pure.eval .«clz» (fun _ => word 83076749736557242056487941267521536)).val = 139 := by decide +kernel
theorem v0808 : (Pure.eval .«clz» (fun _ => word 166153499473114484112975882535043072)).val = 138 := by decide +kernel
theorem v0809 : (Pure.eval .«clz» (fun _ => word 332306998946228968225951765070086144)).val = 137 := by decide +kernel
theorem v0810 : (Pure.eval .«clz» (fun _ => word 664613997892457936451903530140172288)).val = 136 := by decide +kernel
theorem v0811 : (Pure.eval .«clz» (fun _ => word 1329227995784915872903807060280344576)).val = 135 := by decide +kernel
theorem v0812 : (Pure.eval .«clz» (fun _ => word 2658455991569831745807614120560689152)).val = 134 := by decide +kernel
theorem v0813 : (Pure.eval .«clz» (fun _ => word 5316911983139663491615228241121378304)).val = 133 := by decide +kernel
theorem v0814 : (Pure.eval .«clz» (fun _ => word 10633823966279326983230456482242756608)).val = 132 := by decide +kernel
theorem v0815 : (Pure.eval .«clz» (fun _ => word 21267647932558653966460912964485513216)).val = 131 := by decide +kernel
theorem v0816 : (Pure.eval .«clz» (fun _ => word 42535295865117307932921825928971026432)).val = 130 := by decide +kernel
theorem v0817 : (Pure.eval .«clz» (fun _ => word 85070591730234615865843651857942052864)).val = 129 := by decide +kernel
theorem v0818 : (Pure.eval .«clz» (fun _ => word 170141183460469231731687303715884105728)).val = 128 := by decide +kernel
theorem v0819 : (Pure.eval .«clz» (fun _ => word 340282366920938463463374607431768211456)).val = 127 := by decide +kernel
theorem v0820 : (Pure.eval .«clz» (fun _ => word 680564733841876926926749214863536422912)).val = 126 := by decide +kernel
theorem v0821 : (Pure.eval .«clz» (fun _ => word 1361129467683753853853498429727072845824)).val = 125 := by decide +kernel
theorem v0822 : (Pure.eval .«clz» (fun _ => word 2722258935367507707706996859454145691648)).val = 124 := by decide +kernel
theorem v0823 : (Pure.eval .«clz» (fun _ => word 5444517870735015415413993718908291383296)).val = 123 := by decide +kernel
theorem v0824 : (Pure.eval .«clz» (fun _ => word 10889035741470030830827987437816582766592)).val = 122 := by decide +kernel
theorem v0825 : (Pure.eval .«clz» (fun _ => word 21778071482940061661655974875633165533184)).val = 121 := by decide +kernel
theorem v0826 : (Pure.eval .«clz» (fun _ => word 43556142965880123323311949751266331066368)).val = 120 := by decide +kernel
theorem v0827 : (Pure.eval .«clz» (fun _ => word 87112285931760246646623899502532662132736)).val = 119 := by decide +kernel
theorem v0828 : (Pure.eval .«clz» (fun _ => word 174224571863520493293247799005065324265472)).val = 118 := by decide +kernel
theorem v0829 : (Pure.eval .«clz» (fun _ => word 348449143727040986586495598010130648530944)).val = 117 := by decide +kernel
theorem v0830 : (Pure.eval .«clz» (fun _ => word 696898287454081973172991196020261297061888)).val = 116 := by decide +kernel
theorem v0831 : (Pure.eval .«clz» (fun _ => word 1393796574908163946345982392040522594123776)).val = 115 := by decide +kernel
theorem v0832 : (Pure.eval .«clz» (fun _ => word 2787593149816327892691964784081045188247552)).val = 114 := by decide +kernel
theorem v0833 : (Pure.eval .«clz» (fun _ => word 5575186299632655785383929568162090376495104)).val = 113 := by decide +kernel
theorem v0834 : (Pure.eval .«clz» (fun _ => word 11150372599265311570767859136324180752990208)).val = 112 := by decide +kernel
theorem v0835 : (Pure.eval .«clz» (fun _ => word 22300745198530623141535718272648361505980416)).val = 111 := by decide +kernel
theorem v0836 : (Pure.eval .«clz» (fun _ => word 44601490397061246283071436545296723011960832)).val = 110 := by decide +kernel
theorem v0837 : (Pure.eval .«clz» (fun _ => word 89202980794122492566142873090593446023921664)).val = 109 := by decide +kernel
theorem v0838 : (Pure.eval .«clz» (fun _ => word 178405961588244985132285746181186892047843328)).val = 108 := by decide +kernel
theorem v0839 : (Pure.eval .«clz» (fun _ => word 356811923176489970264571492362373784095686656)).val = 107 := by decide +kernel
theorem v0840 : (Pure.eval .«clz» (fun _ => word 713623846352979940529142984724747568191373312)).val = 106 := by decide +kernel
theorem v0841 : (Pure.eval .«clz» (fun _ => word 1427247692705959881058285969449495136382746624)).val = 105 := by decide +kernel
theorem v0842 : (Pure.eval .«clz» (fun _ => word 2854495385411919762116571938898990272765493248)).val = 104 := by decide +kernel
theorem v0843 : (Pure.eval .«clz» (fun _ => word 5708990770823839524233143877797980545530986496)).val = 103 := by decide +kernel
theorem v0844 : (Pure.eval .«clz» (fun _ => word 11417981541647679048466287755595961091061972992)).val = 102 := by decide +kernel
theorem v0845 : (Pure.eval .«clz» (fun _ => word 22835963083295358096932575511191922182123945984)).val = 101 := by decide +kernel
theorem v0846 : (Pure.eval .«clz» (fun _ => word 45671926166590716193865151022383844364247891968)).val = 100 := by decide +kernel
theorem v0847 : (Pure.eval .«clz» (fun _ => word 91343852333181432387730302044767688728495783936)).val = 99 := by decide +kernel
theorem v0848 : (Pure.eval .«clz» (fun _ => word 182687704666362864775460604089535377456991567872)).val = 98 := by decide +kernel
theorem v0849 : (Pure.eval .«clz» (fun _ => word 365375409332725729550921208179070754913983135744)).val = 97 := by decide +kernel
theorem v0850 : (Pure.eval .«clz» (fun _ => word 730750818665451459101842416358141509827966271488)).val = 96 := by decide +kernel
theorem v0851 : (Pure.eval .«clz» (fun _ => word 1461501637330902918203684832716283019655932542976)).val = 95 := by decide +kernel
theorem v0852 : (Pure.eval .«clz» (fun _ => word 2923003274661805836407369665432566039311865085952)).val = 94 := by decide +kernel
theorem v0853 : (Pure.eval .«clz» (fun _ => word 5846006549323611672814739330865132078623730171904)).val = 93 := by decide +kernel
theorem v0854 : (Pure.eval .«clz» (fun _ => word 11692013098647223345629478661730264157247460343808)).val = 92 := by decide +kernel
theorem v0855 : (Pure.eval .«clz» (fun _ => word 23384026197294446691258957323460528314494920687616)).val = 91 := by decide +kernel
theorem v0856 : (Pure.eval .«clz» (fun _ => word 46768052394588893382517914646921056628989841375232)).val = 90 := by decide +kernel
theorem v0857 : (Pure.eval .«clz» (fun _ => word 93536104789177786765035829293842113257979682750464)).val = 89 := by decide +kernel
theorem v0858 : (Pure.eval .«clz» (fun _ => word 187072209578355573530071658587684226515959365500928)).val = 88 := by decide +kernel
theorem v0859 : (Pure.eval .«clz» (fun _ => word 374144419156711147060143317175368453031918731001856)).val = 87 := by decide +kernel
theorem v0860 : (Pure.eval .«clz» (fun _ => word 748288838313422294120286634350736906063837462003712)).val = 86 := by decide +kernel
theorem v0861 : (Pure.eval .«clz» (fun _ => word 1496577676626844588240573268701473812127674924007424)).val = 85 := by decide +kernel
theorem v0862 : (Pure.eval .«clz» (fun _ => word 2993155353253689176481146537402947624255349848014848)).val = 84 := by decide +kernel
theorem v0863 : (Pure.eval .«clz» (fun _ => word 5986310706507378352962293074805895248510699696029696)).val = 83 := by decide +kernel
theorem v0864 : (Pure.eval .«clz» (fun _ => word 11972621413014756705924586149611790497021399392059392)).val = 82 := by decide +kernel
theorem v0865 : (Pure.eval .«clz» (fun _ => word 23945242826029513411849172299223580994042798784118784)).val = 81 := by decide +kernel
theorem v0866 : (Pure.eval .«clz» (fun _ => word 47890485652059026823698344598447161988085597568237568)).val = 80 := by decide +kernel
theorem v0867 : (Pure.eval .«clz» (fun _ => word 95780971304118053647396689196894323976171195136475136)).val = 79 := by decide +kernel
theorem v0868 : (Pure.eval .«clz» (fun _ => word 191561942608236107294793378393788647952342390272950272)).val = 78 := by decide +kernel
theorem v0869 : (Pure.eval .«clz» (fun _ => word 383123885216472214589586756787577295904684780545900544)).val = 77 := by decide +kernel
theorem v0870 : (Pure.eval .«clz» (fun _ => word 766247770432944429179173513575154591809369561091801088)).val = 76 := by decide +kernel
theorem v0871 : (Pure.eval .«clz» (fun _ => word 1532495540865888858358347027150309183618739122183602176)).val = 75 := by decide +kernel
theorem v0872 : (Pure.eval .«clz» (fun _ => word 3064991081731777716716694054300618367237478244367204352)).val = 74 := by decide +kernel
theorem v0873 : (Pure.eval .«clz» (fun _ => word 6129982163463555433433388108601236734474956488734408704)).val = 73 := by decide +kernel
theorem v0874 : (Pure.eval .«clz» (fun _ => word 12259964326927110866866776217202473468949912977468817408)).val = 72 := by decide +kernel
theorem v0875 : (Pure.eval .«clz» (fun _ => word 24519928653854221733733552434404946937899825954937634816)).val = 71 := by decide +kernel
theorem v0876 : (Pure.eval .«clz» (fun _ => word 49039857307708443467467104868809893875799651909875269632)).val = 70 := by decide +kernel
theorem v0877 : (Pure.eval .«clz» (fun _ => word 98079714615416886934934209737619787751599303819750539264)).val = 69 := by decide +kernel
theorem v0878 : (Pure.eval .«clz» (fun _ => word 196159429230833773869868419475239575503198607639501078528)).val = 68 := by decide +kernel
theorem v0879 : (Pure.eval .«clz» (fun _ => word 392318858461667547739736838950479151006397215279002157056)).val = 67 := by decide +kernel
theorem v0880 : (Pure.eval .«clz» (fun _ => word 784637716923335095479473677900958302012794430558004314112)).val = 66 := by decide +kernel
theorem v0881 : (Pure.eval .«clz» (fun _ => word 1569275433846670190958947355801916604025588861116008628224)).val = 65 := by decide +kernel
theorem v0882 : (Pure.eval .«clz» (fun _ => word 3138550867693340381917894711603833208051177722232017256448)).val = 64 := by decide +kernel
theorem v0883 : (Pure.eval .«clz» (fun _ => word 6277101735386680763835789423207666416102355444464034512896)).val = 63 := by decide +kernel
theorem v0884 : (Pure.eval .«clz» (fun _ => word 12554203470773361527671578846415332832204710888928069025792)).val = 62 := by decide +kernel
theorem v0885 : (Pure.eval .«clz» (fun _ => word 25108406941546723055343157692830665664409421777856138051584)).val = 61 := by decide +kernel
theorem v0886 : (Pure.eval .«clz» (fun _ => word 50216813883093446110686315385661331328818843555712276103168)).val = 60 := by decide +kernel
theorem v0887 : (Pure.eval .«clz» (fun _ => word 100433627766186892221372630771322662657637687111424552206336)).val = 59 := by decide +kernel
theorem v0888 : (Pure.eval .«clz» (fun _ => word 200867255532373784442745261542645325315275374222849104412672)).val = 58 := by decide +kernel
theorem v0889 : (Pure.eval .«clz» (fun _ => word 401734511064747568885490523085290650630550748445698208825344)).val = 57 := by decide +kernel
theorem v0890 : (Pure.eval .«clz» (fun _ => word 803469022129495137770981046170581301261101496891396417650688)).val = 56 := by decide +kernel
theorem v0891 : (Pure.eval .«clz» (fun _ => word 1606938044258990275541962092341162602522202993782792835301376)).val = 55 := by decide +kernel
theorem v0892 : (Pure.eval .«clz» (fun _ => word 3213876088517980551083924184682325205044405987565585670602752)).val = 54 := by decide +kernel
theorem v0893 : (Pure.eval .«clz» (fun _ => word 6427752177035961102167848369364650410088811975131171341205504)).val = 53 := by decide +kernel
theorem v0894 : (Pure.eval .«clz» (fun _ => word 12855504354071922204335696738729300820177623950262342682411008)).val = 52 := by decide +kernel
theorem v0895 : (Pure.eval .«clz» (fun _ => word 25711008708143844408671393477458601640355247900524685364822016)).val = 51 := by decide +kernel
theorem v0896 : (Pure.eval .«clz» (fun _ => word 51422017416287688817342786954917203280710495801049370729644032)).val = 50 := by decide +kernel
theorem v0897 : (Pure.eval .«clz» (fun _ => word 102844034832575377634685573909834406561420991602098741459288064)).val = 49 := by decide +kernel
theorem v0898 : (Pure.eval .«clz» (fun _ => word 205688069665150755269371147819668813122841983204197482918576128)).val = 48 := by decide +kernel
theorem v0899 : (Pure.eval .«clz» (fun _ => word 411376139330301510538742295639337626245683966408394965837152256)).val = 47 := by decide +kernel
theorem v0900 : (Pure.eval .«clz» (fun _ => word 822752278660603021077484591278675252491367932816789931674304512)).val = 46 := by decide +kernel
theorem v0901 : (Pure.eval .«clz» (fun _ => word 1645504557321206042154969182557350504982735865633579863348609024)).val = 45 := by decide +kernel
theorem v0902 : (Pure.eval .«clz» (fun _ => word 3291009114642412084309938365114701009965471731267159726697218048)).val = 44 := by decide +kernel
theorem v0903 : (Pure.eval .«clz» (fun _ => word 6582018229284824168619876730229402019930943462534319453394436096)).val = 43 := by decide +kernel
theorem v0904 : (Pure.eval .«clz» (fun _ => word 13164036458569648337239753460458804039861886925068638906788872192)).val = 42 := by decide +kernel
theorem v0905 : (Pure.eval .«clz» (fun _ => word 26328072917139296674479506920917608079723773850137277813577744384)).val = 41 := by decide +kernel
theorem v0906 : (Pure.eval .«clz» (fun _ => word 52656145834278593348959013841835216159447547700274555627155488768)).val = 40 := by decide +kernel
theorem v0907 : (Pure.eval .«clz» (fun _ => word 105312291668557186697918027683670432318895095400549111254310977536)).val = 39 := by decide +kernel
theorem v0908 : (Pure.eval .«clz» (fun _ => word 210624583337114373395836055367340864637790190801098222508621955072)).val = 38 := by decide +kernel
theorem v0909 : (Pure.eval .«clz» (fun _ => word 421249166674228746791672110734681729275580381602196445017243910144)).val = 37 := by decide +kernel
theorem v0910 : (Pure.eval .«clz» (fun _ => word 842498333348457493583344221469363458551160763204392890034487820288)).val = 36 := by decide +kernel
theorem v0911 : (Pure.eval .«clz» (fun _ => word 1684996666696914987166688442938726917102321526408785780068975640576)).val = 35 := by decide +kernel
theorem v0912 : (Pure.eval .«clz» (fun _ => word 3369993333393829974333376885877453834204643052817571560137951281152)).val = 34 := by decide +kernel
theorem v0913 : (Pure.eval .«clz» (fun _ => word 6739986666787659948666753771754907668409286105635143120275902562304)).val = 33 := by decide +kernel
theorem v0914 : (Pure.eval .«clz» (fun _ => word 13479973333575319897333507543509815336818572211270286240551805124608)).val = 32 := by decide +kernel
theorem v0915 : (Pure.eval .«clz» (fun _ => word 26959946667150639794667015087019630673637144422540572481103610249216)).val = 31 := by decide +kernel
theorem v0916 : (Pure.eval .«clz» (fun _ => word 53919893334301279589334030174039261347274288845081144962207220498432)).val = 30 := by decide +kernel
theorem v0917 : (Pure.eval .«clz» (fun _ => word 107839786668602559178668060348078522694548577690162289924414440996864)).val = 29 := by decide +kernel
theorem v0918 : (Pure.eval .«clz» (fun _ => word 215679573337205118357336120696157045389097155380324579848828881993728)).val = 28 := by decide +kernel
theorem v0919 : (Pure.eval .«clz» (fun _ => word 431359146674410236714672241392314090778194310760649159697657763987456)).val = 27 := by decide +kernel
theorem v0920 : (Pure.eval .«clz» (fun _ => word 862718293348820473429344482784628181556388621521298319395315527974912)).val = 26 := by decide +kernel
theorem v0921 : (Pure.eval .«clz» (fun _ => word 1725436586697640946858688965569256363112777243042596638790631055949824)).val = 25 := by decide +kernel
theorem v0922 : (Pure.eval .«clz» (fun _ => word 3450873173395281893717377931138512726225554486085193277581262111899648)).val = 24 := by decide +kernel
theorem v0923 : (Pure.eval .«clz» (fun _ => word 6901746346790563787434755862277025452451108972170386555162524223799296)).val = 23 := by decide +kernel
theorem v0924 : (Pure.eval .«clz» (fun _ => word 13803492693581127574869511724554050904902217944340773110325048447598592)).val = 22 := by decide +kernel
theorem v0925 : (Pure.eval .«clz» (fun _ => word 27606985387162255149739023449108101809804435888681546220650096895197184)).val = 21 := by decide +kernel
theorem v0926 : (Pure.eval .«clz» (fun _ => word 55213970774324510299478046898216203619608871777363092441300193790394368)).val = 20 := by decide +kernel
theorem v0927 : (Pure.eval .«clz» (fun _ => word 110427941548649020598956093796432407239217743554726184882600387580788736)).val = 19 := by decide +kernel
theorem v0928 : (Pure.eval .«clz» (fun _ => word 220855883097298041197912187592864814478435487109452369765200775161577472)).val = 18 := by decide +kernel
theorem v0929 : (Pure.eval .«clz» (fun _ => word 441711766194596082395824375185729628956870974218904739530401550323154944)).val = 17 := by decide +kernel
theorem v0930 : (Pure.eval .«clz» (fun _ => word 883423532389192164791648750371459257913741948437809479060803100646309888)).val = 16 := by decide +kernel
theorem v0931 : (Pure.eval .«clz» (fun _ => word 1766847064778384329583297500742918515827483896875618958121606201292619776)).val = 15 := by decide +kernel
theorem v0932 : (Pure.eval .«clz» (fun _ => word 3533694129556768659166595001485837031654967793751237916243212402585239552)).val = 14 := by decide +kernel
theorem v0933 : (Pure.eval .«clz» (fun _ => word 7067388259113537318333190002971674063309935587502475832486424805170479104)).val = 13 := by decide +kernel
theorem v0934 : (Pure.eval .«clz» (fun _ => word 14134776518227074636666380005943348126619871175004951664972849610340958208)).val = 12 := by decide +kernel
theorem v0935 : (Pure.eval .«clz» (fun _ => word 28269553036454149273332760011886696253239742350009903329945699220681916416)).val = 11 := by decide +kernel
theorem v0936 : (Pure.eval .«clz» (fun _ => word 56539106072908298546665520023773392506479484700019806659891398441363832832)).val = 10 := by decide +kernel
theorem v0937 : (Pure.eval .«clz» (fun _ => word 113078212145816597093331040047546785012958969400039613319782796882727665664)).val = 9 := by decide +kernel
theorem v0938 : (Pure.eval .«clz» (fun _ => word 226156424291633194186662080095093570025917938800079226639565593765455331328)).val = 8 := by decide +kernel
theorem v0939 : (Pure.eval .«clz» (fun _ => word 452312848583266388373324160190187140051835877600158453279131187530910662656)).val = 7 := by decide +kernel
theorem v0940 : (Pure.eval .«clz» (fun _ => word 904625697166532776746648320380374280103671755200316906558262375061821325312)).val = 6 := by decide +kernel
theorem v0941 : (Pure.eval .«clz» (fun _ => word 1809251394333065553493296640760748560207343510400633813116524750123642650624)).val = 5 := by decide +kernel
theorem v0942 : (Pure.eval .«clz» (fun _ => word 3618502788666131106986593281521497120414687020801267626233049500247285301248)).val = 4 := by decide +kernel
theorem v0943 : (Pure.eval .«clz» (fun _ => word 7237005577332262213973186563042994240829374041602535252466099000494570602496)).val = 3 := by decide +kernel
theorem v0944 : (Pure.eval .«clz» (fun _ => word 14474011154664524427946373126085988481658748083205070504932198000989141204992)).val = 2 := by decide +kernel
theorem v0945 : (Pure.eval .«clz» (fun _ => word 28948022309329048855892746252171976963317496166410141009864396001978282409984)).val = 1 := by decide +kernel
theorem v0946 : (Pure.eval .«clz» (fun _ => word 57896044618658097711785492504343953926634992332820282019728792003956564819968)).val = 0 := by decide +kernel

end Solidity.Yul.Checks.Bytes
