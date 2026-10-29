import Solidity.Backend.Jumpdest

/-!
# Byte-encoding regressions (G45.05)

Fixed vectors for `Backend/Opcode.lean` and `Backend/Jumpdest.lean`, and the
axiom pins of their headline theorems. The opcode table itself is proved
over all 256 bytes there; these vectors pin concrete Osaka encodings against
the published opcode numbers.
-/

namespace Solidity.Backend.Checks

open Solidity.Backend

/-- solc's memory-pointer prologue `PUSH1 0x80 PUSH1 0x40 MSTORE`. -/
def prologue : Program := [.push 1 #v[0x80], .push 1 #v[0x40], .op .MSTORE]

#guard encode prologue = [0x60, 0x80, 0x60, 0x40, 0x52]
#guard decode [0x60, 0x80, 0x60, 0x40, 0x52] = some prologue

-- The Osaka additions and the indexed families.
#guard Op.CLZ.code = 0x1e
#guard Op.TLOAD.code = 0x5c ∧ Op.TSTORE.code = 0x5d ∧ Op.MCOPY.code = 0x5e
#guard (Op.DUP 0).code = 0x80 ∧ (Op.DUP 15).code = 0x8f
#guard (Op.SWAP 0).code = 0x90 ∧ (Op.SWAP 15).code = 0x9f
#guard (Op.LOG 0).code = 0xa0 ∧ (Op.LOG 4).code = 0xa4
#guard pushCode 0 = 0x5f ∧ pushCode 1 = 0x60 ∧ pushCode 32 = 0x7f
#guard encode [.push 0 #v[]] = [0x5f]
#guard decode [0x1e] = some [.op .CLZ]

/-- The bytes Osaka defines, written out from the execution-specs opcode
list (not computed from the table): 150 in all. -/
def osakaBytes : List Nat := [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x20, 0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3a, 0x3b, 0x3c, 0x3d, 0x3e, 0x3f, 0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5a, 0x5b, 0x5c, 0x5d, 0x5e, 0x5f, 0x60, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6a, 0x6b, 0x6c, 0x6d, 0x6e, 0x6f, 0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7a, 0x7b, 0x7c, 0x7d, 0x7e, 0x7f, 0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a, 0x8b, 0x8c, 0x8d, 0x8e, 0x8f, 0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98, 0x99, 0x9a, 0x9b, 0x9c, 0x9d, 0x9e, 0x9f, 0xa0, 0xa1, 0xa2, 0xa3, 0xa4, 0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xfa, 0xfd, 0xfe, 0xff]

-- Exactly those bytes decode; every other byte is refused.
#guard ((List.range 256).filter fun k =>
  (Op.ofCode (UInt8.ofNat k)).isSome || (pushWidth (UInt8.ofNat k)).isSome) = osakaBytes
#guard osakaBytes.length = 150

-- Undefined opcodes and truncated immediates are refused.
#guard decode [0x0c] = none
#guard decode [0xfb] = none
#guard decode [0x60] = none
#guard decode [0x7f, 0x00] = none

-- Jump destinations: not inside PUSH data, PUSH0 has none, truncated PUSH hides the rest.
#guard jumpdests [0x60, 0x5b, 0x5b] = [2]
#guard jumpdests [0x5f, 0x5b] = [1]
#guard jumpdests [0x61, 0x5b, 0x5b, 0x5b] = [3]
#guard jumpdests [0x7f, 0x5b] = []
#guard jumpdests [0x5b, 0x0c, 0x5b] = [0, 2]
#guard starts [0x60, 0x01, 0x61, 0x02, 0x03, 0x00] = [0, 2, 5]

/-- info: 'Solidity.Backend.decode_encode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms decode_encode

/-- info: 'Solidity.Backend.encode_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms encode_injective

/-- info: 'Solidity.Backend.encode_decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms encode_decode

/-- info: 'Solidity.Backend.validJumpdest_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms validJumpdest_iff

/-- info: 'Solidity.Backend.validJumpdest_encode_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms validJumpdest_encode_iff

/-- info: 'Solidity.Backend.mem_starts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mem_starts

/-- info: 'Solidity.Backend.mem_starts_iff_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mem_starts_iff_boundary

/-- info: 'Solidity.Backend.starts_encode_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms starts_encode_append

/-- info: 'Solidity.Backend.validJumpdest_encode_append_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms validJumpdest_encode_append_iff

/-- info: 'Solidity.Backend.validJumpdest_encode_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms validJumpdest_encode_prefix

end Solidity.Backend.Checks
