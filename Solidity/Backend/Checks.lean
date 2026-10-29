import Solidity.Backend.Control

/-!
# Byte-encoding and assembler regressions (G45.05, G45.04)

Fixed vectors for `Backend/Opcode.lean`, `Backend/Jumpdest.lean` and
`Backend/Assembler.lean`, and the axiom pins of their headline theorems. The opcode table itself is proved
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

/-! ## The assembler -/

/-- `if (x) goto end; x := 1; end:` in solc's shape. -/
def branch : List (Item String String) :=
  [.instr (.push 1 #v[0]), .instr (.op .CALLDATALOAD), .pushTag "end", .instr (.op .JUMPI),
   .instr (.push 1 #v[1]), .instr (.push 0 #v[]), .instr (.op .SSTORE), .tag "end",
   .instr (.op .STOP)]

#guard (assemble 0 (fun _ => none) branch).map (encode ·.code) =
  some [0x60, 0x00, 0x35, 0x60, 0x0a, 0x57, 0x60, 0x01, 0x5f, 0x55, 0x5b, 0x00]
-- Relocated behind a 0x20-byte prefix, the absolute push moves.
#guard (assemble 0x20 (fun _ => none) branch).map (encode ·.code) =
  some [0x60, 0x00, 0x35, 0x60, 0x2a, 0x57, 0x60, 0x01, 0x5f, 0x55, 0x5b, 0x00]
-- A section-relative push does not move.
#guard (assemble 0x20 (fun _ => none) ([.pushTagRel "a", .tag "a"] : List (Item String String))).map (encode ·.code) =
  some [0x60, 0x02, 0x5b]
-- A tag at offset 0 of a section at 0 is reached by PUSH0.
#guard (assemble 0 (fun _ => none)
    ([.tag "a", .pushTag "a", .instr (.op .JUMP)] : List (Item String String))).map
  (encode ·.code) = some [0x5b, 0x5f, 0x56]

/-- The target is at 255 under `PUSH0`, at 256 under `PUSH1` (too far) and
at 257 under `PUSH2`: the fixpoint needs three rounds. -/
def crossing : List (Item String String) :=
  .pushTag "a" :: List.replicate 254 (.instr (.op .STOP)) ++ [.tag "a"]

#guard (assemble 0 (fun _ => none) crossing).map (fun o => (encode o.code).take 3) =
  some [0x61, 0x01, 0x01]
#guard (asmWidths 0 crossing "a").val = 2

-- Missing or duplicate tags are refused.
#guard (assemble 0 (fun _ => none) [.pushTag "a"] : Option (Assembled String)).isNone
#guard (assemble 0 (fun _ => none) [.tag "a", .tag "a"] : Option (Assembled String)).isNone

/-- A library call: the address is a placeholder until linked. -/
def libCall : List (Item String String) :=
  [.pushLibraryAddress "L", .pushTag "ret", .instr (.op .JUMP), .tag "ret"]

#guard (assemble 0 (fun _ => none) libCall).map (·.linkRefs) = some [(1, "L")]
-- Link references are offsets into the whole code: behind a 0x10-byte prefix they move.
#guard (assemble 0x10 (fun _ => none) libCall).map (·.linkRefs) = some [(0x11, "L")]
#guard (assemble 0 (fun _ => none) libCall).map (fun o =>
    linkBytes (encode o.code) o.linkRefs (fun _ => Vector.replicate 20 0xaa)) =
  (assemble 0 (fun _ => some (Vector.replicate 20 0xaa)) libCall).map (encode ·.code)
#guard (assemble 0 (fun _ => some (Vector.replicate 20 0xaa)) libCall).map (·.linkRefs) = some []

/-! ## Structured control flow -/

/-- `while (slot0 != 0) slot0 -= 1;`, expanded from label 0. -/
def countdown : Block :=
  .loop [.push 0 #v[], .op .SLOAD]
    (.code [.push 1 #v[1], .push 0 #v[], .op .SLOAD, .op .SUB, .push 0 #v[], .op .SSTORE])

#guard (countdown.expand 0).2 = 2
#guard (assemble 0 (fun _ => none) (countdown.expand 0).1).map (encode ·.code) =
  some [0x5b, 0x5f, 0x54, 0x15, 0x60, 0x10, 0x57, 0x60, 0x01, 0x5f, 0x54, 0x03, 0x5f, 0x55,
    0x5f, 0x56, 0x5b]
-- The head (offset 0) is reached by PUSH0, the exit by PUSH1 0x10, the last byte.

/-- `if (slot0 != 0) slot1 = 1 else slot1 = 2;` -/
def branchy : Block :=
  .ite [.push 0 #v[], .op .SLOAD] (.code [.push 1 #v[1], .push 1 #v[1], .op .SSTORE])
    (.code [.push 1 #v[2], .push 1 #v[1], .op .SSTORE])

-- solc's legacy shape: ISZERO, the false branch at 0x0e, the end at 0x14.
#guard (assemble 0 (fun _ => none) (branchy.expand 0).1).map (encode ·.code) =
  some [0x5f, 0x54, 0x15, 0x60, 0x0e, 0x57, 0x60, 0x01, 0x60, 0x01, 0x55, 0x60, 0x14, 0x56,
    0x5b, 0x60, 0x02, 0x60, 0x01, 0x55, 0x5b]
-- After the loop, the `if` takes labels 2 and 3.
#guard ((Block.seq countdown
    (.ite [.push 0 #v[], .op .SLOAD] (.code [.push 1 #v[1], .push 1 #v[1], .op .SSTORE])
      (.code [.push 1 #v[2], .push 1 #v[1], .op .SSTORE]))).expand 0).2 = 4

#guard ofBytesBE (toBytesBE 2 0x1234).toList = 0x1234
#guard byteWidth 0 = 0 ∧ byteWidth 255 = 1 ∧ byteWidth 256 = 2

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

/-- info: 'Solidity.Backend.assemble_pushTag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms assemble_pushTag

/-- info: 'Solidity.Backend.assemble_pushTagRel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms assemble_pushTagRel

/-- info: 'Solidity.Backend.assemble_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms assemble_isSome

/-- info: 'Solidity.Backend.link_patch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms link_patch

/-- info: 'Solidity.Backend.assemble_layout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms assemble_layout

/-- info: 'Solidity.Backend.tagIndex_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tagIndex_unique

/-- info: 'Solidity.Backend.fixWidths_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fixWidths_stable

/-- info: 'Solidity.Backend.Block.tags_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Block.tags_nodup

/-- info: 'Solidity.Backend.Block.expand_assemble_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Block.expand_assemble_isSome

/-- info: 'Solidity.Backend.Block.expand_loop_layout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Block.expand_loop_layout

/-- info: 'Solidity.Backend.Block.loop_jumps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Block.loop_jumps

/-- info: 'Solidity.Backend.Block.ite_jumps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Block.ite_jumps

end Solidity.Backend.Checks
