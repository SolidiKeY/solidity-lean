import tests.h62.item2.«audit-evm-compiler».JointWitness
import Solidity.Backend.Jumpdest

/-! Checked joint inputs for every authored Jumpdest theorem. These are local
byte/program, lookup, boundary and size conditions, with no global producer
premise. Concrete controls distinguish instruction boundaries from PUSH data. -/
namespace Solidity.H62.EvmCompilerAudit.Jumpdest
open Backend

-- Frozen original: Solidity.Backend.starts_cons
#audit_joint_witness "Solidity.Backend.starts_cons" as Solidity.H62.EvmCompilerAudit.Jumpdest.case00 := by
  exact ⟨0x5b, [], True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.Jumpdest.case00

-- Frozen original: Solidity.Backend.inPushData_cons
#audit_joint_witness "Solidity.Backend.inPushData_cons" as Solidity.H62.EvmCompilerAudit.Jumpdest.case01 := by
  exact ⟨0x60, [0x5b], 1, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.Jumpdest.case01

-- Frozen original: Solidity.Backend.mem_starts
#audit_joint_witness "Solidity.Backend.mem_starts" as Solidity.H62.EvmCompilerAudit.Jumpdest.case02 := by
  exact ⟨[0x5b], 0, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.Jumpdest.case02

-- Frozen original: Solidity.Backend.Boundary.cons
#audit_joint_witness "Solidity.Backend.Boundary.cons" as Solidity.H62.EvmCompilerAudit.Jumpdest.case03 := by
  exact ⟨0x5b, [0x5b], 0, Boundary.zero (by decide), True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.Jumpdest.case03

-- Frozen original: Solidity.Backend.mem_starts_iff_boundary
#audit_joint_witness "Solidity.Backend.mem_starts_iff_boundary" as Solidity.H62.EvmCompilerAudit.Jumpdest.case04 := by
  exact ⟨[0x5b], 0, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.Jumpdest.case04

-- Frozen original: Solidity.Backend.validJumpdest_iff
#audit_joint_witness "Solidity.Backend.validJumpdest_iff" as Solidity.H62.EvmCompilerAudit.Jumpdest.case05 := by
  exact ⟨[0x5b], 0, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.Jumpdest.case05

-- Frozen original: Solidity.Backend.Instr.opcode_eq_jumpdest
#audit_joint_witness "Solidity.Backend.Instr.opcode_eq_jumpdest" as Solidity.H62.EvmCompilerAudit.Jumpdest.case06 := by
  exact ⟨.op .JUMPDEST, rfl, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.Jumpdest.case06

-- Frozen original: Solidity.Backend.immWidth_opcode
#audit_joint_witness "Solidity.Backend.immWidth_opcode" as Solidity.H62.EvmCompilerAudit.Jumpdest.case07 := by
  exact ⟨.op .JUMPDEST, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.Jumpdest.case07

-- Frozen original: Solidity.Backend.Instr.encode_eq
#audit_joint_witness "Solidity.Backend.Instr.encode_eq" as Solidity.H62.EvmCompilerAudit.Jumpdest.case08 := by
  exact ⟨.op .JUMPDEST, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.Jumpdest.case08

-- Frozen original: Solidity.Backend.starts_instr_append
#audit_joint_witness "Solidity.Backend.starts_instr_append" as Solidity.H62.EvmCompilerAudit.Jumpdest.case09 := by
  exact ⟨.op .JUMPDEST, [0x00], True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.Jumpdest.case09

-- Frozen original: Solidity.Backend.offset_cons_succ
#audit_joint_witness "Solidity.Backend.offset_cons_succ" as Solidity.H62.EvmCompilerAudit.Jumpdest.case10 := by
  exact ⟨.op .JUMPDEST, [.op .STOP], 0, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.Jumpdest.case10

-- Frozen original: Solidity.Backend.offset_append
#audit_joint_witness "Solidity.Backend.offset_append" as Solidity.H62.EvmCompilerAudit.Jumpdest.case11 := by
  exact ⟨[.op .JUMPDEST], [.op .STOP], 0, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.Jumpdest.case11

-- Frozen original: Solidity.Backend.starts_encode_append
#audit_joint_witness "Solidity.Backend.starts_encode_append" as Solidity.H62.EvmCompilerAudit.Jumpdest.case12 := by
  exact ⟨[.op .JUMPDEST], [0x00], True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.Jumpdest.case12

-- Frozen original: Solidity.Backend.getElem?_encode_append_offset
#audit_joint_witness "Solidity.Backend.getElem?_encode_append_offset" as Solidity.H62.EvmCompilerAudit.Jumpdest.case13 := by
  exact ⟨[.op .JUMPDEST], [0x00], 0, .op .JUMPDEST, rfl, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.Jumpdest.case13

-- Frozen original: Solidity.Backend.validJumpdest_encode_append
#audit_joint_witness "Solidity.Backend.validJumpdest_encode_append" as Solidity.H62.EvmCompilerAudit.Jumpdest.case14 := by
  exact ⟨[.op .JUMPDEST], [0x00], 0, rfl, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.Jumpdest.case14

-- Frozen original: Solidity.Backend.validJumpdest_encode_iff
#audit_joint_witness "Solidity.Backend.validJumpdest_encode_iff" as Solidity.H62.EvmCompilerAudit.Jumpdest.case15 := by
  exact ⟨[.op .JUMPDEST], 0, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.Jumpdest.case15

-- Frozen original: Solidity.Backend.offset_lt_size
#audit_joint_witness "Solidity.Backend.offset_lt_size" as Solidity.H62.EvmCompilerAudit.Jumpdest.case16 := by
  exact ⟨[.op .JUMPDEST], 0, by decide, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.Jumpdest.case16

-- Frozen original: Solidity.Backend.validJumpdest_encode_append_iff
#audit_joint_witness "Solidity.Backend.validJumpdest_encode_append_iff" as Solidity.H62.EvmCompilerAudit.Jumpdest.case17 := by
  exact ⟨[.op .JUMPDEST], [0x00], 0, by decide, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.Jumpdest.case17

-- Frozen original: Solidity.Backend.validJumpdest_encode_prefix
#audit_joint_witness "Solidity.Backend.validJumpdest_encode_prefix" as Solidity.H62.EvmCompilerAudit.Jumpdest.case18 := by
  exact ⟨[.op .JUMPDEST], [0x5b], 0, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.Jumpdest.case18

private theorem packet_starts : starts [0x60, 0x5b, 0x5b] = [0, 2] := by
  rw [starts_cons]
  change 0 :: (starts [0x5b]).map (· + 2) = [0, 2]
  rw [starts_cons]
  change 0 :: (0 :: (starts []).map (· + 1)).map (· + 2) = [0, 2]
  rw [starts]
  rfl

private theorem truncated_starts : starts [0x7f, 0x5b] = [0] := by
  rw [starts_cons]
  change 0 :: (starts []).map (· + 33) = [0]
  rw [starts]
  rfl

theorem push_data_rejected : validJumpdest [0x60, 0x5b, 0x5b] 1 = false := by
  simp only [validJumpdest, jumpdests, packet_starts]
  decide +kernel

theorem following_destination_accepted : validJumpdest [0x60, 0x5b, 0x5b] 2 = true := by
  simp only [validJumpdest, jumpdests, packet_starts]
  decide +kernel

theorem truncated_push_rejected : validJumpdest [0x7f, 0x5b] 1 = false := by
  simp only [validJumpdest, jumpdests, truncated_starts]
  decide +kernel

/-- Scanning all bytes for 0x5b violates the boundary predicate. -/
theorem scan_all_bytes_fails :
    ¬ (∀ (c : List UInt8) (i : Nat), validJumpdest c i = (c[i]? == some Op.JUMPDEST.code)) := by
  intro h
  have bad := h [0x60, 0x5b, 0x5b] 1
  rw [push_data_rejected] at bad
  contradiction

#print axioms packet_starts
#print axioms truncated_starts
#print axioms Solidity.H62.EvmCompilerAudit.Jumpdest.push_data_rejected
#print axioms Solidity.H62.EvmCompilerAudit.Jumpdest.following_destination_accepted
#print axioms Solidity.H62.EvmCompilerAudit.Jumpdest.truncated_push_rejected
#print axioms Solidity.H62.EvmCompilerAudit.Jumpdest.scan_all_bytes_fails
end Solidity.H62.EvmCompilerAudit.Jumpdest
