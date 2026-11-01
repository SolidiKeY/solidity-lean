import Solidity.Backend.Executable.StipendCall
import Solidity.Backend.Control
import Solidity.Backend.Failure.Correct

/-! A real transfer-result branch consumer of the published structured expander,
assembler and empty-REVERT emitter. Assembly preserves the actual requested-gas
CALL pre; kernel fetched CALL/jump execution and frame production remain OPEN.
No identification of the numeric, terminal slice and global EVM runners. -/
namespace Solidity.Backend.Executable.TransferCall

def branch : Block := .ite [] (.code []) (.code (Failure.emit 0 .empty))
def items (pre : Program) : List (Item Nat Empty) :=
  pre.map .instr ++ (branch.expand 0).1
def noLink (e : Empty) : Option (Vector UInt8 20) := nomatch e

def assembleAfter (pre : Program) : Option (Assembled Empty) := assemble 0 noLink (items pre)

/-- Actual caller pre and the real dynamic requested-gas CALL emitter are
assembled together, so branch labels use the whole code's byte coordinates. -/
def compile (prelude : Program) (recipient : ContractWorld.Address) : Option (Assembled Empty) :=
  assembleAfter (prelude ++ StipendCall.code recipient)

theorem assembly_available (pre : Program)
    (bound : ∀ l ∈ refs (items pre),
      tagOffset (fun _ => (32 : Fin 33)) (items pre) l < 256^32) :
    (assembleAfter pre).isSome := by
  have expanded : ((Block.seq (.code pre) branch).expand 0).1 = items pre := rfl
  apply Block.expand_assemble_isSome (.seq (.code pre) branch) 0 0 noLink
  simpa only [expanded, Nat.zero_add] using bound

/-- Every actual instruction in the combined prelude/CALL pre is retained;
the suffix is the existing label resolver's actual emitted program. -/
theorem prefix_preserved (pre : Program) {out : Assembled Empty}
    (ran : assembleAfter pre = some out) :
    out.code = pre ++ ((branch.expand 0).1.map
      (Item.emit (asmWidths 0 (items pre)) (tagOffset (asmWidths 0 (items pre)) (items pre)) 0 noLink)) := by
  have emitted := (assemble_eq ran).2.1
  rw [items, List.map_append] at emitted
  simpa only [List.map_map, Function.comp_def, Item.emit, List.map_id', items] using emitted

private theorem false_ref (pre : Program) :
    (items pre)[pre.length+1]? = some (.pushTag 0) := by
  rw [items, List.getElem?_append_right (by simp only [List.length_map]; omega)]
  simp only [List.length_map, Nat.add_sub_cancel_left]
  rfl

private theorem end_ref (pre : Program) :
    (items pre)[pre.length+3]? = some (.pushTag 1) := by
  rw [items, List.getElem?_append_right (by simp only [List.length_map]; omega)]
  simp only [List.length_map, Nat.add_sub_cancel_left]
  rfl

/-- Both real selected JUMPI/JUMP operands resolve to valid destinations in the
whole encoded program, not to offsets relative to the branch suffix. -/
theorem branch_destinations (pre : Program) {out : Assembled Empty}
    (ran : assembleAfter pre = some out) :
    (∃ j imm, tagIndex (items pre) 0 = some j ∧
      out.code[j]? = some (.op .JUMPDEST) ∧
      out.code[pre.length+1]? = some (.push (asmWidths 0 (items pre) 0) imm) ∧
      ofBytesBE imm.toList = offset out.code j ∧
      validJumpdest (encode out.code) (ofBytesBE imm.toList) = true) ∧
    (∃ j imm, tagIndex (items pre) 1 = some j ∧
      out.code[j]? = some (.op .JUMPDEST) ∧
      out.code[pre.length+3]? = some (.push (asmWidths 0 (items pre) 1) imm) ∧
      ofBytesBE imm.toList = offset out.code j ∧
      validJumpdest (encode out.code) (ofBytesBE imm.toList) = true) := by
  have consume (l k : Nat) (ref : (items pre)[k]? = some (.pushTag l)) :=
    assemble_pushTag ran ref
  obtain ⟨j,imm,index,dest,push,value,_,valid⟩ := consume 0 (pre.length+1) (false_ref pre)
  obtain ⟨j',imm',index',dest',push',value',_,valid'⟩ := consume 1 (pre.length+3) (end_ref pre)
  refine ⟨⟨j,imm,index,dest,push,?_,?_⟩,⟨j',imm',index',dest',push',?_,?_⟩⟩
  · simpa only [Nat.zero_add] using value
  · simpa only [encode_nil, List.nil_append, List.append_nil] using valid [] [] rfl
  · simpa only [Nat.zero_add] using value'
  · simpa only [encode_nil, List.nil_append, List.append_nil] using valid' [] [] rfl

/-- Extract the actual resolved failure-entry suffix. Its terminal PUSHes
and REVERT are fixed instructions, independent of selected label widths. -/
theorem failure_suffix (pre : Program) {out : Assembled Empty}
    (ran : assembleAfter pre = some out) :
    out.code.drop (pre.length+6) = Failure.emit 0 .empty ++ [.op .JUMPDEST] := by
  rw [prefix_preserved pre ran, List.drop_append]
  simp only [List.drop_eq_nil_of_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left, List.nil_append]
  rfl

/-- The selected failure body uses the existing terminal slice, consumes its
actual two free cells and preserves all caller words/memory. This does not
claim that an unproved global jump runner reaches this branch. -/
theorem failure_terminal (s : Failure.Slice.Machine) (room : s.stack.length+2 ≤ 1024)
    (unreachable : Program) :
    Failure.Slice.checkedRun (Failure.emit 0 .empty ++ unreachable) s =
      some (s,some (.revert [])) := by
  have fits : Failure.Fits 0 Failure.Input.empty.bytes := by
    change 0 < 2^256 ∧ 0 < 2^256 ∧ 0+0 ≤ 2^256
    decide +kernel
  exact Failure.checkedRun_emit_suffix 0 .empty unreachable s fits room

/-- Terminal behavior of the actual assembled suffix, without claiming an
unproved global CALL/jump runner reaches its entry. -/
theorem assembled_failure_terminal (pre : Program) {out : Assembled Empty}
    (ran : assembleAfter pre = some out) (s : Failure.Slice.Machine)
    (room : s.stack.length+2 ≤ 1024) :
    Failure.Slice.checkedRun (out.code.drop (pre.length+6)) s = some (s,some (.revert [])) := by
  rw [failure_suffix pre ran]
  exact failure_terminal s room [.op .JUMPDEST]

/-- info: 'Solidity.Backend.Executable.TransferCall.assembly_available' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assembly_available

/-- info: 'Solidity.Backend.Executable.TransferCall.prefix_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_preserved

/-- info: 'Solidity.Backend.Executable.TransferCall.branch_destinations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms branch_destinations

/-- info: 'Solidity.Backend.Executable.TransferCall.failure_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms failure_terminal

/-- info: 'Solidity.Backend.Executable.TransferCall.failure_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms failure_suffix

/-- info: 'Solidity.Backend.Executable.TransferCall.assembled_failure_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assembled_failure_terminal

end Solidity.Backend.Executable.TransferCall
