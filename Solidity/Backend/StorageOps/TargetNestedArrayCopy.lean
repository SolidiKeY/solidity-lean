import Solidity.Backend.StorageOps.TargetArrayCopyTail

/-! Runtime OUTER index computes actual inner storage headers. Inner execution
uses checked target instructions, not semantic overlay/clear. Outer loop proofs
live in the CopyLoop/ClearLoop modules; independent aggregate correspondence
remains a separate obligation. -/
namespace Solidity.Backend.StorageOps.TargetNestedArrayCopy

def copyOperands : List Evm.Instr := [.dup 4,.keccakArr,.dup 2,.add,.dup 4,.keccakArr,.dup 3,.add]
def clearOperands : List Evm.Instr := [.dup 3,.keccakArr,.dup 2,.add]
def increment : List Evm.Instr := [.push (.val ⟨1,by decide⟩),.add]
def copyBody : List Evm.Instr := (copyOperands ++ TargetArrayCopy.code) ++ increment
def clearBody : List Evm.Instr := (clearOperands ++ TargetArrayClear.code) ++ increment

def code : List Evm.Instr := TargetArrayCopy.setup ++ [.loop TargetArrayCopy.condition copyBody] ++
  TargetArrayCopy.transition ++ [.loop TargetArrayClear.condition clearBody] ++ TargetArrayCopy.finish

theorem run_copy_operands (machine : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (i limit oldLength : Fin Evm.W) :
    Evm.run copyOperands { machine with stack := .val i :: .val limit :: .slot src :: .slot dst :: .val oldLength :: tail } =
      .ok { machine with stack := .slot (.data src i.val) :: .slot (.data dst i.val) :: .val i :: .val limit :: .slot src :: .slot dst :: .val oldLength :: tail } 0 := by
  simp only [copyOperands,Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Evm.Slot.add,Nat.zero_add]

theorem run_clear_operands (machine : Evm.Machine) (tail : List Evm.Word) (dst : Evm.Slot)
    (i oldLength newLength : Fin Evm.W) :
    Evm.run clearOperands { machine with stack := .val i :: .val oldLength :: .slot dst :: .val newLength :: tail } =
      .ok { machine with stack := .slot (.data dst i.val) :: .val i :: .val oldLength :: .slot dst :: .val newLength :: tail } 0 := by
  simp only [clearOperands,Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Evm.Slot.add,Nat.zero_add]

/-- CURRENT inner headers/payloads drive the genuine inner two-loop copy. The
outer runtime counter and captured metadata are preserved below its operands. -/
theorem run_copy_child (machine : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (i limit oldLength : Fin Evm.W) :
    Evm.run (copyOperands ++ TargetArrayCopy.code)
      { machine with stack := .val i :: .val limit :: .slot src :: .slot dst :: .val oldLength :: tail } =
      .ok (TargetArrayCopyTail.afterCopy machine
        (.val i :: .val limit :: .slot src :: .slot dst :: .val oldLength :: tail) (.data src i.val) (.data dst i.val)) 0 := by
  rw [Evm.run_append_ok (run_copy_operands machine tail src dst i limit oldLength)]
  exact TargetArrayCopyTail.run_current _ _ _ _

/-- A stale OUTER child executes the actual inner live-prefix clear program;
inner older shadows remain protected by its existing checked specification. -/
theorem run_clear_child (machine : Evm.Machine) (tail : List Evm.Word) (dst : Evm.Slot)
    (i oldLength newLength : Fin Evm.W) :
    Evm.run (clearOperands ++ TargetArrayClear.code)
      { machine with stack := .val i :: .val oldLength :: .slot dst :: .val newLength :: tail } =
      .ok (TargetArrayClear.afterClear machine
        (.val i :: .val oldLength :: .slot dst :: .val newLength :: tail) (.data dst i.val)) 0 := by
  rw [Evm.run_append_ok (run_clear_operands machine tail dst i oldLength newLength)]
  exact TargetArrayClear.run_current _ _ _

theorem run_increment (machine : Evm.Machine) (tail : List Evm.Word) (i : Fin Evm.W)
    (next : i.val+1 < Evm.W) :
    Evm.run increment { machine with stack := .val i :: tail } =
      .ok { machine with stack := .val ⟨i.val+1,next⟩ :: tail } 0 := by
  simp only [increment,Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind]
  rw [show 1+i.val = i.val+1 by omega,Evm.wmod_of_lt next]

theorem run_copy_body (machine : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (i limit oldLength : Fin Evm.W) (next : i.val+1 < Evm.W) :
    Evm.run copyBody { machine with stack := .val i :: .val limit :: .slot src :: .slot dst :: .val oldLength :: tail } =
      .ok { TargetArrayCopyTail.afterCopy machine
        (.val i :: .val limit :: .slot src :: .slot dst :: .val oldLength :: tail) (.data src i.val) (.data dst i.val) with
        stack := .val ⟨i.val+1,next⟩ :: .val limit :: .slot src :: .slot dst :: .val oldLength :: tail } 0 := by
  rw [copyBody,Evm.run_append_ok (run_copy_child machine tail src dst i limit oldLength)]
  exact run_increment (TargetArrayCopyTail.afterCopy machine
    (.val i :: .val limit :: .slot src :: .slot dst :: .val oldLength :: tail) (.data src i.val) (.data dst i.val))
    (.val limit :: .slot src :: .slot dst :: .val oldLength :: tail) i next

theorem run_clear_body (machine : Evm.Machine) (tail : List Evm.Word) (dst : Evm.Slot)
    (i oldLength newLength : Fin Evm.W) (next : i.val+1 < Evm.W) :
    Evm.run clearBody { machine with stack := .val i :: .val oldLength :: .slot dst :: .val newLength :: tail } =
      .ok { TargetArrayClear.afterClear machine
        (.val i :: .val oldLength :: .slot dst :: .val newLength :: tail) (.data dst i.val) with
        stack := .val ⟨i.val+1,next⟩ :: .val oldLength :: .slot dst :: .val newLength :: tail } 0 := by
  rw [clearBody,Evm.run_append_ok (run_clear_child machine tail dst i oldLength newLength)]
  exact run_increment (TargetArrayClear.afterClear machine
    (.val i :: .val oldLength :: .slot dst :: .val newLength :: tail) (.data dst i.val))
    (.val oldLength :: .slot dst :: .val newLength :: tail) i next

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayCopy.copyOperands' does not depend on any axioms -/
#guard_msgs in #print axioms copyOperands
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayCopy.clearOperands' does not depend on any axioms -/
#guard_msgs in #print axioms clearOperands
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayCopy.increment' does not depend on any axioms -/
#guard_msgs in #print axioms increment
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayCopy.copyBody' does not depend on any axioms -/
#guard_msgs in #print axioms copyBody
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayCopy.clearBody' does not depend on any axioms -/
#guard_msgs in #print axioms clearBody
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayCopy.code' does not depend on any axioms -/
#guard_msgs in #print axioms code
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayCopy.run_copy_operands' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms run_copy_operands
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayCopy.run_clear_operands' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms run_clear_operands
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayCopy.run_copy_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms run_copy_child
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayCopy.run_clear_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms run_clear_child
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayCopy.run_increment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms run_increment
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayCopy.run_copy_body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms run_copy_body
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayCopy.run_clear_body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms run_clear_body

end Solidity.Backend.StorageOps.TargetNestedArrayCopy
