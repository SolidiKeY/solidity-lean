import Solidity.Yul.Compilation.ShapeCapacity

/-! Actual last-accessible DUP16/SWAP16 arithmetic update. Static operand
availability, caller framing and every-boundary capacity are independent. -/
namespace Solidity.Yul.Compilation.ShapeCapacity.Controls
open Backend Scalar LabelExec

def code : Program := [.op (.DUP 15),pushByte 1,.op .ADD,.op (.SWAP 15),.op .POP]
def dirty : Word := BitVec.ofNat 256 (2^200+257)
def locals : Vector Word 16 := #v[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,dirty]
def final : Vector Word 16 := #v[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,dirty+1]

theorem shape : CodeShape code 16 16 := by
  exact .cons (.mk 16 17 0 rfl rfl rfl)
    (.cons (.mk 0 1 17 rfl rfl rfl)
      (.cons (.mk 2 1 16 rfl rfl rfl)
        (.cons (.mk 17 17 0 rfl rfl rfl)
          (.cons (.mk 1 0 16 rfl rfl rfl) (.nil 16)))))

/-- All sixteen raw local words, not just this finite example, have a derived
actual result of length sixteen, independently of every caller value. -/
theorem every_input (values : Vector Word 16) :
    ∃ output : Stack, output.length = 16 ∧ run code values.toList = some output ∧
      ∀ caller : Stack, run code (values.toList ++ caller) = some (output ++ caller) :=
  code_frame shape values

theorem actual_update : run code locals.toList = some final.toList := by decide

theorem caller_preserved (caller : Stack) :
    run code (locals.toList ++ caller) = some (final.toList ++ caller) :=
  run_frame actual_update caller

theorem trace (height : Int) : heightTrace code height =
    [height,height+1,height+2,height+1,height+1,height] := by
  change [height,height+1,(height+1)+1,((height+1)+1)+(-1),
    (((height+1)+1)+(-1))+0,((((height+1)+1)+(-1))+0)+(-1)] = _
  simp only [Int.add_assoc,Int.reduceAdd,Int.add_zero]

theorem capacity_exact (height : Int) :
    stackBound code height = true ↔ 0 ≤ height ∧ height+2 ≤ 1024 := by
  simp only [stackBound,trace,List.all_cons,List.all_nil,Bool.and_true,
    Bool.and_eq_true,safeHeight,decide_eq_true_eq]
  omega

theorem caller_capacity_exact (caller : Stack) :
    stackBound code ((16+caller.length : Nat) : Int) = true ↔ caller.length ≤ 1006 := by
  rw [capacity_exact]
  omega

/-- Scalar execution still succeeds one caller word beyond the admitted
prefix capacity, even though both entry and final heights fit within1024. -/
theorem overflow_is_not_underflow :
    run code (locals.toList ++ List.replicate 1007 dirty) =
      some (final.toList ++ List.replicate 1007 dirty) ∧
    stackBound code 1023 = false ∧ (16+1007 : Nat) ≤ 1024 :=
  ⟨caller_preserved _,by decide,by decide⟩

#guard run code (List.replicate 15 dirty) == none
#guard step (.op (.SWAP 15)) (List.replicate 16 dirty) == none
#guard stackBound code 1022
#guard !(stackBound code 1023)
#guard dirty.toNat = 2^200+257
#guard (dirty+1).toNat = 2^200+258
#check every_input locals
#check caller_preserved [dirty,88]
#check framed_capacity shape locals [dirty,88] (by decide)
/-- info: 'Solidity.Yul.Compilation.ShapeCapacity.Controls.shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms shape
/-- info: 'Solidity.Yul.Compilation.ShapeCapacity.Controls.every_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms every_input
/-- info: 'Solidity.Yul.Compilation.ShapeCapacity.Controls.actual_update' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms actual_update
/-- info: 'Solidity.Yul.Compilation.ShapeCapacity.Controls.caller_preserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms caller_preserved
/-- info: 'Solidity.Yul.Compilation.ShapeCapacity.Controls.trace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms trace
/-- info: 'Solidity.Yul.Compilation.ShapeCapacity.Controls.capacity_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms capacity_exact
/-- info: 'Solidity.Yul.Compilation.ShapeCapacity.Controls.caller_capacity_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms caller_capacity_exact
/-- info: 'Solidity.Yul.Compilation.ShapeCapacity.Controls.overflow_is_not_underflow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms overflow_is_not_underflow
end Solidity.Yul.Compilation.ShapeCapacity.Controls
