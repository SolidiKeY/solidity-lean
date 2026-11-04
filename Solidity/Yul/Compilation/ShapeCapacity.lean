import Solidity.Backend.LabelExec.FragmentSound

/-! Consumer laws for the existing intrinsically indexed numeric CodeShape.
Operand existence derives actual scalar execution; arbitrary caller tails are
then framed by the existing executor law. Capacity is checked separately at
all actual shifted boundaries, not inferred from successful execution. -/
namespace Solidity.Yul.Compilation.ShapeCapacity
open Backend Scalar LabelExec

/-- Construct a real scalar result from intrinsic static operand heights. -/
theorem code_total {p : Program} {n m : Nat} (shape : CodeShape p n m)
    (s : Stack) (sized : s.length = n) :
    ∃ t : Stack, run p s = some t ∧ t.length = m := by
  induction shape generalizing s with
  | nil n => exact ⟨s,rfl,sized⟩
  | @cons i p n mid m head rest ih =>
    rcases head with ⟨a,b,suffix,row,hin,hout⟩
    obtain ⟨next,stepped,nextLength⟩ := arity_domain i a b suffix s row (sized.trans hin)
    obtain ⟨t,completed,finalLength⟩ := ih next (nextLength.trans hout.symm)
    refine ⟨t,?_,finalLength⟩
    simpa only [run,stepped,Option.bind_some] using completed

/-- One actual output is derived before any caller tail is chosen. -/
theorem code_frame {p : Program} {n m : Nat} (shape : CodeShape p n m)
    (locals : Vector Word n) :
    ∃ t : Stack, t.length = m ∧ run p locals.toList = some t ∧
      ∀ caller : Stack, run p (locals.toList ++ caller) = some (t ++ caller) := by
  obtain ⟨t,completed,sized⟩ := code_total shape locals.toList (by simp only [Vector.length_toList])
  exact ⟨t,sized,completed,fun caller => run_frame completed caller⟩

/-- Static operand sufficiency can be lifted; this is not a capacity waiver. -/
theorem instruction_lift {i : Instr} {n m : Nat} (shape : InstrShape i n m) (extra : Nat) :
    InstrShape i (n+extra) (m+extra) := by
  rcases shape with ⟨a,b,suffix,row,hin,hout⟩
  exact .mk a b (suffix+extra) row (by omega) (by omega)

theorem code_lift {p : Program} {n m : Nat} (shape : CodeShape p n m) (extra : Nat) :
    CodeShape p (n+extra) (m+extra) := by
  induction shape with
  | nil n => exact .nil (n+extra)
  | cons head rest ih => exact .cons (instruction_lift head extra) ih

/-- Every boundary shifts, including entry and exit. No run premise. -/
theorem trace_shift (p : Program) (height extra : Int) :
    heightTrace p (height+extra) = (heightTrace p height).map (fun h => h+extra) := by
  induction p generalizing height with
  | nil => rfl
  | cons i p ih =>
    simp only [heightTrace,List.map_cons]
    rw [show (height+extra)+stackDelta i = (height+stackDelta i)+extra by omega,ih]

/-- The exact real 1024-word check after adding a caller height; no maximum
height estimate or final-height-only substitute is accepted. -/
theorem capacity_shift (p : Program) (height extra : Int) :
    stackBound p (height+extra) = true ↔
      ∀ h, h ∈ heightTrace p height → 0 ≤ h+extra ∧ h+extra ≤ 1024 := by
  simp only [stackBound,trace_shift,List.all_map,List.all_eq_true,Function.comp_apply,
    safeHeight,decide_eq_true_eq]

/-- Actual result and caller preservation plus separately supplied all-prefix
capacity. This is scalar numeric capacity, not charged/native EVM adequacy. -/
theorem framed_capacity {p : Program} {n m : Nat} (shape : CodeShape p n m)
    (locals : Vector Word n) (caller : Stack)
    (capacity : stackBound p ((n+caller.length : Nat) : Int) = true) :
    ∃ t : Stack, t.length = m ∧ run p (locals.toList ++ caller) = some (t ++ caller) ∧
      m+caller.length ≤ 1024 := by
  obtain ⟨t,sized,completed,framed⟩ := code_frame shape locals
  have bounded := run_capacity (framed caller) (by
    simpa only [List.length_append,Vector.length_toList] using capacity)
  refine ⟨t,sized,framed caller,?_⟩
  simpa only [List.length_append,sized] using bounded
/-- info: 'Solidity.Yul.Compilation.ShapeCapacity.code_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms code_total
/-- info: 'Solidity.Yul.Compilation.ShapeCapacity.code_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms code_frame
/-- info: 'Solidity.Yul.Compilation.ShapeCapacity.instruction_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms instruction_lift
/-- info: 'Solidity.Yul.Compilation.ShapeCapacity.code_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms code_lift
/-- info: 'Solidity.Yul.Compilation.ShapeCapacity.trace_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms trace_shift
/-- info: 'Solidity.Yul.Compilation.ShapeCapacity.capacity_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms capacity_shift
/-- info: 'Solidity.Yul.Compilation.ShapeCapacity.framed_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms framed_capacity
end Solidity.Yul.Compilation.ShapeCapacity
