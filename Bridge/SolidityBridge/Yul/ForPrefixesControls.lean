import SolidityBridge.Yul.ForPrefixes
import SolidityBridge.Yul.StructuredForControls

/-! Genuine all-horizon/noncompletion and all finite macro-prefix witnesses
for the existing original FOR with a false high-word flag and counter99.
Never evaluate its whole unending target. Model fault below is denotational
noncompletion, not an exceptional native halt or source revert/panic. -/
namespace SolidityBridge.Yul.ForPrefixes.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Closed
open Solidity.Yul.Compilation ProducerExpressions
abbrev dirty := StructuredFor.Controls.dirty
abbrev test := StructuredFor.Controls.test
abbrev after := StructuredFor.Controls.after
abbrev inside := StructuredFor.Controls.inside
abbrev before := StructuredFor.Controls.before
abbrev statement := StructuredFor.Controls.statement
abbrev actualProfile := StructuredFor.Controls.actualProfile
abbrev target := StructuredFor.Controls.target
abbrev selected := StructuredFor.Controls.selected
abbrev machine := StructuredFor.Controls.machine

def initial : Vector Scalar.Word 3 := #v[99,dirty,0]
def update (locals : Vector Scalar.Word 3) := after.update (inside.update locals)

private theorem before_zero (locals : Vector Scalar.Word 3) (zero : locals[2] = 0) :
    before.update locals = locals := by
  change (if locals[2] = 0 then locals else _) = locals
  rw [if_pos zero]
private theorem inside_zero (locals : Vector Scalar.Word 3) (zero : locals[2] = 0) :
    inside.update locals = locals := by
  change (if locals[2] = 0 then locals else _) = locals
  rw [if_pos zero]
private theorem after_counter (locals : Vector Scalar.Word 3) :
    (after.update locals)[0] = locals[0] := by
  change (if locals[0] = 0 then locals else locals.set 1 _ (by decide))[0] = locals[0]
  split <;> simp only [Vector.getElem_set,show ¬ (1 : Nat)=0 by decide,ite_false]
private theorem after_flag (locals : Vector Scalar.Word 3) :
    (after.update locals)[2] = locals[2] := by
  change (if locals[0] = 0 then locals else locals.set 1 _ (by decide))[2] = locals[2]
  split <;> simp only [Vector.getElem_set,show ¬ (1 : Nat)=2 by decide,ite_false]

theorem invariant (count : Nat) :
    (Nat.repeat update count initial)[0] = 99 ∧ (Nat.repeat update count initial)[2] = 0 := by
  induction count with
  | zero => exact ⟨rfl,rfl⟩
  | succ count ih =>
    change (after.update (inside.update (Nat.repeat update count initial)))[0] = 99 ∧
      (after.update (inside.update (Nat.repeat update count initial)))[2] = 0
    rw [inside_zero _ ih.2]
    exact ⟨(after_counter _).trans ih.1,(after_flag _).trans ih.2⟩

theorem forever_guard (count : Nat) : test.value (Nat.repeat update count initial) ≠ 0 := by
  change (Nat.repeat update count initial)[0] ≠ 0
  rw [(invariant count).1]
  decide

theorem source_all_horizons (fuel : Nat) :
    evalStmt fuel .nil True.intro statement actualProfile (sourceLocals initial) = none := by
  apply source_never (c := ⟨false,false⟩) test after inside before initial _ fuel
  intro count
  rw [before_zero initial rfl]
  exact forever_guard count

def cc := (test.lowered.code 2).get (by rfl)
def bodyBlock := (inside.emit 2).get (by rfl)
def postBlock := (after.emit 2).get (by rfl)
def preBlock := (before.emit 2).get (by rfl)
def condSlice := (OccurrenceSelection.selectCode cc).get (by rfl)
def bodySelected := (LoopSelection.selectBlock (.seq bodyBlock postBlock)).get (by rfl)
def preSelected := (LoopSelection.selectBlock preBlock).get (by rfl)

/-- Exact actual model continuation for every count and arbitrary caller/frame.
The output uses actual compiled iteration, not a desired-run hypothesis. -/
theorem every_macro_prefix (count : Nat) (tail : Stack) (m : Evm.Machine)
    (represented : m.stack = irStack ([77,dirty] ++ (initial.toList ++ tail))) :
    Evm.loopIterN (Evm.run condSlice.ir) (Evm.run bodySelected.realization.ir) count m =
      .inl {m with stack := irStack ([77,dirty] ++ ((Nat.repeat update count initial).toList ++ tail))} :=
  macro_prefix (c := ⟨false,false⟩) test after inside 2 cc postBlock bodyBlock rfl rfl rfl
    condSlice bodySelected.realization count initial #v[77,dirty] tail
    (fun j _ => forever_guard j) m represented

theorem loop_no_finite_outcome (tail : Stack) (m : Evm.Machine)
    (represented : m.stack = irStack ([77,dirty] ++ (initial.toList ++ tail))) :
    Evm.loopRun (Evm.run condSlice.ir) (Evm.run bodySelected.realization.ir) m = .fault :=
  model_loop_no_finite_outcome (c := ⟨false,false⟩) test after inside 2 cc postBlock bodyBlock
    rfl rfl rfl condSlice bodySelected.realization initial #v[77,dirty] tail forever_guard m represented

/-- Whole actual selected original FOR model denotation, including its prelude.
This is still the model's noncompletion encoding, not native exceptional halt. -/
theorem whole_model_no_finite_outcome (tail : Stack) (m : Evm.Machine)
    (represented : m.stack = irStack ([77,dirty] ++ (initial.toList ++ tail))) :
    Evm.run selected.realization.ir m = .fault := by
  have preRun := preSelected.realization.execute _ _ m represented
    (StructuredSource.structured before 2 preBlock rfl initial #v[77,dirty] tail)
  rw [before_zero initial rfl] at preRun
  change Evm.run preSelected.realization.ir m =
    .ok {m with stack := irStack ([77,dirty] ++ (initial.toList ++ tail))} 0 at preRun
  rw [←represented] at preRun
  change Evm.run preSelected.realization.ir m = .ok m 0 at preRun
  change Evm.run (preSelected.realization.ir ++ [.loop condSlice.ir bodySelected.realization.ir]) m = .fault
  rw [Evm.run_append_ok preRun]
  change (Evm.loopRun (Evm.run condSlice.ir) (Evm.run bodySelected.realization.ir) m).bind _ = .fault
  rw [loop_no_finite_outcome tail m represented]
  rfl

/-- The previous high-flag terminating witness cannot satisfy the forever guard. -/
theorem finite_guard_refused : ¬ (∀ j, test.value (Nat.repeat update j
    (before.update #v[99,dirty,StructuredFor.Controls.high])) ≠ 0) := by
  intro forever
  exact forever 2 (by decide)

-- Evaluate only a bounded macro-prefix; never Evm.run selected on initial.
#guard match Evm.loopIterN (Evm.run condSlice.ir) (Evm.run bodySelected.realization.ir) 3
  (machine [77,dirty,99,dirty,0,88]) with
  | .inl next => next.stack == irStack [77,dirty,99,dirty+3,0,88]
  | .inr _ => false
#check StructuredFor.Controls.source_eight
#check source_all_horizons 0
#check source_all_horizons 8
#check every_macro_prefix 0

/-- info: 'SolidityBridge.Yul.ForPrefixes.Controls.invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms invariant
/-- info: 'SolidityBridge.Yul.ForPrefixes.Controls.forever_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms forever_guard
/-- info: 'SolidityBridge.Yul.ForPrefixes.Controls.source_all_horizons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_all_horizons
/-- info: 'SolidityBridge.Yul.ForPrefixes.Controls.every_macro_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms every_macro_prefix
/-- info: 'SolidityBridge.Yul.ForPrefixes.Controls.loop_no_finite_outcome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loop_no_finite_outcome
/-- info: 'SolidityBridge.Yul.ForPrefixes.Controls.whole_model_no_finite_outcome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms whole_model_no_finite_outcome
/-- info: 'SolidityBridge.Yul.ForPrefixes.Controls.finite_guard_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms finite_guard_refused
end SolidityBridge.Yul.ForPrefixes.Controls
