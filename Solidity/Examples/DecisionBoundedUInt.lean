import Solidity.Calculus.DecisionBoundedUInt
import Solidity.Examples.DecisionArrayGaps

/-! # Exact bounded preparation controls before pipeline integration
Original assigned array verdicts stay unchanged here. Kernel preparation facts
are separate from the executable observations of the unchanged decision route.
-/
namespace Solidity.Examples.DecisionBoundedUInt
open Solidity.Decide
open Solidity.Examples.DecisionArrayGaps
set_option Elab.async false

def yesBody : LFml Probe := .eq (p := .uint) (.var 0) (.var 0)
def belowThree : LFml Probe := .all 0 .uint (.imp (uintBelow 0 (uintOfNat 3)) yesBody)

theorem yes_body_qf : yesBody.qfB = true := rfl

theorem bounded_equivalence (g : State Probe []) (ν : AEnv) :
    (belowThree.inst (uintSamples (uintOfNat 3))).holds g ν ↔ belowThree.holds g ν :=
  boundedUInt_inst_iff g ν 0 (uintOfNat 3) yesBody yes_body_qf

theorem recognized_guard : (boundedUIntGuard? (C := Probe) 0 (uintBelow 0 (uintOfNat 3))).isSome = true := by
  decide +kernel

theorem wrong_binder_refused :
    (boundedUIntGuard? (C := Probe) 1 (uintBelow 0 (uintOfNat 3))).isNone = true := by decide +kernel

theorem three_samples : (uintSamples (C := Probe) (uintOfNat 3)).length = 3 := by decide +kernel

theorem expansion_qf : (boundedUIntPrep belowThree).body.qfB = true := by decide +kernel

def zeroBlock : LFml Probe := .all 0 .uint (.imp (uintBelow 0 (uintOfNat 0)) .ff)

theorem zero_expands_true : (boundedUIntPrep zeroBlock).body = .tt := by rfl

theorem zero_valid : zeroBlock.Valid := by
  intro g ν
  exact ((boundedUIntExpand zeroBlock).meaning g ν).mp trivial

def oversized : LFml Probe := .all 0 .uint (.imp (uintBelow 0 (uintOfNat 1000)) .tt)

/-- The resource guard returns the original binder before constructing its samples. -/
theorem oversized_preserved : (boundedUIntPrep oversized).body = oversized := by rfl

def failedTerm : LTm Probe (.val .uint) := .err
def strictFailed : LFml Probe := .eq failedTerm failedTerm
def optionalFailed : LFml Probe := LFml.optEq failedTerm failedTerm

theorem strict_failed_false (g : State Probe []) (ν : AEnv) : ¬ strictFailed.holds g ν := by
  intro h
  exact h

theorem optional_failed_true (g : State Probe []) (ν : AEnv) : optionalFailed.holds g ν := by
  exact ⟨fun h => False.elim h, ⟨fun h => False.elim h, fun h => False.elim h⟩⟩

def strictOne : LFml Probe := .all 0 .uint (.imp (uintBelow 0 (uintOfNat 1)) strictFailed)

theorem strict_one_countermodel : ¬ strictOne.holds (State.init Probe) AEnv.dflt := by
  intro h
  exact strict_failed_false _ _ (h (uintOfNat 0) rfl)

/-- Exactness transports the actual refutation of a partial operand to its expansion. -/
theorem strict_expanded_countermodel :
    ¬ (boundedUIntPrep strictOne).body.holds (State.init Probe) AEnv.dflt := by
  intro h
  exact strict_one_countermodel (((boundedUIntExpand strictOne).meaning _ _).mp h)

def realFixedLeaf : LFml Probe := (leafOf? fixedBlock).get (by decide +kernel)
def realBadLeaf : LFml Probe := (leafOf? fixedBad).get (by decide +kernel)

/-- The actual frozen-source fixed-array blocks become quantifier-free under preparation. -/
theorem actual_fixed_prepares_qf : (boundedUIntPrep realFixedLeaf).body.qfB = true := by decide +kernel

theorem actual_bad_prepares_qf : (boundedUIntPrep realBadLeaf).body.qfB = true := by decide +kernel

theorem actual_fixed_exact (g : State Probe []) (ν : AEnv) :
    (boundedUIntPrep realFixedLeaf).body.holds g ν ↔ realFixedLeaf.holds g ν :=
  (boundedUIntExpand realFixedLeaf).meaning g ν

theorem actual_bad_exact (g : State Probe []) (ν : AEnv) :
    (boundedUIntPrep realBadLeaf).body.holds g ν ↔ realBadLeaf.holds g ν :=
  (boundedUIntExpand realBadLeaf).meaning g ν

def notTwo : LFml Probe := .not (.eq (p := .uint) (.var 0) (.app0 (.lit (uintOfNat 2))))
def mustIncludeTwo : LFml Probe := .all 0 .uint (.imp (uintBelow 0 (uintOfNat 3)) notTwo)

/-- Omitting an in-range literal can pass finite samples while the universal is false. -/
theorem wrong_samples_pass (g : State Probe []) (ν : AEnv) :
    (mustIncludeTwo.inst (uintSamples (uintOfNat 2))).holds g ν := by
  exact ⟨fun _ _ => by change ¬ uintOfNat 0 = uintOfNat 2; decide +kernel,
    fun _ _ => by change ¬ uintOfNat 1 = uintOfNat 2; decide +kernel⟩

theorem omitted_instance_refutes : ¬ mustIncludeTwo.holds (State.init Probe) AEnv.dflt := by
  intro h
  exact (h (uintOfNat 2) rfl) rfl

theorem complete_samples_refute :
    ¬ (mustIncludeTwo.inst (uintSamples (uintOfNat 3))).holds (State.init Probe) AEnv.dflt := by
  intro h
  exact omitted_instance_refutes ((boundedUInt_inst_iff _ _ 0 (uintOfNat 3) notTwo rfl).mp h)

def wrongTruthGuard : LFml Probe :=
  .eq (.app2 (.binop .lt (p := .uint) rfl) (.var 0) (.app0 (.lit (uintOfNat 3)))) (.app0 (.lit false))

theorem wrong_truth_refused : (boundedUIntGuard? 0 wrongTruthGuard).isNone = true := by decide +kernel

def groundGuard : LFml Probe :=
  .eq (.app2 (.binop .lt (p := .uint) rfl) (.app0 (.lit (uintOfNat 0)))
    (.app0 (.lit (uintOfNat 3)))) (.app0 (.lit true))

theorem non_variable_guard_refused : (boundedUIntGuard? 0 groundGuard).isNone = true := by decide +kernel

end Solidity.Examples.DecisionBoundedUInt
