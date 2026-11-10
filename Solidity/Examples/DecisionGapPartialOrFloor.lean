import Solidity.Calculus.Decision
import Solidity.Calculus.Surface

/-!
# Partial-OR floor family: both polarities, decided

`(∀ uint i; ∀ uint j; ((i ≤ j && i < cap - 1) || i ≤ i) == true → owed[i] == v)
→ owed[k] == r` over a contract with a second uint root, so that discovery
must pick the right pair of roots. The claim is valid exactly when `0 < k`
and `r = v`; every other member is refuted at the symbolic region state
(`cap = 0`, `owed` reads `v` everywhere but key zero). A guard with a total
bound (`cap + 1`) is not a member.
-/
namespace Solidity.Examples.DecisionGapPartialOrFloor
open Solidity.Decide Solidity.Decide.ResidueReason
set_option Elab.async false

def Floors : Contract := contract!{ uint other; mapping(uint => uint) owed; uint cap; }

def roots : PartialOrRoots Floors := ⟨"cap", "owed", rfl, rfl⟩

/-- `owed[k] == r` under the block `owed[i] == v`. -/
def claim (v k r : Nat) : Fml Floors [] :=
  roots.sourceClaim (.user "i") (.user "j") (uintOfNat v) (uintOfNat k) (uintOfNat r)

/-- Valid: a positive key with the block's value. -/
def good : Fml Floors [] := claim 5 2 5
/-- Refuted: key zero is unconstrained when `cap = 0`. -/
def atZero : Fml Floors [] := claim 5 0 5
/-- Refuted: the wrong value at a positive key. -/
def wrongValue : Fml Floors [] := claim 5 3 4

/-- The same shape with a total bound `cap + 1` is not a member. Written with
constructors: `dl{}` has no spelling for a `&&` nested under `||` in a guard
(`docs/automation.md`, unpinned shapes), the same reason `PartialOrRoots.sourceGuard`
is built this way. -/
def totalGuard : Tm Floors [.val .uint, .val .uint] (.val .bool) :=
  .app2 (.binop .or rfl)
    (.app2 (.binop .and rfl)
      (.app2 (.binop .le (p := .uint) rfl) (.pvV (.there .here)) (.pvV .here))
      (.app2 (.binop .lt (p := .uint) rfl) (.pvV (.there .here))
        (.app2 (.binop .add rfl) roots.scalarRead (.app0 (.lit (uintOfNat 1))))))
    (.app2 (.binop .le (p := .uint) rfl) (.pvV (.there .here)) (.pvV (.there .here)))
/-- The total-bound claim, otherwise the shape of `good`. -/
def totalClaim : Fml Floors [] :=
  .imp (.all (.user "i") .uint (.all (.user "j") .uint
    (.imp (.eq totalGuard (.app0 (.lit true)))
      (.eq (roots.mapRead (.pvV (.there .here))) (.app0 (.lit (uintOfNat 5)))))))
    (.eq (roots.mapRead (.app0 (.lit (uintOfNat 2)))) (.app0 (.lit (uintOfNat 5))))

@[noinline] def observe (φ : Fml Floors []) : Bool × Bool × Bool × String :=
  (φ.inTarget {}, φ.partialOrFloor, φ.Covered, match decideGoal φ with
    | .proved => "proved" | .refuted _ => "refuted" | .unknown => "unknown")

/-- info: [(true, true, true, "proved"), (true, true, true, "refuted"), (true, true, true, "refuted")] -/
#guard_msgs in #eval [good, atZero, wrongValue].map observe

/-- The three claims are members; the total-bound guard is not. -/
theorem members : good.partialOrFloor = true ∧ atZero.partialOrFloor = true ∧
    wrongValue.partialOrFloor = true ∧ totalClaim.partialOrFloor = false := by
  decide +kernel

/-- All three members are in the target. -/
theorem targets : good.inTarget {} = true ∧ atZero.inTarget {} = true ∧
    wrongValue.inTarget {} = true := by decide +kernel

/-- `owed[2] == 5`: covered. -/
theorem good_covered : good.Covered = true := by decide +kernel
/-- `owed[0] == 5`: covered. -/
theorem atZero_covered : atZero.Covered = true := by decide +kernel
/-- `owed[3] == 4`: covered. -/
theorem wrongValue_covered : wrongValue.Covered = true := by decide +kernel

/-- Coverage and the exact family semantics force the certified verdict. -/
theorem good_proved : decideGoal good = .proved := by
  have hv : Fml.Valid good :=
    (PartialOrBlockAt.valid_positive (sp := roots) (value := uintOfNat 5)
      (key := uintOfNat 2) ⟨.user "i", .user "j", rfl⟩ (by decide))
  have hd : decideGoal good ≠ .unknown := decideGoal_complete good_covered rfl
  cases he : decideGoal good with
  | proved => rfl
  | refuted σ =>
    exact absurd ((Fml.holdsH_iff σ good rfl).mpr (hv σ)) (decideGoal_refutes he)
  | unknown => exact absurd he hd

/-- The symbolic region state, independently of the decider, refutes key zero. -/
theorem atZero_countermodel :
    ¬ holds (roots.counterState (uintOfNat 5) (uintOfNat 5)) atZero :=
  roots.sourceClaim_counter_refutes _ _ _ _ _ (by decide)

/-- The region state refutes the wrong value, independently of the decider. -/
theorem wrongValue_countermodel :
    ¬ holds (roots.counterState (uintOfNat 5) (uintOfNat 4)) wrongValue :=
  roots.sourceClaim_counter_refutes _ _ _ _ _ (by decide)

private def refutedCheck : LeafVerdict Floors → Bool
  | .refuted _ => true
  | _ => false

private theorem refuted_of_check (φ : Fml Floors [])
    (h : refutedCheck (decideGoal φ) = true) :
    ∃ σ : State Floors [], decideGoal φ = .refuted σ ∧ ¬ Fml.holdsH σ φ := by
  cases hd : decideGoal φ with
  | proved => rw [hd] at h; cases h
  | refuted σ => exact ⟨σ, rfl, decideGoal_refutes hd⟩
  | unknown => rw [hd] at h; cases h

/-- The decider returns a certified countermodel. -/
theorem atZero_refuted : ∃ σ : State Floors [],
    decideGoal atZero = .refuted σ ∧ ¬ Fml.holdsH σ atZero :=
  refuted_of_check atZero (by decide +kernel)

/-- The decider returns a certified countermodel for the wrong value. -/
theorem wrongValue_refuted : ∃ σ : State Floors [],
    decideGoal wrongValue = .refuted σ ∧ ¬ Fml.holdsH σ wrongValue :=
  refuted_of_check wrongValue (by decide +kernel)

/-- Key zero is not valid. -/
theorem atZero_notValid : ¬ Fml.Valid atZero := fun h => atZero_countermodel (h _)
/-- The wrong value is not valid. -/
theorem wrongValue_notValid : ¬ Fml.Valid wrongValue := fun h => wrongValue_countermodel (h _)

/-- info: 'Solidity.Decide.ResidueReason.PartialOrFloor.valid_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PartialOrFloor.valid_iff
/-- info: 'Solidity.Examples.DecisionGapPartialOrFloor.good_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms good_proved
/-- info: 'Solidity.Examples.DecisionGapPartialOrFloor.atZero_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms atZero_refuted
/--
info: 'Solidity.Examples.DecisionGapPartialOrFloor.wrongValue_countermodel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms wrongValue_countermodel

end Solidity.Examples.DecisionGapPartialOrFloor
