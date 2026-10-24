import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.Close
import Solidity.Calculus.Sound

/-!
# The public correctness judgement distinguishes good and bad executions

The negative witnesses run normally: neither a revert nor the accepted
exhaustion case can make their boxes vacuous. Soundness then rules out a
calculus derivation of the translated false specifications.
-/
namespace Solidity.Examples.Tactics.Nonvacuity

open Semantics
open scoped Scoped

def C : Contract := contract!{ }

/-- `uint x = 7;` satisfies its actual result, in every initial state. -/
def good : Spec C [] :=
  .box (sol[C]{ uint x = 7; }) (.eq (.pvV .here) (.lit ⟨7, rfl⟩))

/-- The same normally returning program does not establish `x = 8`. -/
def bad : Spec C [] :=
  .box (sol[C]{ uint x = 7; }) (.eq (.pvV .here) (.lit ⟨8, rfl⟩))

/-- Positive witness: the calculus proves the actual result. -/
theorem good_provable : Proves C .all [] .nil good.toFml := by
  unfold good Spec.toFml
  sol_prove
  sol_leaf
  sol_close

/-- The bridge yields direct program correctness for that proof. -/
theorem good_valid : ⊨ good := Proves.valid good_provable

/-- Concrete negative witness, evaluated in the kernel. -/
theorem bad_at_init : ¬ Spec.sat (State.init C) bad := by
  change ¬ (∃ v : PrimTy.uint.Denote,
    some ⟨7, by decide⟩ = some v ∧ some ⟨8, by decide⟩ = some v)
  intro ⟨v, hv, hw⟩
  have h := congrArg (fun x => x.map Subtype.val) (hv.trans hw.symm)
  contradiction

/-- A false result is not valid in all states. -/
theorem bad_invalid : ¬ (⊨ bad) := fun h => bad_at_init (h (State.init C))

/-- Soundness forbids deriving the translated false specification. -/
theorem bad_unprovable : ¬ Proves C .all [] .nil bad.toFml :=
  fun h => bad_invalid (Proves.valid h)

/-- Signed primitive captures have a real landed state too. -/
example : ⊨ (Spec.box (sol[C]{ int x = -7; })
    (.eq (.pvV .here) (.lit ⟨-7, rfl⟩))) := by
  apply Proves.valid (R := .all)
  sol_prove
  sol_leaf
  sol_close

/-- Boolean primitive captures cannot turn a true strict equation false. -/
example : ⊨ (Spec.box (sol[C]{ bool x = true; })
    (.eq (.pvV .here) (.lit true))) := by
  apply Proves.valid (R := .all)
  sol_prove
  sol_leaf
  sol_close

/-- The delayed macro resolves the lemma after it has been declared. -/
example {Δ : Ctx} (g : State C []) (ℓ : LocsV C Δ)
    (P : CloseS.Landed g ℓ → Prop) (h : ∀ x, P x) : CloseS.LandedAll g ℓ P := by
  sol_close_landed
  exact h

/-- info: 'Solidity.Examples.Tactics.Nonvacuity.good_provable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms good_provable

/-- info: 'Solidity.Examples.Tactics.Nonvacuity.bad_unprovable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bad_unprovable

end Solidity.Examples.Tactics.Nonvacuity
