import SolidityBridge.WeakestPreLaws
import Loom.MonadAlgebras.WP.Tactic

/-!
# Loom's WP reads the core run

The program is a Kleisli arrow on typed states, rather than a `StateT`:
its input and output contexts can differ. The only exception interpretation
is the core's `afterRunTR`, connected to Loom's handler algebra below.
No `NoFailure` instance is supplied: even box rejects panic.
-/

namespace Solidity.Bridge.Loom

/-- The actual modal error policy, including the separate panic check. -/
def haltPolicy (m : Modality) (e : THalt) : Prop :=
  m.onTHalt e ∧ e ≠ .panic

/-- Use Loom's own parameterized exception algebra over the identity monad. -/
noncomputable def algebra (m : Modality) : MAlgOrdered (ExceptT THalt Id) Prop :=
  MAlgExcept THalt (haltPolicy m) Prop Id

/-- Loom's WP of the actual result; `ExceptT THalt Id α` reduces to `TRes α`. -/
noncomputable def loomWp {α : Type} (m : Modality) (r : TRes α) (q : α → Prop) : Prop :=
  letI : MAlgOrdered (ExceptT THalt Id) Prop := algebra m
  _root_.wp (m := ExceptT THalt Id) r q

theorem loomWp_iff_afterRunTR {α : Type} (m : Modality) (r : TRes α) (q : α → Prop) :
    loomWp m r q ↔ m.afterRunTR q r := by
  cases r with
  | ok a =>
    change q a ↔ m.afterRunTR q (.ok a)
    simp only [Modality.afterRunTR, ne_eq, reduceCtorEq, not_false_eq_true, and_true]
  | error e =>
    change (LE.pure (haltPolicy m e) : Prop) ↔ m.afterRunTR q (.error e)
    simp only [purePropE, haltPolicy, Modality.afterRunTR, ne_eq, Except.error.injEq]

/-- Equality of predicate transformers, not an alternative program semantics. -/
theorem loomWp_eq_wp {α β : Type} (m : Modality) (run : α → TRes β) (q : Set β) :
    (fun σ => loomWp m (run σ) q) = Bridge.wp m run q := by
  funext σ
  exact propext (loomWp_iff_afterRunTR m (run σ) q)

/-- Bind is inherited from the bridge's law for the core's actual halt policy. -/
theorem loomWp_bind {α β : Type} (m : Modality) (r : TRes α)
    (next : α → TRes β) (q : β → Prop) :
    loomWp m (r >>= next) q ↔ loomWp m r (fun a => loomWp m (next a) q) := by
  have h : (fun _ : Unit => loomWp m (r >>= next) q) =
      (fun _ : Unit => loomWp m r (fun a => loomWp m (next a) q)) := by
    simp only [loomWp_eq_wp, Bridge.wp_comp]
  exact Iff.of_eq (congrFun h ())

/-- Loom generators with the modality's explicitly selected algebra. -/
abbrev Generator {α : Type} (m : Modality) (r : TRes α) : Type :=
  @WPGen (ExceptT THalt Id) inferInstance α Prop inferInstance (algebra m) r

end Solidity.Bridge.Loom

/-- info: 'Solidity.Bridge.Loom.loomWp_iff_afterRunTR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Bridge.Loom.loomWp_iff_afterRunTR
/-- info: 'Solidity.Bridge.Loom.loomWp_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Bridge.Loom.loomWp_bind
