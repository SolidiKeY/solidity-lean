import Solidity.Calculus.DecisionCompoundFieldReason
import Solidity.Calculus.DecisionUIntConstant

/-! # Closed compound-field countermodels with exact optional readings
The RHS has no scalar locals in its memory-only context. Its optional Theory
reading is preserved across all parent allocations; no halting or default-value
premise is introduced. Counterstates remain before parent allocation.
-/
namespace Solidity.Decide.ResidueReason
open Semantics (structDef lookupBy)

/-- Reuse the producer's exact finite field-realization premise. -/
theorem NonliteralUIntFreshField.fieldsMapFree {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : NonliteralUIntFreshField φ) : ∀ fT ∈ structDef w.s, fT.2.mapFree = true :=
  mapFree_structDef w.s (by simpa only [Ty.mapFree, decide_eq_true_eq] using w.mapFree)

/-- The producer child heap, with no parent allocated yet. -/
def NonliteralUIntFreshField.counterState {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : NonliteralUIntFreshField φ) (σ : State C Γ) : State C Γ :=
  (σ.adopt (MemoryWitness.children σ.heap w.s w.fieldsMapFree)).1

/-- Every closed member has a constructive countermodel, including undefined RHSs. -/
theorem NonliteralUIntFreshField.counterState_refutes {C : Contract} {φ : Fml C []}
    (w : NonliteralUIntFreshField φ) (σ : State C []) : ¬ holds (w.counterState σ) φ := by
  intro h
  let g : Grown σ.H (MObj · (.struct w.s)) :=
    MemoryWitness.children σ.heap w.s w.fieldsMapFree
  let base : State C [] := (σ.adopt g).1
  let τ0 : State C [.mem (.struct w.s)] := base.push none
  have hb : holds base (.allocAll w.x (.struct w.s)
      (.eq (MemoryWitness.fieldRead w.field) w.rhs)) :=
    Eq.mp (congrArg (fun ψ : Fml C [] => holds (w.counterState σ) ψ) w.equation) h
  cases hv : w.rhs.denote τ0 with
  | some value =>
    apply MemoryWitness.fieldEq_refutes σ g w.field w.x value
    intro o
    have he : (MemoryWitness.fieldRead w.field).denote (base.allocPush o) =
        w.rhs.denote (base.allocPush o) := hb o
    have hr : w.rhs.denote (base.allocPush o) = some value :=
      (uintLinear_memoryOnly_denote w.linear (base.allocPush o) τ0).trans hv
    exact he.trans hr
  | none =>
    let o : MObj base.H (.struct w.s) :=
      MFields.set (structDef w.s) g.val w.field (uintOfNat 0)
    have heval : (MemoryWitness.fieldRead w.field).eval (base.allocPush o) =
        some (uintOfNat 0) := by
      rw [MemoryWitness.fieldRead_eval, MFields.get_set_same]
    have hd : (MemoryWitness.fieldRead w.field).denote (base.allocPush o) =
        some (uintOfNat 0) := Tm.denote_eval _ _ _ heval
    have he : (MemoryWitness.fieldRead w.field).denote (base.allocPush o) =
        w.rhs.denote (base.allocPush o) := hb o
    rw [hd, uintLinear_memoryOnly_denote w.linear (base.allocPush o) τ0, hv] at he
    cases he

/-- The exact existing hash reading is refuted at that same before-parent state. -/
theorem NonliteralUIntFreshField.counterState_refutesH {C : Contract} {φ : Fml C []}
    (w : NonliteralUIntFreshField φ) (σ : State C []) : ¬ Fml.holdsH (w.counterState σ) φ :=
  fun h => w.counterState_refutes σ ((Fml.holdsH_iff (w.counterState σ) φ w.hashFree).mp h)

/-- A real closed-leaf Answer, ready for later lazy pipeline composition. -/
def NonliteralUIntFreshField.answer {C : Contract} {φ : Fml C []}
    (w : NonliteralUIntFreshField φ) : MemoryWitness.Answer φ :=
  .refuted w.counterState w.counterState_refutes

end Solidity.Decide.ResidueReason
