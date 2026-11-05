import Solidity.Calculus.DecisionResidueReasons
import Solidity.Calculus.DecisionUIntRecognizer

/-! # Nonliteral uint-linear right-hand sides in fresh-field equations
A second exact source reason, independent of coverage/verdicts and separately
named from equation reversal. Existing arithmetic syntax evidence is reused.
-/
namespace Solidity.Decide.ResidueReason
open Semantics (structDef lookupBy)

structure NonliteralUIntFreshField {C : Contract} {Γ : Ctx} (φ : Fml C Γ) where
  x : Var
  s : Name
  f : Name
  field : lookupBy f (structDef s) = some (.prim .uint)
  rhs : Tm C (.mem (.struct s) :: Γ) (.val .uint)
  linear : rhs.UIntLinear
  nonliteral : (MemoryWitness.literalTerm rhs).isSome = false
  mapFree : (Ty.ref (.struct s)).mapFree = true
  equation : φ = .allocAll x (.struct s) (.eq (MemoryWitness.fieldRead field) rhs)

def NonliteralUIntFreshField.cast {C : Contract} {Γ : Ctx} {φ ψ : Fml C Γ}
    (h : φ = ψ) (w : NonliteralUIntFreshField ψ) : NonliteralUIntFreshField φ := h.symm ▸ w

private def nonliteralEquation? {C : Contract} {Γ : Ctx} (x : Var) (s : Name)
    (hm : (Ty.ref (.struct s)).mapFree = true) (body : Fml C (.mem (.struct s) :: Γ))
    (e : MemoryWitness.EqView body) :
    Option (NonliteralUIntFreshField (.allocAll x (.struct s) body)) := by
  rcases e with ⟨p, a, b, heq⟩
  cases p with
  | bool | int => exact none
  | uint =>
    exact if hn : (MemoryWitness.literalTerm b).isSome = false then
      if hg : b.uintLinearShape = true then
        (structDef s).findSome? fun fT =>
          if hf : lookupBy fT.1 (structDef s) = some (.prim .uint) then
            if ha : a.beqR (MemoryWitness.fieldRead hf) = true then
              some ⟨x, s, fT.1, hf, b, b.uintLinearShape_sound hg, hn, hm, by
                exact congrArg (Fml.allocAll x (.struct s))
                  (heq.trans (congrArg (fun lhs => Fml.eq lhs b) (Tm.eq_of_beqR ha)))⟩
            else none
          else none
      else none
    else none

private def nonliteralStructBody? {C : Contract} {Γ : Ctx} (x : Var) (s : Name)
    (hm : (Ty.ref (.struct s)).mapFree = true) (body : Fml C (.mem (.struct s) :: Γ)) :
    Option (NonliteralUIntFreshField (.allocAll x (.struct s) body)) := do
  let e ← MemoryWitness.eqView body
  nonliteralEquation? x s hm body e

private def nonliteralBound? {C : Contract} {Γ : Ctx} (x : Var) :
    (R : RefTy) → (body : Fml C (.mem R :: Γ)) →
      Option (NonliteralUIntFreshField (.allocAll x R body))
  | .struct s, body =>
    if hm : (Ty.ref (.struct s)).mapFree = true then nonliteralStructBody? x s hm body
    else none
  | _, _ => none

def nonliteralUIntFreshField? {C : Contract} {Γ : Ctx} (φ : Fml C Γ) :
    Option (NonliteralUIntFreshField φ) := do
  let v ← MemoryWitness.allocView φ
  let w ← nonliteralBound? v.x v.R v.body
  return w.cast v.eqn

/-- The field schema requires a direct literal RHS; this uint-linear RHS has
nonliteral source syntax at its root. -/
def nonliteralUIntFreshFieldReason : String :=
  "The fresh-field schema requires a direct literal RHS; this uint-linear RHS has a nonliteral root."

def _root_.Solidity.Fml.freshStructNonliteralUIntEquation {C : Contract} {Γ : Ctx}
    (φ : Fml C Γ) : Bool := (nonliteralUIntFreshField? φ).isSome

theorem nonliteralUIntFreshField_witness {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (h : φ.freshStructNonliteralUIntEquation = true) : Nonempty (NonliteralUIntFreshField φ) := by
  unfold Fml.freshStructNonliteralUIntEquation at h
  cases he : nonliteralUIntFreshField? φ with
  | none => rw [he] at h; cases h
  | some w => exact ⟨w⟩

private theorem nonliteralStructBody_complete {C : Contract} {Γ : Ctx}
    (x : Var) (s f : Name) (hf : lookupBy f (structDef s) = some (.prim .uint))
    (rhs : Tm C (.mem (.struct s) :: Γ) (.val .uint)) (hl : rhs.UIntLinear)
    (hn : (MemoryWitness.literalTerm rhs).isSome = false)
    (hm : (Ty.ref (.struct s)).mapFree = true) :
    (nonliteralStructBody? x s hm (.eq (MemoryWitness.fieldRead hf) rhs)).isSome = true := by
  have hg : rhs.uintLinearShape = true := Tm.uintLinearShape_complete hl
  simp only [nonliteralStructBody?, MemoryWitness.eqView, Option.bind_eq_bind,
    Option.bind_some, nonliteralEquation?, dif_pos hn, dif_pos hg]
  apply List.findSome?_isSome_iff.mpr
  refine ⟨(f, .prim .uint), Semantics.lookupBy_eq_some_mem hf, ?_⟩
  simp only [dif_pos hf, Tm.beqR_self, dif_pos True.intro, Option.isSome_some]

theorem nonliteralUIntFreshField_complete {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : NonliteralUIntFreshField φ) : φ.freshStructNonliteralUIntEquation = true := by
  rcases w with ⟨x, s, f, hf, rhs, hl, hn, hm, heq⟩
  subst φ
  have hc : (nonliteralStructBody? x s hm (.eq (MemoryWitness.fieldRead hf) rhs)).isSome = true :=
    nonliteralStructBody_complete x s f hf rhs hl hn hm
  simp only [Fml.freshStructNonliteralUIntEquation, nonliteralUIntFreshField?,
    MemoryWitness.allocView, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    nonliteralBound?, dif_pos hm]
  cases hs : nonliteralStructBody? x s hm (.eq (MemoryWitness.fieldRead hf) rhs) with
  | none => rw [hs] at hc; cases hc
  | some w => rfl

theorem nonliteralUIntFreshField_iff {C : Contract} {Γ : Ctx} {φ : Fml C Γ} :
    φ.freshStructNonliteralUIntEquation = true ↔ Nonempty (NonliteralUIntFreshField φ) :=
  ⟨nonliteralUIntFreshField_witness, fun ⟨w⟩ => nonliteralUIntFreshField_complete w⟩

instance nonliteralUIntFreshField_decidable {C : Contract} {Γ : Ctx} {φ : Fml C Γ} :
    Decidable (Nonempty (NonliteralUIntFreshField φ)) :=
  if h : φ.freshStructNonliteralUIntEquation = true then isTrue (nonliteralUIntFreshField_witness h)
  else isFalse (fun ⟨w⟩ => h (nonliteralUIntFreshField_complete w))

theorem NonliteralUIntFreshField.hashFree {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : NonliteralUIntFreshField φ) : φ.hasHash = false := by
  have he : φ.hasHash = (Fml.allocAll w.x (.struct w.s)
      (.eq (MemoryWitness.fieldRead w.field) w.rhs)).hasHash :=
    congrArg (fun ψ : Fml C Γ => ψ.hasHash) w.equation
  have hr : w.rhs.hasHash = false := uintLinear_hashFree w.linear
  exact he.trans (by
    change (false || w.rhs.hasHash) = false
    exact congrArg (fun b : Bool => false || b) hr)

private theorem fieldRead_not_uintLinear {C : Contract} {Γ : Ctx} {s f : Name}
    (hf : lookupBy f (structDef s) = some (.prim .uint)) :
    ¬ (MemoryWitness.fieldRead (C := C) (Γ := Γ) hf).UIntLinear := by
  intro h
  cases h

/-- The one-line reason is certified for the actual producer schema, without
claiming refusal by every other decision route. -/
theorem NonliteralUIntFreshField.schema_refuses {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : NonliteralUIntFreshField φ) :
    MemoryWitness.fieldEquation w.x w.s .uint (MemoryWitness.fieldRead w.field) w.rhs = none := by
  have hab : ¬ (MemoryWitness.fieldRead w.field).beqR w.rhs = true := by
    intro h
    have he : MemoryWitness.fieldRead w.field = w.rhs := Tm.eq_of_beqR h
    have hl : (MemoryWitness.fieldRead w.field).UIntLinear :=
      Eq.mpr (congrArg (fun t : Tm C (.mem (.struct w.s) :: Γ) (.val .uint) => t.UIntLinear) he) w.linear
    exact fieldRead_not_uintLinear w.field hl
  have hn : MemoryWitness.literalTerm w.rhs = none := by
    have h : (MemoryWitness.literalTerm w.rhs).isSome = false := w.nonliteral
    cases he : MemoryWitness.literalTerm w.rhs with
    | none => rfl
    | some value => rw [he] at h; cases h
  unfold MemoryWitness.fieldEquation
  simp only [dif_neg hab, Option.bind_eq_bind, hn, Option.bind_none]

end Solidity.Decide.ResidueReason
