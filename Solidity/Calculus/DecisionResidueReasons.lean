import Solidity.Calculus.MemStructCut
import Solidity.Calculus.HashPremise

/-! # Independently decidable source reasons for the remaining gap census
These typed recognizers describe actual source families without consulting a
coverage or verdict function. They are components for a later exhaustive
Residue/bridge proof; no global exhaustiveness or universal unknown is asserted.
-/
namespace Solidity.Decide.ResidueReason
open Semantics (structDef lookupBy)

/-- A direct literal on the left of a primitive field read under a single
map-free fresh-struct binder. The witness retains the complete source equation. -/
structure ReversedFreshField {C : Contract} {Γ : Ctx} (φ : Fml C Γ) where
  x : Var
  s : Name
  f : Name
  p : PrimTy
  value : p.Denote
  field : lookupBy f (structDef s) = some (.prim p)
  mapFree : (Ty.ref (.struct s)).mapFree = true
  equation : φ = .allocAll x (.struct s)
    (.eq (.app0 (.lit value)) (MemoryWitness.fieldRead field))

def ReversedFreshField.cast {C : Contract} {Γ : Ctx} {φ ψ : Fml C Γ}
    (h : φ = ψ) (w : ReversedFreshField ψ) : ReversedFreshField φ := h.symm ▸ w

private def reversedStructBody? {C : Contract} {Γ : Ctx} (x : Var) (s : Name)
    (hm : (Ty.ref (.struct s)).mapFree = true) (body : Fml C (.mem (.struct s) :: Γ)) :
    Option (ReversedFreshField (.allocAll x (.struct s) body)) := do
  let e ← MemoryWitness.eqView body
  let ⟨q, value⟩ ← MemoryWitness.literalTerm e.a
  if hqp : q = e.p then
    let value : e.p.Denote := hqp ▸ value
    if ha : e.a.beqR (.app0 (.lit value)) = true then
      (structDef s).findSome? fun fT =>
        if hf : lookupBy fT.1 (structDef s) = some (.prim e.p) then
          if hb : e.b.beqR (MemoryWitness.fieldRead hf) = true then
            some ⟨x, s, fT.1, e.p, value, hf, hm, by
              exact congrArg (Fml.allocAll x (.struct s))
                (e.eqn.trans (by rw [Tm.eq_of_beqR ha, Tm.eq_of_beqR hb]))⟩
          else none
        else none
    else none
  else none

private def reversedBound? {C : Contract} {Γ : Ctx} (x : Var) :
    (R : RefTy) → (body : Fml C (.mem R :: Γ)) →
      Option (ReversedFreshField (.allocAll x R body))
  | .struct s, body =>
    if hm : (Ty.ref (.struct s)).mapFree = true then reversedStructBody? x s hm body
    else none
  | _, _ => none

/-- Recognition returns a complete intrinsically typed source witness. -/
def reversedFreshField? {C : Contract} {Γ : Ctx} (φ : Fml C Γ) :
    Option (ReversedFreshField φ) := do
  let v ← MemoryWitness.allocView φ
  let w ← reversedBound? v.x v.R v.body
  return w.cast v.eqn

/-- The fresh-struct schema recognizes field-on-left/direct-literal-on-right
 equations; this source family reverses those operands. -/
def reversedFreshFieldReason : String :=
  "The fresh-struct schema requires the field on the left and a direct literal on the right."

/-- Decidable source classification, independent of target, coverage and verdict. -/
def _root_.Solidity.Fml.freshStructReversedPrimitiveEquation {C : Contract} {Γ : Ctx}
    (φ : Fml C Γ) : Bool := (reversedFreshField? φ).isSome

/-- Every recognized case carries the actual source syntax, not a verdict tag. -/
theorem reversedFreshField_witness {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (h : φ.freshStructReversedPrimitiveEquation = true) : Nonempty (ReversedFreshField φ) := by
  unfold Fml.freshStructReversedPrimitiveEquation at h
  cases he : reversedFreshField? φ with
  | none => rw [he] at h; cases h
  | some w => exact ⟨w⟩

private theorem reversedStructBody_complete {C : Contract} {Γ : Ctx}
    (x : Var) (s f : Name) (p : PrimTy) (value : p.Denote)
    (hf : lookupBy f (structDef s) = some (.prim p))
    (hm : (Ty.ref (.struct s)).mapFree = true) :
    (reversedStructBody? (C := C) (Γ := Γ) x s hm
      (.eq (.app0 (.lit value)) (MemoryWitness.fieldRead hf))).isSome = true := by
  unfold reversedStructBody?
  simp only [MemoryWitness.eqView, MemoryWitness.literalTerm, MemoryWitness.literalOp,
    Option.bind_eq_bind, Option.bind_some, Tm.beqR_self]
  apply List.findSome?_isSome_iff.mpr
  refine ⟨(f, .prim p), Semantics.lookupBy_eq_some_mem hf, ?_⟩
  simp only [dif_pos hf, Tm.beqR_self, dif_pos True.intro, Option.isSome_some]

/-- Every member of the stated exact typed source family is recognized. -/
theorem reversedFreshField_complete {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : ReversedFreshField φ) : φ.freshStructReversedPrimitiveEquation = true := by
  rcases w with ⟨x, s, f, p, value, hf, hm, heq⟩
  subst φ
  have hc : (reversedStructBody? (C := C) (Γ := Γ) x s hm
      (.eq (.app0 (.lit value)) (MemoryWitness.fieldRead hf))).isSome = true :=
    reversedStructBody_complete (C := C) (Γ := Γ) x s f p value hf hm
  simp only [Fml.freshStructReversedPrimitiveEquation, reversedFreshField?,
    MemoryWitness.allocView, Option.bind_eq_bind, Option.bind_some, Option.pure_def, reversedBound?, dif_pos hm]
  cases hs : reversedStructBody? (C := C) (Γ := Γ) x s hm
      (.eq (.app0 (.lit value)) (MemoryWitness.fieldRead hf)) with
  | none => rw [hs] at hc; cases hc
  | some w => rfl

/-- Exact classification of the intrinsic family, not of coverage or unknown. -/
theorem reversedFreshField_iff {C : Contract} {Γ : Ctx} {φ : Fml C Γ} :
    φ.freshStructReversedPrimitiveEquation = true ↔ Nonempty (ReversedFreshField φ) :=
  ⟨reversedFreshField_witness, fun ⟨w⟩ => reversedFreshField_complete w⟩

instance reversedFreshField_decidable {C : Contract} {Γ : Ctx} {φ : Fml C Γ} :
    Decidable (Nonempty (ReversedFreshField φ)) :=
  if h : φ.freshStructReversedPrimitiveEquation = true then
    isTrue (reversedFreshField_witness h)
  else isFalse (fun ⟨w⟩ => h (reversedFreshField_complete w))

/-- The producer's existing finite child realization applies to this exact
map-free source witness. No new heap or freshness assumption is introduced. -/
theorem ReversedFreshField.fieldsMapFree {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : ReversedFreshField φ) : ∀ fT ∈ structDef w.s, fT.2.mapFree = true :=
  mapFree_structDef w.s (by simpa only [Ty.mapFree, decide_eq_true_eq] using w.mapFree)

/-- Reuse the producer's child heap before the parent allocation. -/
def ReversedFreshField.counterState {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : ReversedFreshField φ) (σ : State C Γ) : State C Γ :=
  (σ.adopt (MemoryWitness.children σ.heap w.s w.fieldsMapFree)).1

/-- Equation symmetry transports the existing field countermodel at the same
constructed state; it does not replace it by the initial heap. -/
theorem ReversedFreshField.counterState_refutes {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : ReversedFreshField φ) (σ : State C Γ) : ¬ holds (w.counterState σ) φ := by
  intro h
  have hb : holds (w.counterState σ) (.allocAll w.x (.struct w.s)
      (.eq (.app0 (.lit w.value)) (MemoryWitness.fieldRead w.field))) :=
    Eq.mp (congrArg (fun ψ : Fml C Γ => holds (w.counterState σ) ψ) w.equation) h
  apply MemoryWitness.fieldEq_refutes σ
    (MemoryWitness.children σ.heap w.s w.fieldsMapFree) w.field w.x w.value
  intro o
  exact (hb o).symm

/-- An independently usable constructive answer for this source family, consumed
by the certified reversed-field fallback when the original producer misses. -/
def ReversedFreshField.answer {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : ReversedFreshField φ) : MemoryWitness.Answer φ :=
  .refuted w.counterState w.counterState_refutes

/-- This precise source family is structurally hash-free; no hash premise is
removed or strengthened when exposing its refutation. -/
theorem ReversedFreshField.hashFree {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : ReversedFreshField φ) : φ.hasHash = false :=
  (congrArg (fun ψ : Fml C Γ => ψ.hasHash) w.equation).trans rfl

theorem ReversedFreshField.counterState_refutesH {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : ReversedFreshField φ) (σ : State C Γ) : ¬ Fml.holdsH (w.counterState σ) φ :=
  fun h => w.counterState_refutes σ ((Fml.holdsH_iff (w.counterState σ) φ w.hashFree).mp h)

end Solidity.Decide.ResidueReason
