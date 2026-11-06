import Solidity.Calculus.DecisionResidueReasons

/-! # Mapping-bearing reversed-field source reason
These typed recognizers describe actual source families without consulting a
coverage or verdict function. They are components for a later exhaustive
Residue/bridge proof; no global exhaustiveness or universal unknown is asserted.
-/
namespace Solidity.Decide.ResidueReason
open Semantics (structDef lookupBy)

/-- A direct literal on the left of a primitive field read under a single
mapping-bearing fresh-struct binder. The witness retains the complete source equation. -/
structure MappingReversedFreshField {C : Contract} {Γ : Ctx} (φ : Fml C Γ) where
  x : Var
  s : Name
  f : Name
  p : PrimTy
  value : p.Denote
  field : lookupBy f (structDef s) = some (.prim p)
  mapBearing : (Ty.ref (.struct s)).mapFree = false
  equation : φ = .allocAll x (.struct s)
    (.eq (.app0 (.lit value)) (MemoryWitness.fieldRead field))

def MappingReversedFreshField.cast {C : Contract} {Γ : Ctx} {φ ψ : Fml C Γ}
    (h : φ = ψ) (w : MappingReversedFreshField ψ) : MappingReversedFreshField φ := h.symm ▸ w

private def mappingReversedStructBody? {C : Contract} {Γ : Ctx} (x : Var) (s : Name)
    (hm : (Ty.ref (.struct s)).mapFree = false) (body : Fml C (.mem (.struct s) :: Γ)) :
    Option (MappingReversedFreshField (.allocAll x (.struct s) body)) := do
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

private def mappingReversedBound? {C : Contract} {Γ : Ctx} (x : Var) :
    (R : RefTy) → (body : Fml C (.mem R :: Γ)) →
      Option (MappingReversedFreshField (.allocAll x R body))
  | .struct s, body =>
    if hm : (Ty.ref (.struct s)).mapFree = false then mappingReversedStructBody? x s hm body
    else none
  | _, _ => none

/-- Recognition returns a complete intrinsically typed source witness. -/
def mappingReversedFreshField? {C : Contract} {Γ : Ctx} (φ : Fml C Γ) :
    Option (MappingReversedFreshField φ) := do
  let v ← MemoryWitness.allocView φ
  let w ← mappingReversedBound? v.x v.R v.body
  return w.cast v.eqn

/-- This structural boundary does not assert refusal by every decision route. -/
def mappingReversedFreshFieldReason : String :=
  "The existing fresh-struct realization requires a map-free struct; this source contains mapping structure."

/-- Decidable source classification, independent of target, coverage and verdict. -/
def _root_.Solidity.Fml.freshStructMappingReversedPrimitiveEquation {C : Contract} {Γ : Ctx}
    (φ : Fml C Γ) : Bool := (mappingReversedFreshField? φ).isSome

/-- Every recognized case carries the actual source syntax, not a verdict tag. -/
theorem mappingReversedFreshField_witness {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (h : φ.freshStructMappingReversedPrimitiveEquation = true) : Nonempty (MappingReversedFreshField φ) := by
  unfold Fml.freshStructMappingReversedPrimitiveEquation at h
  cases he : mappingReversedFreshField? φ with
  | none => rw [he] at h; cases h
  | some w => exact ⟨w⟩

private theorem mappingReversedStructBody_complete {C : Contract} {Γ : Ctx}
    (x : Var) (s f : Name) (p : PrimTy) (value : p.Denote)
    (hf : lookupBy f (structDef s) = some (.prim p))
    (hm : (Ty.ref (.struct s)).mapFree = false) :
    (mappingReversedStructBody? (C := C) (Γ := Γ) x s hm
      (.eq (.app0 (.lit value)) (MemoryWitness.fieldRead hf))).isSome = true := by
  unfold mappingReversedStructBody?
  simp only [MemoryWitness.eqView, MemoryWitness.literalTerm, MemoryWitness.literalOp,
    Option.bind_eq_bind, Option.bind_some, Tm.beqR_self]
  apply List.findSome?_isSome_iff.mpr
  refine ⟨(f, .prim p), Semantics.lookupBy_eq_some_mem hf, ?_⟩
  simp only [dif_pos hf, Tm.beqR_self, dif_pos True.intro, Option.isSome_some]

/-- Every member of the stated exact typed source family is recognized. -/
theorem mappingReversedFreshField_complete {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : MappingReversedFreshField φ) : φ.freshStructMappingReversedPrimitiveEquation = true := by
  rcases w with ⟨x, s, f, p, value, hf, hm, heq⟩
  subst φ
  have hc : (mappingReversedStructBody? (C := C) (Γ := Γ) x s hm
      (.eq (.app0 (.lit value)) (MemoryWitness.fieldRead hf))).isSome = true :=
    mappingReversedStructBody_complete (C := C) (Γ := Γ) x s f p value hf hm
  simp only [Fml.freshStructMappingReversedPrimitiveEquation, mappingReversedFreshField?,
    MemoryWitness.allocView, Option.bind_eq_bind, Option.bind_some, Option.pure_def, mappingReversedBound?, dif_pos hm]
  cases hs : mappingReversedStructBody? (C := C) (Γ := Γ) x s hm
      (.eq (.app0 (.lit value)) (MemoryWitness.fieldRead hf)) with
  | none => rw [hs] at hc; cases hc
  | some w => rfl

/-- Exact classification of the intrinsic family, not of coverage or unknown. -/
theorem mappingReversedFreshField_iff {C : Contract} {Γ : Ctx} {φ : Fml C Γ} :
    φ.freshStructMappingReversedPrimitiveEquation = true ↔ Nonempty (MappingReversedFreshField φ) :=
  ⟨mappingReversedFreshField_witness, fun ⟨w⟩ => mappingReversedFreshField_complete w⟩

instance mappingReversedFreshField_decidable {C : Contract} {Γ : Ctx} {φ : Fml C Γ} :
    Decidable (Nonempty (MappingReversedFreshField φ)) :=
  if h : φ.freshStructMappingReversedPrimitiveEquation = true then
    isTrue (mappingReversedFreshField_witness h)
  else isFalse (fun ⟨w⟩ => h (mappingReversedFreshField_complete w))

/-- Exact source syntax is hash-free, irrespective of mapping structure. -/
theorem MappingReversedFreshField.hashFree {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : MappingReversedFreshField φ) : φ.hasHash = false :=
  (congrArg (fun ψ : Fml C Γ => ψ.hasHash) w.equation).trans rfl

/-- The existing map-free schema refuses this binder, independently of its body.
This does not claim that every global decision route refuses. -/
theorem MappingReversedFreshField.schema_refuses {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : MappingReversedFreshField φ) (body : Fml C (.mem (.struct w.s) :: Γ)) :
    MemoryWitness.boundAnswer w.x (.struct w.s) body = none := by
  simp only [MemoryWitness.boundAnswer, w.mapBearing, Bool.false_eq_true, if_false]

end Solidity.Decide.ResidueReason
