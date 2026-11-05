import Solidity.Calculus.MemObserve
import Solidity.Calculus.MemStructCut
import Solidity.Calculus.HashPremise

/-! # A given-heap reflexive literal-read source reason
This exact intrinsic family queries no target, coverage or verdict function.
Its validity ranges over every heap and optional binder value, including unset.
The finite candidate checker alone cannot supply that global certificate.
-/
namespace Solidity.Decide.ResidueReason

/-- One box-bound dynamic uint array, with the same direct literal read twice. -/
structure GivenHeapLiteralReadReflexive {C : Contract} {Γ : Ctx} (φ : Fml C Γ) where
  name : Var
  key : PrimTy.uint.Denote
  equation : φ = .bind .box name (.mem (.array (.prim .uint)))
    (.eq (MxObs.read (q := .uint) key).tm (MxObs.read (q := .uint) key).tm)

def GivenHeapLiteralReadReflexive.cast {C : Contract} {Γ : Ctx} {φ ψ : Fml C Γ}
    (h : φ = ψ) (w : GivenHeapLiteralReadReflexive ψ) : GivenHeapLiteralReadReflexive φ :=
  h.symm ▸ w

private structure HeapBindView {C : Contract} {Γ : Ctx} (φ : Fml C Γ) where
  mode : Modality
  name : Var
  type : LTy
  body : Fml C (type :: Γ)
  equation : φ = .bind mode name type body

private def heapBindView {C : Contract} {Γ : Ctx} (φ : Fml C Γ) : Option (HeapBindView φ) :=
  @Fml.casesOn C (fun _ φ => Option (HeapBindView φ)) Γ φ
    (@fun _ => none) (@fun _ _ _ _ => none)
    (@fun _ _ => none) (@fun _ _ => none)
    (@fun _ _ _ => none) (@fun _ _ _ => none)
    (@fun _ _ _ _ _ => none) (@fun _ _ _ _ _ _ _ => none)
    (@fun _ _ => none) (@fun _ _ _ _ => none)
    (@fun _ m x t body => some ⟨m, x, t, body, rfl⟩)
    (@fun _ _ _ => none) (@fun _ _ _ _ => none) (@fun _ _ => none)

private def givenReadBody? {C : Contract} {Γ : Ctx} (name : Var)
    (body : Fml C (.mem (.array (.prim .uint)) :: Γ)) :
    Option (GivenHeapLiteralReadReflexive (.bind .box name (.mem (.array (.prim .uint))) body)) := do
  let e ← MemoryWitness.eqView body
  match e with
  | ⟨.uint, a, b, heq⟩ =>
    let key ← mxObsReadKey? a
    if ha : a.beqR (MxObs.read (q := .uint) key).tm = true then
      if hb : b.beqR (MxObs.read (q := .uint) key).tm = true then
        some ⟨name, key, congrArg (Fml.bind .box name (.mem (.array (.prim .uint))))
          (heq.trans (by rw [Tm.eq_of_beqR ha, Tm.eq_of_beqR hb]))⟩
      else none
    else none
  | _ => none

private def givenReadBound? {C : Contract} {Γ : Ctx} (name : Var) :
    (mode : Modality) → (type : LTy) → (body : Fml C (type :: Γ)) →
      Option (GivenHeapLiteralReadReflexive (.bind mode name type body))
  | .box, .mem (.array (.prim .uint)), body => givenReadBody? name body
  | _, _, _ => none

/-- Reuse the producer equation view and literal-key extractor, then check full terms. -/
def givenHeapLiteralRead? {C : Contract} {Γ : Ctx} (φ : Fml C Γ) :
    Option (GivenHeapLiteralReadReflexive φ) := do
  let v ← heapBindView φ
  let w ← givenReadBound? v.name v.mode v.type v.body
  return w.cast v.equation

/-- A candidate heap can certify a countermodel, not validity over every given heap. -/
def givenHeapLiteralReadReason : String :=
  "The given-heap fallback searches for a countermodel at one heap and cannot certify validity over every heap and binder value."

/-- Exact source classification, independent of all decision observations. -/
def _root_.Solidity.Fml.givenHeapLiteralReadReflexive {C : Contract} {Γ : Ctx}
    (φ : Fml C Γ) : Bool := (givenHeapLiteralRead? φ).isSome

/-- Recognition carries the complete typed source equality. -/
theorem givenHeapLiteralRead_witness {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (h : φ.givenHeapLiteralReadReflexive = true) : Nonempty (GivenHeapLiteralReadReflexive φ) := by
  unfold Fml.givenHeapLiteralReadReflexive at h
  cases he : givenHeapLiteralRead? φ with
  | none => rw [he] at h; cases h
  | some w => exact ⟨w⟩

private theorem literalRead_key {C : Contract} {Γ : Ctx} (key : PrimTy.uint.Denote) :
    mxObsReadKey? ((MxObs.read (q := .uint) key).tm :
      Tm C (.mem (.array (.prim .uint)) :: Γ) (.val .uint)) = some key := by
  rfl

/-- Every member of the exact typed family is recognized. -/
theorem givenHeapLiteralRead_complete {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : GivenHeapLiteralReadReflexive φ) : φ.givenHeapLiteralReadReflexive = true := by
  rcases w with ⟨name, key, heq⟩
  subst φ
  unfold Fml.givenHeapLiteralReadReflexive givenHeapLiteralRead?
  simp only [heapBindView, givenReadBound?, givenReadBody?, MemoryWitness.eqView,
    Option.bind_eq_bind, Option.bind_some, literalRead_key, Tm.beqR_self,
    dif_pos True.intro]
  rfl

/-- Exact source membership, not an unknown-result or noncoverage test. -/
theorem givenHeapLiteralRead_iff {C : Contract} {Γ : Ctx} {φ : Fml C Γ} :
    φ.givenHeapLiteralReadReflexive = true ↔ Nonempty (GivenHeapLiteralReadReflexive φ) :=
  ⟨givenHeapLiteralRead_witness, fun ⟨w⟩ => givenHeapLiteralRead_complete w⟩

instance givenHeapLiteralRead_decidable {C : Contract} {Γ : Ctx} {φ : Fml C Γ} :
    Decidable (Nonempty (GivenHeapLiteralReadReflexive φ)) :=
  if h : φ.givenHeapLiteralReadReflexive = true then
    isTrue (givenHeapLiteralRead_witness h)
  else isFalse (fun ⟨w⟩ => h (givenHeapLiteralRead_complete w))

/-- Fixed-array binders are outside this dynamic-array source class, for every body. -/
theorem givenHeapLiteralRead_fixed_refusal {C : Contract} {Γ : Ctx} (name : Var)
    (element : Ty) (n : Nat) (body : Fml C (.mem (.fixed element n) :: Γ)) :
    (Fml.bind .box name (.mem (.fixed element n)) body).givenHeapLiteralReadReflexive = false := by
  rfl

/-- This class deliberately specifies box-produced declarations, not diamond ones. -/
theorem givenHeapLiteralRead_diamond_refusal {C : Contract} {Γ : Ctx} (name : Var)
    (type : LTy) (body : Fml C (type :: Γ)) :
    (Fml.bind .diamond name type body).givenHeapLiteralReadReflexive = false := by
  rfl

/-- Fresh allocation is a different source family, regardless of its body. -/
theorem givenHeapLiteralRead_fresh_refusal {C : Contract} {Γ : Ctx} (name : Var)
    (type : RefTy) (body : Fml C (.mem type :: Γ)) :
    (Fml.allocAll name type body).givenHeapLiteralReadReflexive = false := by
  rfl

/-- Theory equality is reflexive even when the read is unset or out of bounds. -/
theorem GivenHeapLiteralReadReflexive.valid {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : GivenHeapLiteralReadReflexive φ) : ∀ σ : State C Γ, holds σ φ := by
  rcases w with ⟨name, key, heq⟩
  subst φ
  intro σ v
  rfl

/-- This precise source family contains no hashes. -/
theorem GivenHeapLiteralReadReflexive.hashFree {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : GivenHeapLiteralReadReflexive φ) : φ.hasHash = false :=
  (congrArg (fun ψ : Fml C Γ => ψ.hasHash) w.equation).trans rfl

/-- Preserve the existing hash-premised interpretation exactly. -/
theorem GivenHeapLiteralReadReflexive.validH {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : GivenHeapLiteralReadReflexive φ) : ∀ σ : State C Γ, Fml.holdsH σ φ :=
  fun σ => (Fml.holdsH_iff σ φ w.hashFree).mpr (w.valid σ)

/-- An independently usable global Answer, with no one-heap promotion. -/
def GivenHeapLiteralReadReflexive.answer {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : GivenHeapLiteralReadReflexive φ) : MemoryWitness.Answer φ := .proved w.valid

end Solidity.Decide.ResidueReason
