import Solidity.Calculus.DecisionGivenHeapComputedReason

/-! # Exact fixed-array given-heap read source class
The array length, identity, index and both complete operands stay intrinsic.
Membership is source syntax, independent of target, coverage and verdict.
-/
namespace Solidity.Decide.ResidueReason

def fixedHeapUIntRead {C : Contract} {Γ : Ctx} (n : Nat)
    (key : Tm C (.mem (.fixed (.prim .uint) n) :: Γ) (.val .uint)) :
    Tm C (.mem (.fixed (.prim .uint) n) :: Γ) (.val .uint) :=
  .app2 .read (.app0 .memory) (.app2 (.mat .fixed) (.pvI .here) key)

structure GivenHeapFixedReadReflexive {C : Contract} {Γ : Ctx} (φ : Fml C Γ) where
  name : Var
  length : Nat
  key : Tm C (.mem (.fixed (.prim .uint) length) :: Γ) (.val .uint)
  linear : key.UIntLinear
  equation : φ = .bind .box name (.mem (.fixed (.prim .uint) length))
    (.eq (fixedHeapUIntRead length key) (fixedHeapUIntRead length key))

def GivenHeapFixedReadReflexive.cast {C : Contract} {Γ : Ctx} {φ ψ : Fml C Γ}
    (h : φ = ψ) (w : GivenHeapFixedReadReflexive ψ) : GivenHeapFixedReadReflexive φ :=
  h.symm ▸ w

private structure FixedHeapBindView {C : Contract} {Γ : Ctx} (φ : Fml C Γ) where
  mode : Modality
  name : Var
  type : LTy
  body : Fml C (type :: Γ)
  equation : φ = .bind mode name type body

private def fixedHeapBindView {C : Contract} {Γ : Ctx} (φ : Fml C Γ) :
    Option (FixedHeapBindView φ) := by
  apply @Fml.casesOn C (fun Γ φ => Option (FixedHeapBindView φ)) Γ φ
  case bind => intro Γ mode name type body; exact some ⟨mode, name, type, body, rfl⟩
  all_goals intros; exact none

private def fixedHeapReadKey? {C : Contract} {Γ : Ctx} {n : Nat}
    (t : Tm C (.mem (.fixed (.prim .uint) n) :: Γ) (.val .uint)) :
    Option (Tm C (.mem (.fixed (.prim .uint) n) :: Γ) (.val .uint)) := do
  let ⟨addr, _⟩ ← mxReadView t
  let ⟨_, (_, _, key), _⟩ ← mxAddressView addr
  pure key

private def givenFixedReadBody? {C : Contract} {Γ : Ctx} (name : Var) (n : Nat)
    (body : Fml C (.mem (.fixed (.prim .uint) n) :: Γ)) :
    Option (GivenHeapFixedReadReflexive (.bind .box name (.mem (.fixed (.prim .uint) n)) body)) := do
  let e ← MemoryWitness.eqView body
  match e with
  | ⟨.uint, a, b, heq⟩ =>
    let key ← fixedHeapReadKey? a
    if hl : key.uintLinearShape = true then
      if ha : a.beqR (fixedHeapUIntRead n key) = true then
        if hb : b.beqR (fixedHeapUIntRead n key) = true then
          some ⟨name, n, key, Tm.uintLinearShape_sound key hl,
            congrArg (Fml.bind .box name (.mem (.fixed (.prim .uint) n)))
              (heq.trans (by rw [Tm.eq_of_beqR ha, Tm.eq_of_beqR hb]))⟩
        else none
      else none
    else none
  | _ => none

private def givenFixedReadBound? {C : Contract} {Γ : Ctx} (name : Var) :
    (mode : Modality) → (type : LTy) → (body : Fml C (type :: Γ)) →
      Option (GivenHeapFixedReadReflexive (.bind mode name type body))
  | .box, .mem (.fixed (.prim .uint) n), body => givenFixedReadBody? name n body
  | _, _, _ => none

def givenHeapFixedRead? {C : Contract} {Γ : Ctx} (φ : Fml C Γ) :
    Option (GivenHeapFixedReadReflexive φ) := do
  let v ← fixedHeapBindView φ
  let w ← givenFixedReadBound? v.name v.mode v.type v.body
  return w.cast v.equation

def givenHeapFixedReadReason : String :=
  "The given-heap dynamic-array schemas reject fixed-array binders, even for identical direct reads."

def _root_.Solidity.Fml.givenHeapFixedReadReflexive {C : Contract} {Γ : Ctx}
    (φ : Fml C Γ) : Bool := (givenHeapFixedRead? φ).isSome

theorem givenHeapFixedRead_witness {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (h : φ.givenHeapFixedReadReflexive = true) : Nonempty (GivenHeapFixedReadReflexive φ) := by
  unfold Fml.givenHeapFixedReadReflexive at h
  cases he : givenHeapFixedRead? φ with
  | none => rw [he] at h; cases h
  | some w => exact ⟨w⟩

private theorem fixedHeapReadKey_self {C : Contract} {Γ : Ctx} (n : Nat)
    (key : Tm C (.mem (.fixed (.prim .uint) n) :: Γ) (.val .uint)) :
    fixedHeapReadKey? (fixedHeapUIntRead n key) = some key := by rfl

theorem givenHeapFixedRead_complete {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : GivenHeapFixedReadReflexive φ) : φ.givenHeapFixedReadReflexive = true := by
  rcases w with ⟨name, n, key, linear, heq⟩
  subst φ
  have hs : key.uintLinearShape = true := Tm.uintLinearShape_complete linear
  unfold Fml.givenHeapFixedReadReflexive givenHeapFixedRead?
  simp only [fixedHeapBindView, givenFixedReadBound?, givenFixedReadBody?,
    MemoryWitness.eqView, Option.bind_eq_bind, Option.bind_some,
    fixedHeapReadKey_self, dif_pos hs, Tm.beqR_self, dif_pos True.intro]
  rfl

theorem givenHeapFixedRead_iff {C : Contract} {Γ : Ctx} {φ : Fml C Γ} :
    φ.givenHeapFixedReadReflexive = true ↔ Nonempty (GivenHeapFixedReadReflexive φ) :=
  ⟨givenHeapFixedRead_witness, fun ⟨w⟩ => givenHeapFixedRead_complete w⟩

instance givenHeapFixedRead_decidable {C : Contract} {Γ : Ctx} {φ : Fml C Γ} :
    Decidable (Nonempty (GivenHeapFixedReadReflexive φ)) :=
  if h : φ.givenHeapFixedReadReflexive = true then isTrue (givenHeapFixedRead_witness h)
  else isFalse (fun ⟨w⟩ => h (givenHeapFixedRead_complete w))

theorem GivenHeapFixedReadReflexive.valid {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : GivenHeapFixedReadReflexive φ) : ∀ σ : State C Γ, holds σ φ := by
  rcases w with ⟨name, n, key, linear, heq⟩
  subst φ
  intro σ v
  rfl

theorem GivenHeapFixedReadReflexive.hashFree {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : GivenHeapFixedReadReflexive φ) : φ.hasHash = false := by
  rcases w with ⟨name, n, key, linear, heq⟩
  subst φ
  have hk : key.hasHash = false := uintLinear_hashFree linear
  change (key.hasHash || key.hasHash) = false
  rw [hk]
  rfl

theorem GivenHeapFixedReadReflexive.validH {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : GivenHeapFixedReadReflexive φ) : ∀ σ : State C Γ, Fml.holdsH σ φ :=
  fun σ => (Fml.holdsH_iff σ φ w.hashFree).mpr (w.valid σ)

end Solidity.Decide.ResidueReason
