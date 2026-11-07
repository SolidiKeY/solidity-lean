import Solidity.Calculus.DecisionGivenHeapReason
import Solidity.Calculus.DecisionUIntRecognizer

/-! # Nonliteral linear given-heap read source reason
This exact intrinsic family is classified independently of coverage and verdicts.
Theory equality compares identical denotations even when a read/index is undefined.
No program-equality observation or global decision route is changed.
-/
namespace Solidity.Decide.ResidueReason

/-- A direct read of the box-bound dynamic array at the original typed index. -/
def computedHeapUIntRead {C : Contract} {Γ : Ctx}
    (key : Tm C (.mem (.array (.prim .uint)) :: Γ) (.val .uint)) :
    Tm C (.mem (.array (.prim .uint)) :: Γ) (.val .uint) :=
  .app2 .read (.app0 .memory) (.app2 (.mat .dyn) (.pvI .here) key)

/-- The original source equation, with a genuine linear, nonliteral index. -/
structure GivenHeapLinearReadReflexive {C : Contract} {Γ : Ctx} (φ : Fml C Γ) where
  name : Var
  key : Tm C (.mem (.array (.prim .uint)) :: Γ) (.val .uint)
  linear : key.UIntLinear
  nonliteral : (MemoryWitness.literalTerm key).isSome = false
  equation : φ = .bind .box name (.mem (.array (.prim .uint)))
    (.eq (computedHeapUIntRead key) (computedHeapUIntRead key))

def GivenHeapLinearReadReflexive.cast {C : Contract} {Γ : Ctx} {φ ψ : Fml C Γ}
    (h : φ = ψ) (w : GivenHeapLinearReadReflexive ψ) : GivenHeapLinearReadReflexive φ :=
  h.symm ▸ w

private structure ComputedHeapBindView {C : Contract} {Γ : Ctx} (φ : Fml C Γ) where
  mode : Modality
  name : Var
  type : LTy
  body : Fml C (type :: Γ)
  equation : φ = .bind mode name type body

private def computedHeapBindView {C : Contract} {Γ : Ctx} (φ : Fml C Γ) :
    Option (ComputedHeapBindView φ) := by
  apply @Fml.casesOn C (fun Γ φ => Option (ComputedHeapBindView φ)) Γ φ
  case bind => intro Γ mode name type body; exact some ⟨mode, name, type, body, rfl⟩
  all_goals intros; exact none

/-- Existing intrinsic address views retain the actual index, without decoding it anew. -/
private def computedHeapReadKey? {C : Contract} {Γ : Ctx}
    (t : Tm C (.mem (.array (.prim .uint)) :: Γ) (.val .uint)) :
    Option (Tm C (.mem (.array (.prim .uint)) :: Γ) (.val .uint)) := do
  let ⟨addr, _⟩ ← mxReadView t
  let ⟨_, (_, _, key), _⟩ ← mxAddressView addr
  pure key

private def givenLinearReadBody? {C : Contract} {Γ : Ctx} (name : Var)
    (body : Fml C (.mem (.array (.prim .uint)) :: Γ)) :
    Option (GivenHeapLinearReadReflexive
      (.bind .box name (.mem (.array (.prim .uint))) body)) := do
  let e ← MemoryWitness.eqView body
  match e with
  | ⟨.uint, a, b, heq⟩ =>
    let key ← computedHeapReadKey? a
    if hl : key.uintLinearShape = true then
      if hn : (MemoryWitness.literalTerm key).isSome = false then
        if ha : a.beqR (computedHeapUIntRead key) = true then
          if hb : b.beqR (computedHeapUIntRead key) = true then
            some ⟨name, key, Tm.uintLinearShape_sound key hl, hn,
              congrArg (Fml.bind .box name (.mem (.array (.prim .uint))))
                (heq.trans (by rw [Tm.eq_of_beqR ha, Tm.eq_of_beqR hb]))⟩
          else none
        else none
      else none
    else none
  | _ => none

private def givenLinearReadBound? {C : Contract} {Γ : Ctx} (name : Var) :
    (mode : Modality) → (type : LTy) → (body : Fml C (type :: Γ)) →
      Option (GivenHeapLinearReadReflexive (.bind mode name type body))
  | .box, .mem (.array (.prim .uint)), body => givenLinearReadBody? name body
  | _, _, _ => none

/-- Actual typed source recognition; no target, coverage or unknown test occurs. -/
def givenHeapLinearRead? {C : Contract} {Γ : Ctx} (φ : Fml C Γ) :
    Option (GivenHeapLinearReadReflexive φ) := do
  let v ← computedHeapBindView φ
  let w ← givenLinearReadBound? v.name v.mode v.type v.body
  return w.cast v.equation

def givenHeapLinearReadReason : String :=
  "The given-heap positive schema accepts literal indices; this reflexive read uses a nonliteral linear uint index."

def _root_.Solidity.Fml.givenHeapLinearReadReflexive {C : Contract} {Γ : Ctx}
    (φ : Fml C Γ) : Bool := (givenHeapLinearRead? φ).isSome

theorem givenHeapLinearRead_witness {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (h : φ.givenHeapLinearReadReflexive = true) : Nonempty (GivenHeapLinearReadReflexive φ) := by
  unfold Fml.givenHeapLinearReadReflexive at h
  cases he : givenHeapLinearRead? φ with
  | none => rw [he] at h; cases h
  | some w => exact ⟨w⟩

/-- Global theory validity does not assume that this computed index is defined. -/
theorem GivenHeapLinearReadReflexive.valid {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : GivenHeapLinearReadReflexive φ) : ∀ σ : State C Γ, holds σ φ := by
  rcases w with ⟨name, key, linear, nonliteral, heq⟩
  subst φ
  intro σ v
  rfl

theorem GivenHeapLinearReadReflexive.hashFree {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : GivenHeapLinearReadReflexive φ) : φ.hasHash = false := by
  rcases w with ⟨name, key, linear, nonliteral, heq⟩
  subst φ
  have hk : key.hasHash = false := uintLinear_hashFree linear
  change (key.hasHash || key.hasHash) = false
  rw [hk]
  rfl

theorem GivenHeapLinearReadReflexive.validH {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : GivenHeapLinearReadReflexive φ) : ∀ σ : State C Γ, Fml.holdsH σ φ :=
  fun σ => (Fml.holdsH_iff σ φ w.hashFree).mpr (w.valid σ)

private theorem computedHeapReadKey_self {C : Contract} {Γ : Ctx}
    (key : Tm C (.mem (.array (.prim .uint)) :: Γ) (.val .uint)) :
    computedHeapReadKey? (computedHeapUIntRead key) = some key := by
  rfl

/-- Every member of this independently stated syntax family is found. -/
theorem givenHeapLinearRead_complete {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : GivenHeapLinearReadReflexive φ) : φ.givenHeapLinearReadReflexive = true := by
  rcases w with ⟨name, key, linear, nonliteral, heq⟩
  subst φ
  have hs : key.uintLinearShape = true := Tm.uintLinearShape_complete linear
  unfold Fml.givenHeapLinearReadReflexive givenHeapLinearRead?
  simp only [computedHeapBindView, givenLinearReadBound?, givenLinearReadBody?,
    MemoryWitness.eqView, Option.bind_eq_bind, Option.bind_some,
    computedHeapReadKey_self, dif_pos hs, dif_pos nonliteral, Tm.beqR_self,
    dif_pos True.intro]
  rfl

/-- Exact constructive membership, not an unknown or noncoverage predicate. -/
theorem givenHeapLinearRead_iff {C : Contract} {Γ : Ctx} {φ : Fml C Γ} :
    φ.givenHeapLinearReadReflexive = true ↔ Nonempty (GivenHeapLinearReadReflexive φ) :=
  ⟨givenHeapLinearRead_witness, fun ⟨w⟩ => givenHeapLinearRead_complete w⟩

instance givenHeapLinearRead_decidable {C : Contract} {Γ : Ctx} {φ : Fml C Γ} :
    Decidable (Nonempty (GivenHeapLinearReadReflexive φ)) :=
  if h : φ.givenHeapLinearReadReflexive = true then
    isTrue (givenHeapLinearRead_witness h)
  else isFalse (fun ⟨w⟩ => h (givenHeapLinearRead_complete w))

/-- The old literal-only classifier is preserved as a disjoint source family. -/
theorem GivenHeapLinearReadReflexive.not_literal {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : GivenHeapLinearReadReflexive φ) : φ.givenHeapLiteralReadReflexive = false := by
  rcases w with ⟨name, key, linear, nonliteral, heq⟩
  subst φ
  cases linear with
  | «local» i => rfl
  | lit value => change true = false at nonliteral; cases nonliteral
  | add ha hb => rfl
  | sub ha hb => rfl
  | mulL value hb => rfl
  | mulR value ha => rfl

theorem GivenHeapLinearReadReflexive.disjoint_literal {C : Contract} {Γ : Ctx}
    {φ : Fml C Γ} (w : GivenHeapLinearReadReflexive φ) :
    ¬ Nonempty (GivenHeapLiteralReadReflexive φ) := by
  intro h
  obtain ⟨old⟩ := h
  have hl : φ.givenHeapLiteralReadReflexive = true := givenHeapLiteralRead_complete old
  rw [w.not_literal] at hl
  cases hl

theorem givenHeapLinearRead_literal_refusal {C : Contract} {Γ : Ctx}
    (name : Var) (value : PrimTy.uint.Denote) :
    (Fml.bind .box name (.mem (.array (.prim .uint)))
      (.eq (computedHeapUIntRead (.app0 (.lit value)))
        (computedHeapUIntRead (.app0 (.lit value)))) : Fml C Γ).givenHeapLinearReadReflexive = false := by
  rfl

theorem givenHeapLinearRead_fixed_refusal {C : Contract} {Γ : Ctx} (name : Var)
    (element : Ty) (n : Nat) (body : Fml C (.mem (.fixed element n) :: Γ)) :
    (Fml.bind .box name (.mem (.fixed element n)) body).givenHeapLinearReadReflexive = false := by
  rfl

theorem givenHeapLinearRead_diamond_refusal {C : Contract} {Γ : Ctx} (name : Var)
    (type : LTy) (body : Fml C (type :: Γ)) :
    (Fml.bind .diamond name type body).givenHeapLinearReadReflexive = false := by
  rfl

theorem givenHeapLinearRead_fresh_refusal {C : Contract} {Γ : Ctx} (name : Var)
    (type : RefTy) (body : Fml C (.mem type :: Γ)) :
    (Fml.allocAll name type body).givenHeapLinearReadReflexive = false := by
  rfl

end Solidity.Decide.ResidueReason
