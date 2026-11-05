import Solidity.Calculus.DecisionBoundedUInt
import Solidity.Calculus.DecisionLeafEquality

/-! # Exact literal instances of bounded universal source formulas
A genuine all-state certificate using the existing optional substitution
semantics. No storage realization, coverage/verdict query or future premise.
-/
namespace Solidity.Decide

/-- One in-range literal instance follows from the real guarded universal.
The quantifier-free body may contain arbitrary typed partial observations. -/
theorem boundedUInt_literal_instance_valid {C : Contract}
    (k : Nat) (bound value : PrimTy.uint.Denote) (body : LFml C)
    (hq : body.qfB = true) (hv : value.1.toNat < bound.1.toNat) :
    LFml.Valid (.imp (.all k .uint (.imp (uintBelow k bound) body))
      (body.subst1 k (.app0 (.lit value)))) := by
  intro g ν hall
  have hg : (uintBelow (C := C) k bound).holds g (ν.set .uint k value) :=
    (uintBelow_set_holds g ν k bound value).mpr hv
  have hb : body.holds g (ν.set .uint k value) := hall value hg
  exact (LFml.holds_subst1 g ν k (.app0 (.lit value))
    (v := value) (by rfl) body hq).mpr hb

/-- Exact syntactic instance family at a supplied literal. The literal is a
parameter, not a verdict or an assumed source/compiler certificate. -/
structure BoundedUIntLiteralInstance {C : Contract} (B : LFml C)
    (value : PrimTy.uint.Denote) where
  index : Nat
  bound : PrimTy.uint.Denote
  body : LFml C
  qf : body.qfB = true
  inside : value.1.toNat < bound.1.toNat
  equation : B = .imp (.all index .uint (.imp (uintBelow index bound) body))
    (body.subst1 index (.app0 (.lit value)))

/-- The entire semantic statement follows from the retained actual syntax. -/
theorem BoundedUIntLiteralInstance.valid {C : Contract} {B : LFml C}
    {value : PrimTy.uint.Denote} (w : BoundedUIntLiteralInstance B value) : B.Valid := by
  rw [w.equation]
  exact boundedUInt_literal_instance_valid w.index w.bound value w.body w.qf w.inside

/-- Full syntax comparisons retain an intrinsic witness; no prepared budget or
classification is consulted. This recognizer is parameterized by the literal. -/
def boundedUIntLiteralInstance? {C : Contract} (B : LFml C)
    (value : PrimTy.uint.Denote) : Option (BoundedUIntLiteralInstance B value) :=
  match B with
  | .imp (.all k .uint (.imp G body)) rhs =>
    if hq : body.qfB = true then
      match boundedUIntGuard? k G with
      | some ⟨bound, hG⟩ =>
        if hv : value.1.toNat < bound.1.toNat then
          if he : rhs.same (body.subst1 k (.app0 (.lit value))) = true then
            some ⟨k, bound, body, hq, hv, by rw [hG, LFml.eq_of_same _ _ he]⟩
          else none
        else none
      | none => none
    else none
  | _ => none

/-- Decidable actual syntax at the supplied literal, independent of coverage. -/
def LFml.boundedUIntLiteralInstance {C : Contract} (B : LFml C)
    (value : PrimTy.uint.Denote) : Bool := (boundedUIntLiteralInstance? B value).isSome

theorem boundedUIntLiteralInstance_witness {C : Contract} {B : LFml C}
    {value : PrimTy.uint.Denote} (h : B.boundedUIntLiteralInstance value = true) :
    Nonempty (BoundedUIntLiteralInstance B value) := by
  unfold LFml.boundedUIntLiteralInstance at h
  cases he : boundedUIntLiteralInstance? B value with
  | none => rw [he] at h; cases h
  | some w => exact ⟨w⟩

/-- Every exact member of the stated literal-parameterized family is recognized. -/
theorem boundedUIntLiteralInstance_complete {C : Contract} {B : LFml C}
    {value : PrimTy.uint.Denote} (w : BoundedUIntLiteralInstance B value) :
    B.boundedUIntLiteralInstance value = true := by
  rcases w with ⟨k, bound, body, hq, hv, heq⟩
  subst B
  unfold LFml.boundedUIntLiteralInstance
  simp only [boundedUIntLiteralInstance?, boundedUIntGuard?, uintBelow,
    uintLtBoundCandidate, uintLtBinCandidate, LTm.litV?, leafFormula_same_self,
    dif_pos hq, dif_pos hv, dif_pos True.intro, Option.isSome_some]

theorem boundedUIntLiteralInstance_iff {C : Contract} {B : LFml C}
    {value : PrimTy.uint.Denote} : B.boundedUIntLiteralInstance value = true ↔
      Nonempty (BoundedUIntLiteralInstance B value) :=
  ⟨boundedUIntLiteralInstance_witness, fun ⟨w⟩ => boundedUIntLiteralInstance_complete w⟩

instance boundedUIntLiteralInstance_decidable {C : Contract} {B : LFml C}
    {value : PrimTy.uint.Denote} : Decidable (Nonempty (BoundedUIntLiteralInstance B value)) :=
  if h : B.boundedUIntLiteralInstance value = true then
    isTrue (boundedUIntLiteralInstance_witness h)
  else isFalse (fun ⟨w⟩ => h (boundedUIntLiteralInstance_complete w))

end Solidity.Decide
