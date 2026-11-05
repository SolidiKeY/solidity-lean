import Solidity.Calculus.DecisionBoundedInstanceSource

/-! # Formula-derived bounded literal-instance search
Candidates come from the actual literal bound after the unchanged source-node
estimate check. Each returned result retains its genuine syntax/validity proof.
-/
namespace Solidity.Decide

structure BoundedLiteralHit {C : Contract} (B : LFml C) where
  value : PrimTy.uint.Denote
  witness : BoundedUIntLiteralInstance B value

private def boundedLiteralSearchAt {C : Contract} (B : LFml C)
    (bound : PrimTy.uint.Denote) : Option (BoundedLiteralHit B) :=
  (uintSamples (C := C) bound).findSome? fun t => do
    let value ← t.litV?
    let w ← boundedUIntLiteralInstance? B value
    return ⟨value, w⟩

/-- Reject an over-budget estimate before allocating the finite sample list. -/
def boundedUIntLiteralSearch? {C : Contract} (B : LFml C) : Option (BoundedLiteralHit B) :=
  match B with
  | .imp (.all k .uint (.imp G body)) rhs => do
    let ⟨bound, _hG⟩ ← boundedUIntGuard? k G
    if boundedUIntEstimate bound (.imp G body) ≤ 511 then boundedLiteralSearchAt (.imp (.all k .uint (.imp G body)) rhs) bound
    else none
  | _ => none

/-- A hit gives universal validity, never finite-state promotion. -/
theorem BoundedLiteralHit.valid {C : Contract} {B : LFml C}
    (hit : BoundedLiteralHit B) : B.Valid := hit.witness.valid

private theorem boundedLiteralSearchAt_complete {C : Contract} {B : LFml C}
    (bound value : PrimTy.uint.Denote) (hv : value.1.toNat < bound.1.toNat)
    (w : BoundedUIntLiteralInstance B value) :
    (boundedLiteralSearchAt B bound).isSome = true := by
  unfold boundedLiteralSearchAt
  apply List.findSome?_isSome_iff.mpr
  refine ⟨LTm.app0 (.lit value), uintSamples_complete bound value hv, ?_⟩
  have hc : (boundedUIntLiteralInstance? B value).isSome = true :=
    boundedUIntLiteralInstance_complete w
  simp only [LTm.litV?, Option.bind_eq_bind, Option.bind_some]
  cases he : boundedUIntLiteralInstance? B value with
  | none => rw [he] at hc; cases hc
  | some found => rfl

/-- Every in-range exact member is found when its original source estimate fits.
This is a completeness theorem for this schema, not for all target formulas. -/
theorem boundedUIntLiteralSearch_complete {C : Contract} {B : LFml C}
    {value : PrimTy.uint.Denote} (w : BoundedUIntLiteralInstance B value)
    (hb : boundedUIntEstimate w.bound (.imp (uintBelow w.index w.bound) w.body) ≤ 511) :
    (boundedUIntLiteralSearch? B).isSome = true := by
  rcases w with ⟨k, bound, body, hq, hv, heq⟩
  subst B
  change boundedUIntEstimate bound (.imp (uintBelow k bound) body) ≤ 511 at hb
  unfold boundedUIntLiteralSearch?
  simp only [boundedUIntGuard?, uintBelow, uintLtBoundCandidate, uintLtBinCandidate,
    LTm.litV?, leafFormula_same_self, dif_pos True.intro, Option.bind_eq_bind,
    Option.bind_some]
  simp only [uintBelow] at hb
  split
  · exact boundedLiteralSearchAt_complete bound value hv ⟨k, bound, body, hq, hv, rfl⟩
  · rename_i hbudget
    exact False.elim (hbudget hb)

/-- Concrete producer outputs plus the found syntax witness. This structure
alone does not claim that arbitrary certificates are recognized by a compiler. -/
structure BoundedUIntSourceHit {C : Contract} (φ : Fml C []) where
  source : SourceReduction φ
  universal : UniversalPrefix source.leaf.elim.condSimp.prenex
  hit : BoundedLiteralHit universal.body

/-- Existing source/prefix limits are unchanged; search never consults a verdict. -/
def boundedUIntSource? {C : Contract} (φ : Fml C []) : Option (BoundedUIntSourceHit φ) := do
  let r ← sourceReduction? φ
  let u ← UniversalPrefix.ofFormula? 1024 r.leaf.elim.condSimp.prenex
  let hit ← boundedUIntLiteralSearch? u.body
  return ⟨r, u, hit⟩

theorem BoundedUIntSourceHit.valid {C : Contract} {φ : Fml C []}
    (hit : BoundedUIntSourceHit φ) : Fml.Valid φ :=
  boundedUIntInstance_source_valid hit.source hit.universal hit.hit.witness

theorem BoundedUIntSourceHit.validH {C : Contract} {φ : Fml C []}
    (hit : BoundedUIntSourceHit φ) (hh : φ.hasHash = false) : Fml.ValidH φ :=
  (Fml.validH_iff hh).mpr hit.valid

end Solidity.Decide
