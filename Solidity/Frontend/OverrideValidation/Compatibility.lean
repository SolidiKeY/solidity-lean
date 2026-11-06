import Solidity.Frontend.OverrideValidation.Graph

/-! Independent per-edge override obligations, over original declarations.
Graph construction and declaration validity are separate obligations. -/
namespace Solidity.Frontend.OverrideValidation
open Solidity.Source

/-- Equal visibility, or external becoming public. A getter is external as a callable. -/
def VisibilityAllowed (base derived : Option Visibility) : Prop :=
  base = derived ∨ base = some .external ∧ derived = some .pub

def visibilityAllowedB (base derived : Option Visibility) : Bool :=
  base == derived || (base == some .external && derived == some .pub)

/-- Payability is invariant; other mutability may become stricter. -/
def MutabilityAllowed (base derived : Option Mutability) : Prop :=
  base = derived ∨ (base = none ∧ (derived = some .view ∨ derived = some .pure)) ∨
    (base = some .view ∧ derived = some .pure)

def mutabilityAllowedB (base derived : Option Mutability) : Bool :=
  base == derived || (base == none && (derived == some .view || derived == some .pure)) ||
    (base == some .view && derived == some .pure)

/-- A type obligation names the actual extracted Source parameter/return lists. -/
def SignatureCondition (E : Env) (base derived : Decl)
    (condition : List STy → List STy → List STy → List STy → Bool) : Prop :=
  ∃ ps rs qs ss, signature E base = some (ps, rs) ∧
    signature E derived = some (qs, ss) ∧ condition ps rs qs ss = true

def signatureConditionB (E : Env) (base derived : Decl)
    (condition : List STy → List STy → List STy → List STy → Bool) : Bool :=
  match signature E base, signature E derived with
  | some (ps, rs), some (qs, ss) => condition ps rs qs ss
  | _, _ => false

/-- Modifiers must preserve parameters. Fallbacks may change their tuples.
Other callables preserve return types; non-external function overrides also
preserve the original parameter/return data locations (7723, 1443). -/
def PairTypes (E : Env) (base derived : Decl) : Prop :=
  (family derived = some .modifier →
    SignatureCondition E base derived (fun ps _ qs _ => STy.sameList ps qs)) ∧
  (family derived ≠ some .modifier → family derived ≠ some .fallback →
    SignatureCondition E base derived (fun _ rs _ ss => STy.sameListUpToLoc rs ss) ∧
    (family derived = some .function → visibility base ≠ some .external →
      SignatureCondition E base derived (fun ps rs qs ss =>
        STy.sameList ps qs && STy.sameList rs ss)))

def pairTypesB (E : Env) (base derived : Decl) : Bool :=
  (family derived != some .modifier ||
    signatureConditionB E base derived (fun ps _ qs _ => STy.sameList ps qs)) &&
  (family derived == some .modifier || family derived == some .fallback ||
    (signatureConditionB E base derived (fun _ rs _ ss => STy.sameListUpToLoc rs ss) &&
      (family derived != some .function || visibility base == some .external ||
        signatureConditionB E base derived (fun ps rs qs ss =>
          STy.sameList ps qs && STy.sameList rs ss))))

/-- Solidity FunctionDefinition families; getters and modifiers are separate. -/
def functionLikeB (d : Decl) : Bool :=
  family d == some .function || family d == some .fallback || family d == some .receive

/-- Interface functions, fallback and receive are implicitly virtual. -/
def Virtual (E : Env) (d : Decl) : Prop :=
  writtenVirtual d = true ∨ functionLikeB d = true ∧ E.scopeKind d.scope = some .interface

def virtualB (E : Env) (d : Decl) : Bool :=
  writtenVirtual d || (functionLikeB d && E.scopeKind d.scope == some .interface)

/-- The compatibility obligations on one declaration-graph override edge. -/
structure Compatible (E : Env) (base derived : Decl) : Prop where
  notGetter : family base ≠ some .getter
  virtual : Virtual E base
  visibility : VisibilityAllowed (visibility base) (visibility derived)
  mutability : family derived = some .modifier ∨ MutabilityAllowed (mutability base) (mutability derived)
  keepsBody : implemented base = true → implemented derived = true
  types : PairTypes E base derived

def compatibleB (E : Env) (base derived : Decl) : Bool :=
  family base != some .getter && virtualB E base &&
    visibilityAllowedB (visibility base) (visibility derived) &&
    (family derived == some .modifier || mutabilityAllowedB (mutability base) (mutability derived)) &&
    (!implemented base || implemented derived) && pairTypesB E base derived

theorem visibilityAllowedB_iff {base derived : Option Visibility} :
    visibilityAllowedB base derived = true ↔ VisibilityAllowed base derived := by
  simp only [visibilityAllowedB, VisibilityAllowed, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]

theorem mutabilityAllowedB_iff {base derived : Option Mutability} :
    mutabilityAllowedB base derived = true ↔ MutabilityAllowed base derived := by
  simp only [mutabilityAllowedB, MutabilityAllowed, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq, or_assoc]

theorem signatureConditionB_iff {E : Env} {base derived : Decl}
    {condition : List STy → List STy → List STy → List STy → Bool} :
    signatureConditionB E base derived condition = true ↔ SignatureCondition E base derived condition := by
  unfold signatureConditionB SignatureCondition
  cases hb : signature E base with
  | none => simp only [reduceCtorEq, false_and, exists_false]
  | some pair =>
    obtain ⟨ps, rs⟩ := pair
    cases hd : signature E derived with
    | none => simp only [reduceCtorEq, false_and, and_false, exists_false]
    | some pair =>
      obtain ⟨qs, ss⟩ := pair
      simp only [Option.some.injEq, Prod.mk.injEq, and_assoc, exists_and_left,
        exists_eq_left']

theorem virtualB_iff {E : Env} {d : Decl} : virtualB E d = true ↔ Virtual E d := by
  simp only [virtualB, Virtual, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]

theorem pairTypesB_iff {E : Env} {base derived : Decl} :
    pairTypesB E base derived = true ↔ PairTypes E base derived := by
  simp only [pairTypesB, PairTypes, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne,
    beq_iff_eq, signatureConditionB_iff]
  grind

theorem compatibleB_iff {E : Env} {base derived : Decl} :
    compatibleB E base derived = true ↔ Compatible E base derived := by
  simp only [compatibleB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    bne_iff_ne, beq_iff_eq, virtualB_iff, visibilityAllowedB_iff, mutabilityAllowedB_iff,
    pairTypesB_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨hg, hv⟩, hvis⟩, hmu⟩, hb⟩, ht⟩
    refine ⟨hg, hv, hvis, hmu, ?_, ht⟩
    intro hi
    rcases hb with hb | hb
    · rw [hi] at hb
      cases hb
    · exact hb
  · intro h
    refine ⟨⟨⟨⟨⟨h.notGetter, h.virtual⟩, h.visibility⟩, h.mutability⟩, ?_⟩, h.types⟩
    cases hi : implemented base with
    | false => exact .inl rfl
    | true => exact .inr (h.keepsBody hi)

end Solidity.Frontend.OverrideValidation
