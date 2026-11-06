import Solidity.Frontend.OverrideValidation.Compatibility
import Solidity.Frontend.OverrideValidation.Pruning

/-! Independent required/missing/extraneous/duplicate override-list rules.
Every named entry resolves to an original contract position. -/
namespace Solidity.Frontend.OverrideValidation
open Solidity.Source

def HasBase (E : Env) (c key : Node E) : Prop := ∃ f, Frontier E c key f

def hasBaseB (E : Env) (c key : Node E) : Bool :=
  (nodes E).any (frontierB E c key)

def HasOverrideBase (E : Env) (c key : Node E) : Prop := ∃ f, OverrideFrontier E c key f

def hasOverrideBaseB (E : Env) (c key : Node E) : Bool :=
  (nodes E).any (overrideFrontierB E c key)

def Multiple (E : Env) (c key : Node E) : Prop :=
  ∃ f g, OverrideFrontier E c key f ∧ OverrideFrontier E c key g ∧ f ≠ g

def multipleB (E : Env) (c key : Node E) : Bool :=
  (nodes E).any fun f => overrideFrontierB E c key f &&
    (nodes E).any fun g => overrideFrontierB E c key g && f != g

/-- Exactly one inherited interface function needs no explicit specifier. -/
def SingleInterface (E : Env) (c key : Node E) : Prop :=
  ∃ f, OverrideFrontier E c key f ∧ functionLikeB f.decl = true ∧
    E.scopeKind f.decl.scope = some .interface ∧ ∀ g, OverrideFrontier E c key g → g = f

def singleInterfaceB (E : Env) (c key : Node E) : Bool :=
  (nodes E).any fun f => overrideFrontierB E c key f && functionLikeB f.decl &&
    E.scopeKind f.decl.scope == some .interface &&
      (nodes E).all fun g => !overrideFrontierB E c key g || g == f

/-- An entry names the actual owner of an inherited declaration. -/
def Listed (E : Env) (p : IdPath) (f : Node E) : Prop :=
  ∃ owner, Own E owner f ∧ Refers E p owner

def listedB (E : Env) (p : IdPath) (f : Node E) : Bool :=
  (nodes E).any fun owner => ownB E owner f && refersB E p owner

/-- Distinct spellings must not resolve to the same contract identity. -/
def PathsDisjoint (E : Env) (p q : IdPath) : Prop :=
  ∀ owner, ¬ (Refers E p owner ∧ Refers E q owner)

def pathsDistinctB (E : Env) : List IdPath → Bool
  | [] => true
  | p :: ps => (ps.all fun q => (nodes E).all fun owner =>
      !(refersB E p owner && refersB E q owner)) && pathsDistinctB E ps

structure NamedList (E : Env) (c key : Node E) (ps : List IdPath) : Prop where
  hasBase : HasOverrideBase E c key
  complete : Multiple E c key → ∀ f, OverrideFrontier E c key f → ∃ p ∈ ps, Listed E p f
  valid : ∀ p ∈ ps, ∃ f, OverrideFrontier E c key f ∧ Listed E p f
  distinct : ps.Pairwise (PathsDisjoint E)

def namedListB (E : Env) (c key : Node E) (ps : List IdPath) : Bool :=
  hasOverrideBaseB E c key &&
    (!multipleB E c key || (nodes E).all fun f => !overrideFrontierB E c key f || ps.any fun p => listedB E p f) &&
    (ps.all fun p => (nodes E).any fun f => overrideFrontierB E c key f && listedB E p f) &&
    pathsDistinctB E ps

/-- Specifier absence and presence have separate graph obligations. -/
def OverrideLists (E : Env) (c key : Node E) : Prop :=
  match overridePaths key.decl with
  | none => ¬ HasOverrideBase E c key ∨ SingleInterface E c key
  | some ps => NamedList E c key ps

def overrideListsB (E : Env) (c key : Node E) : Bool :=
  match overridePaths key.decl with
  | none => !hasOverrideBaseB E c key || singleInterfaceB E c key
  | some ps => namedListB E c key ps

theorem hasBaseB_iff {E : Env} {c key : Node E} : hasBaseB E c key = true ↔ HasBase E c key := by
  simp only [hasBaseB, HasBase, any_nodes_iff, frontierB_iff]

theorem hasOverrideBaseB_iff {E : Env} {c key : Node E} :
    hasOverrideBaseB E c key = true ↔ HasOverrideBase E c key := by
  simp only [hasOverrideBaseB, HasOverrideBase, any_nodes_iff, overrideFrontierB_iff]

theorem multipleB_iff {E : Env} {c key : Node E} : multipleB E c key = true ↔ Multiple E c key := by
  simp only [multipleB, Multiple, any_nodes_iff, Bool.and_eq_true, overrideFrontierB_iff, bne_iff_ne]
  constructor
  · rintro ⟨f, hf, g, hg, hne⟩
    exact ⟨f, g, hf, hg, hne⟩
  · rintro ⟨f, g, hf, hg, hne⟩
    exact ⟨f, hf, g, hg, hne⟩

theorem singleInterfaceB_iff {E : Env} {c key : Node E} :
    singleInterfaceB E c key = true ↔ SingleInterface E c key := by
  simp only [singleInterfaceB, SingleInterface, any_nodes_iff, Bool.and_eq_true,
    overrideFrontierB_iff, beq_iff_eq, all_nodes_iff, Bool.or_eq_true, Bool.not_eq_true',
    Bool.eq_false_iff, ne_eq]
  grind

theorem listedB_iff {E : Env} {p : IdPath} {f : Node E} : listedB E p f = true ↔ Listed E p f := by
  simp only [listedB, Listed, any_nodes_iff, Bool.and_eq_true, ownB_iff, refersB_iff]

theorem pathsDistinctB_iff {E : Env} {ps : List IdPath} :
    pathsDistinctB E ps = true ↔ ps.Pairwise (PathsDisjoint E) := by
  induction ps with
  | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
  | cons p ps ih =>
    simp only [pathsDistinctB, List.pairwise_cons, Bool.and_eq_true, List.all_eq_true,
      Bool.not_eq_true', Bool.eq_false_iff, ne_eq, Bool.and_eq_true,
      refersB_iff, ih, PathsDisjoint, mem_nodes, true_implies]

theorem namedListB_iff {E : Env} {c key : Node E} {ps : List IdPath} :
    namedListB E c key ps = true ↔ NamedList E c key ps := by
  simp only [namedListB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Bool.eq_false_iff, ne_eq, hasOverrideBaseB_iff, multipleB_iff,
    overrideFrontierB_iff, List.any_eq_true, listedB_iff, List.all_eq_true,
    pathsDistinctB_iff, mem_nodes, true_implies, true_and]
  constructor
  · rintro ⟨⟨⟨hh, hc⟩, hv⟩, hd⟩
    refine ⟨hh, ?_, hv, hd⟩
    intro hm f hf
    rcases hc with hn | hc
    · exact (hn hm).elim
    · rcases hc f with hn | hc
      · exact (hn hf).elim
      · exact hc
  · intro h
    refine ⟨⟨⟨h.hasBase, ?_⟩, h.valid⟩, h.distinct⟩
    by_cases hm : Multiple E c key
    · right
      intro f
      by_cases hf : OverrideFrontier E c key f
      · exact .inr (h.complete hm f hf)
      · exact .inl hf
    · exact .inl hm

theorem overrideListsB_iff {E : Env} {c key : Node E} :
    overrideListsB E c key = true ↔ OverrideLists E c key := by
  cases h : overridePaths key.decl <;>
    simp only [overrideListsB, OverrideLists, h, Bool.or_eq_true, Bool.not_eq_true',
      Bool.eq_false_iff, ne_eq, hasOverrideBaseB_iff, singleInterfaceB_iff, namedListB_iff]

def CrossFamily (d f : Decl) : Prop :=
  d.name = f.name ∧
    ((family d = some .modifier ∧ (functionLikeB f = true ∨ family f = some .getter)) ∨
     ((functionLikeB d = true ∨ family d = some .getter) ∧ family f = some .modifier))

def crossFamilyB (d f : Decl) : Bool :=
  d.name == f.name &&
    ((family d == some .modifier && (functionLikeB f || family f == some .getter)) ||
      ((functionLikeB d || family d == some .getter) && family f == some .modifier))

def NoCrossFamily (E : Env) (c d : Node E) : Prop :=
  ∀ f, OverrideFrontier E c f f → ¬ CrossFamily d.decl f.decl

def noCrossFamilyB (E : Env) (c d : Node E) : Bool :=
  (nodes E).all fun f => !overrideFrontierB E c f f || !crossFamilyB d.decl f.decl

theorem crossFamilyB_iff {d f : Decl} : crossFamilyB d f = true ↔ CrossFamily d f := by
  simp only [crossFamilyB, CrossFamily, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]

theorem noCrossFamilyB_iff {E : Env} {c d : Node E} :
    noCrossFamilyB E c d = true ↔ NoCrossFamily E c d := by
  simp only [noCrossFamilyB, NoCrossFamily, all_nodes_iff, Bool.or_eq_true,
    Bool.not_eq_true', Bool.eq_false_iff, ne_eq, overrideFrontierB_iff, crossFamilyB_iff]
  grind

/-- Visible inherited declarations cannot introduce a same-name modifier /
function-or-getter collision, even when the child declares neither slot. -/
def InheritedFamilies (E : Env) (c : Node E) : Prop :=
  ∀ f g, Frontier E c f f → Frontier E c g g → ¬ CrossFamily f.decl g.decl

def inheritedFamiliesB (E : Env) (c : Node E) : Bool :=
  (nodes E).all fun f => !frontierB E c f f ||
    (nodes E).all fun g => !frontierB E c g g || !crossFamilyB f.decl g.decl

theorem inheritedFamiliesB_iff {E : Env} {c : Node E} :
    inheritedFamiliesB E c = true ↔ InheritedFamilies E c := by
  simp only [inheritedFamiliesB, InheritedFamilies, all_nodes_iff, Bool.or_eq_true,
    Bool.not_eq_true', Bool.eq_false_iff, ne_eq, frontierB_iff, crossFamilyB_iff]
  grind

/-- Scope priority uses the already checked Source C3 chain. The getter
namespace rule is directional: a higher-priority getter can hide a function
with other parameters, but a higher-priority function cannot hide a getter. -/
def ScopeEarlier (E : Env) (c d f : Node E) : Prop :=
  (E.chain c.decl.name).idxOf (d.decl.scope.getD "") <
    (E.chain c.decl.name).idxOf (f.decl.scope.getD "")

def NamespaceConflict (E : Env) (c d f : Node E) : Prop :=
  d.decl.name = f.decl.name ∧
    ((family d.decl = some .getter ∧ family f.decl = some .getter ∧ d ≠ f) ∨
     (family d.decl = some .function ∧ family f.decl = some .getter ∧ ScopeEarlier E c d f))

def namespaceConflictB (E : Env) (c d f : Node E) : Bool :=
  d.decl.name == f.decl.name &&
    ((family d.decl == some .getter && family f.decl == some .getter && d != f) ||
     (family d.decl == some .function && family f.decl == some .getter && decide ((E.chain c.decl.name).idxOf (d.decl.scope.getD "") < (E.chain c.decl.name).idxOf (f.decl.scope.getD ""))))

def MemberNames (E : Env) (c : Node E) : Prop :=
  ∀ d f, (Own E c d ∨ Frontier E c d d) → (Own E c f ∨ Frontier E c f f) →
    ¬ NamespaceConflict E c d f

def memberNamesB (E : Env) (c : Node E) : Bool :=
  (nodes E).all fun d => !(ownB E c d || frontierB E c d d) ||
    (nodes E).all fun f => !(ownB E c f || frontierB E c f f) || !namespaceConflictB E c d f

theorem namespaceConflictB_iff {E : Env} {c d f : Node E} :
    namespaceConflictB E c d f = true ↔ NamespaceConflict E c d f := by
  simp only [namespaceConflictB, NamespaceConflict, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq, bne_iff_ne, decide_eq_true_eq, ScopeEarlier, and_assoc]

theorem memberNamesB_iff {E : Env} {c : Node E} : memberNamesB E c = true ↔ MemberNames E c := by
  simp only [memberNamesB, MemberNames, all_nodes_iff, Bool.or_eq_true,
    Bool.not_eq_true', Bool.eq_false_iff, ne_eq, ownB_iff, frontierB_iff, namespaceConflictB_iff]
  grind

/-- Lists and edge compatibility are both checked for each own declaration. -/
def DeclarationOverrides (E : Env) (c d : Node E) : Prop :=
  OverrideLists E c d ∧ (∀ f, OverrideFrontier E c d f → Compatible E f.decl d.decl) ∧ NoCrossFamily E c d

def declarationOverridesB (E : Env) (c d : Node E) : Bool :=
  overrideListsB E c d && ((nodes E).all fun f => !overrideFrontierB E c d f || compatibleB E f.decl d.decl) && noCrossFamilyB E c d

theorem declarationOverridesB_iff {E : Env} {c d : Node E} :
    declarationOverridesB E c d = true ↔ DeclarationOverrides E c d := by
  simp only [declarationOverridesB, DeclarationOverrides, Bool.and_eq_true,
    overrideListsB_iff, all_nodes_iff, noCrossFamilyB_iff, Bool.or_eq_true, Bool.not_eq_true',
    Bool.eq_false_iff, ne_eq, overrideFrontierB_iff, compatibleB_iff]
  grind

end Solidity.Frontend.OverrideValidation
