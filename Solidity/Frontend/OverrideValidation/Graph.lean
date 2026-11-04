import Solidity.Frontend.OverrideValidation.Attributes
import Solidity.Frontend.OverrideValidation.Routes

/-!
# Declaration edges and inherited frontiers

The graph reads the existing resolved Env. Path lookup is the existing Source
name-resolution boundary; override traversal does not call `baseFns`,
`inheritedVersion`, `dedupScope`, `ownFns` or `finalVersion`.

The propositional rules below quantify declaration positions and routes.
Their Boolean implementations enumerate those positions independently.
This module alone does not check override legality or graph pruning.
-/

namespace Solidity.Frontend.OverrideValidation

open Solidity.Source

/-- The positions of all original declarations, without name-based deduplication. -/
def nodes (E : Env) : List (Node E) := List.finRange E.decls.length

/-- A contract/interface declaration at file level. -/
def contractB (d : Decl) : Bool :=
  d.top && d.scope.isNone && (d.kind == .contract || d.kind == .interface)

/-- Direct base paths, retaining each complete path from Source syntax. -/
def basePaths (d : Decl) : List IdPath :=
  match d.kind, d.top, d.node with
  | .contract, _, .contract _ _ _ bs _ => inheritPaths bs
  | .interface, _, .interface _ bs _ => inheritPaths bs
  | _, _, _ => []

/-- A resolved contract reference within the fixed environment. Nominal
uniqueness must be established before using this as a unique binding. -/
def Refers (E : Env) (p : IdPath) (b : Node E) : Prop :=
  contractB b.decl = true ∧ ∃ d ∈ E.lookupPath none p,
    d.kind = b.decl.kind ∧ d.scope = b.decl.scope ∧ d.name = b.decl.name

def refersB (E : Env) (p : IdPath) (b : Node E) : Bool :=
  contractB b.decl && (E.lookupPath none p).any fun d =>
    d.kind == b.decl.kind && d.scope == b.decl.scope && d.name == b.decl.name

/-- One source inheritance edge, before any override traversal. -/
def BaseEdge (E : Env) (a b : Node E) : Prop :=
  contractB a.decl = true ∧ ∃ p ∈ basePaths a.decl, Refers E p b

def baseEdgeB (E : Env) (a b : Node E) : Bool :=
  contractB a.decl && (basePaths a.decl).any fun p => refersB E p b

/-- The original declaring contract of a callable position. -/
def Own (E : Env) (owner d : Node E) : Prop :=
  contractB owner.decl = true ∧ d.decl.scope = some owner.decl.name

def ownB (E : Env) (owner d : Node E) : Bool :=
  contractB owner.decl && d.decl.scope == some owner.decl.name

/-- Ordinary functions and generated public getters share an override namespace. -/
def ordinaryB (d : Decl) : Bool := family d == some .function || family d == some .getter

/-- A signature comparison primitive; location erasure is Source S01’s
existing type equality, not an override-frontier helper. -/
def Params (E : Env) (d f : Decl) : Prop :=
  ∃ ps rs qs ss, signature E d = some (ps, rs) ∧
    signature E f = some (qs, ss) ∧ STy.sameListUpToLoc ps qs = true

def paramsB (E : Env) (d f : Decl) : Bool :=
  match signature E d, signature E f with
  | some (ps, _), some (qs, _) => STy.sameListUpToLoc ps qs
  | _, _ => false

/-- Independent callable-slot rule. Fallback keys deliberately ignore their
parameter and return tuples, while modifier keys use the name alone.
Modifier parameter compatibility is a separate override obligation. -/
def SameSlot (E : Env) (d f : Decl) : Prop :=
  (ordinaryB d = true ∧ ordinaryB f = true ∧ d.name = f.name ∧ Params E d f) ∨
  (family d = some .fallback ∧ family f = some .fallback) ∨
  (family d = some .receive ∧ family f = some .receive) ∨
  (family d = some .modifier ∧ family f = some .modifier ∧ d.name = f.name)

def sameSlotB (E : Env) (d f : Decl) : Bool :=
  (ordinaryB d && ordinaryB f && d.name == f.name && paramsB E d f) ||
  (family d == some .fallback && family f == some .fallback) ||
  (family d == some .receive && family f == some .receive) ||
  (family d == some .modifier && family f == some .modifier && d.name == f.name)

/-- A declaration in an owner that can be inherited for a requested slot. -/
def OwnMatching (E : Env) (request owner d : Node E) : Prop :=
  Own E owner d ∧ SameSlot E request.decl d.decl ∧ d.decl.isPrivate = false

def ownMatchingB (E : Env) (request owner d : Node E) : Bool :=
  ownB E owner d && sameSlotB E request.decl d.decl && !d.decl.isPrivate

/-- A graph route over a proposition-valued edge relation. -/
inductive RelRoute {n : Nat} (edge : Fin n → Fin n → Prop) :
    List (Fin n) → Fin n → Fin n → Prop where
  | done {available : List (Fin n)} {a : Fin n} : RelRoute edge available a a
  | step {available : List (Fin n)} {a b next : Fin n} :
      a ≠ b → a ∈ available → edge a next →
      RelRoute edge (available.erase a) next b → RelRoute edge available a b

/-- A path stops at an owner declaring the requested slot. -/
def ShadowStep (E : Env) (request a b : Node E) : Prop :=
  BaseEdge E a b ∧ ∀ d : Node E, ¬ OwnMatching E request a d

def shadowStepB (E : Env) (request a b : Node E) : Bool :=
  baseEdgeB E a b && !((nodes E).any fun d => ownMatchingB E request a d)

/-- Every declaration reached along a direct-base route until its first
matching owner is retained. This keeps distinct inherited declarations even
when they are reached through one intermediate contract. -/
def Frontier (E : Env) (c request chosen : Node E) : Prop :=
  ∃ b owner : Node E, BaseEdge E c b ∧ OwnMatching E request owner chosen ∧
    RelRoute (ShadowStep E request) (nodes E) b owner

def frontierB (E : Env) (c request chosen : Node E) : Bool :=
  (nodes E).any fun b => baseEdgeB E c b && (nodes E).any fun owner =>
    ownMatchingB E request owner chosen && routeB (shadowStepB E request) (nodes E) b owner

/-- The inherited declarations keep their complete original positions. -/
def inherited (E : Env) (c request : Node E) : List (Node E) :=
  (nodes E).filter (frontierB E c request)

/-- Every actual position occurs in the finite enumeration. -/
theorem mem_nodes {E : Env} (d : Node E) : d ∈ nodes E :=
  List.mem_ofFn.mpr ⟨d, rfl⟩

theorem any_nodes_iff {E : Env} {p : Node E → Bool} :
    (nodes E).any p = true ↔ ∃ d : Node E, p d = true := by
  simp only [List.any_eq_true]
  exact ⟨fun ⟨d, _, hd⟩ => ⟨d, hd⟩, fun ⟨d, hd⟩ => ⟨d, mem_nodes d, hd⟩⟩

theorem refersB_iff {E : Env} {p : IdPath} {b : Node E} :
    refersB E p b = true ↔ Refers E p b := by
  simp only [refersB, Refers, Bool.and_eq_true, List.any_eq_true, beq_iff_eq, and_assoc]

theorem baseEdgeB_iff {E : Env} {a b : Node E} :
    baseEdgeB E a b = true ↔ BaseEdge E a b := by
  simp only [baseEdgeB, BaseEdge, Bool.and_eq_true, List.any_eq_true, refersB_iff]

theorem ownB_iff {E : Env} {owner d : Node E} : ownB E owner d = true ↔ Own E owner d := by
  simp only [ownB, Own, Bool.and_eq_true, beq_iff_eq]

theorem paramsB_iff {E : Env} {d f : Decl} : paramsB E d f = true ↔ Params E d f := by
  unfold paramsB Params
  cases hd : signature E d with
  | none => simp only [reduceCtorEq, false_and, exists_false]
  | some pair =>
    obtain ⟨ps, rs⟩ := pair
    cases hf : signature E f with
    | none => simp only [reduceCtorEq, false_and, and_false, exists_false]
    | some pair =>
      obtain ⟨qs, ss⟩ := pair
      simp only [Option.some.injEq, Prod.mk.injEq, and_assoc, exists_and_left, exists_eq_left']

theorem sameSlotB_iff {E : Env} {d f : Decl} : sameSlotB E d f = true ↔ SameSlot E d f := by
  simp only [sameSlotB, SameSlot, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    paramsB_iff, and_assoc, or_assoc]

theorem ownMatchingB_iff {E : Env} {request owner d : Node E} :
    ownMatchingB E request owner d = true ↔ OwnMatching E request owner d := by
  simp only [ownMatchingB, OwnMatching, Bool.and_eq_true, Bool.not_eq_true',
    ownB_iff, sameSlotB_iff, and_assoc]

theorem route_rel_iff {n : Nat} {edgeB : Fin n → Fin n → Bool}
    {edgeP : Fin n → Fin n → Prop} (edge_ok : ∀ a b, edgeB a b = true ↔ edgeP a b)
    {available : List (Fin n)} {a b : Fin n} :
    Route edgeB available a b ↔ RelRoute edgeP available a b := by
  constructor
  · intro h
    induction h with
    | done => exact .done
    | step hn hm he _ ih => exact .step hn hm ((edge_ok _ _).mp he) ih
  · intro h
    induction h with
    | done => exact .done
    | step hn hm he _ ih => exact .step hn hm ((edge_ok _ _).mpr he) ih

theorem routeB_rel_iff {n : Nat} {edgeB : Fin n → Fin n → Bool}
    {edgeP : Fin n → Fin n → Prop} (edge_ok : ∀ a b, edgeB a b = true ↔ edgeP a b)
    {available : List (Fin n)} {a b : Fin n} :
    routeB edgeB available a b = true ↔ RelRoute edgeP available a b :=
  (routeB_iff edgeB available a b).trans (route_rel_iff edge_ok)

theorem shadowStepB_iff {E : Env} {request a b : Node E} :
    shadowStepB E request a b = true ↔ ShadowStep E request a b := by
  simp only [shadowStepB, ShadowStep, Bool.and_eq_true, baseEdgeB_iff, Bool.not_eq_true',
    Bool.eq_false_iff, ne_eq, any_nodes_iff, ownMatchingB_iff, not_exists]

theorem frontierB_iff {E : Env} {c request chosen : Node E} :
    frontierB E c request chosen = true ↔ Frontier E c request chosen := by
  simp only [frontierB, any_nodes_iff, Bool.and_eq_true, baseEdgeB_iff, ownMatchingB_iff,
    routeB_rel_iff (fun _ _ => shadowStepB_iff), Frontier]
  constructor
  · rintro ⟨b, hb, owner, ho, hr⟩
    exact ⟨b, owner, hb, ho, hr⟩
  · rintro ⟨b, owner, hb, ho, hr⟩
    exact ⟨b, hb, owner, ho, hr⟩

theorem mem_inherited_iff {E : Env} {c request chosen : Node E} :
    chosen ∈ inherited E c request ↔ Frontier E c request chosen := by
  simp only [inherited, List.mem_filter, mem_nodes, true_and, frontierB_iff]

end Solidity.Frontend.OverrideValidation
