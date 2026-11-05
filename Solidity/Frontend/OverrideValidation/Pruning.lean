import Solidity.Frontend.OverrideValidation.OverrideFrontier

/-! Override-graph cut vertices and ambiguity pruning. Artificial root/top
vertices are graph administration; every real vertex is an original Env position. -/
namespace Solidity.Frontend.OverrideValidation
open Solidity.Source

/-- One declaration overrides a frontier declaration of its own owner. -/
def OverrideEdge (E : Env) (d f : Node E) : Prop :=
  ∃ owner, Own E owner d ∧ OverrideFrontier E owner d f

def overrideEdgeB (E : Env) (d f : Node E) : Bool :=
  (nodes E).any fun owner => ownB E owner d && overrideFrontierB E owner d f

def Active (E : Env) (c key d : Node E) : Prop :=
  ∃ root, OverrideFrontier E c key root ∧ RelRoute (OverrideEdge E) (nodes E) root d

def activeB (E : Env) (c key d : Node E) : Bool :=
  (nodes E).any fun root => overrideFrontierB E c key root &&
    routeB (overrideEdgeB E) (nodes E) root d

abbrev GraphVertex (E : Env) := Fin (E.decls.length + 2)

def realVertex {E : Env} (d : Node E) : GraphVertex E :=
  ⟨d.val, Nat.lt.step (Nat.lt.step d.isLt)⟩

def rootVertex (E : Env) : GraphVertex E :=
  ⟨E.decls.length, Nat.lt.step (Nat.lt_succ_self _)⟩

def topVertex (E : Env) : GraphVertex E :=
  ⟨E.decls.length + 1, Nat.lt_succ_self _⟩

def realNode (E : Env) (v : GraphVertex E) : Option (Node E) :=
  if h : v.val < E.decls.length then some ⟨v.val, h⟩ else none

def vertices (E : Env) : List (GraphVertex E) := List.finRange (E.decls.length + 2)

/-- Undirected override graph, with a root incident to inherited declarations
and a top incident to active leaves. Inactive declarations have no edges. -/
def Adjacent (E : Env) (c key : Node E) (a b : GraphVertex E) : Prop :=
  match realNode E a, realNode E b with
  | some d, some f => Active E c key d ∧ Active E c key f ∧
      (OverrideEdge E d f ∨ OverrideEdge E f d)
  | none, some f => (a = rootVertex E ∧ OverrideFrontier E c key f) ∨
      (a = topVertex E ∧ Active E c key f ∧ ∀ g, ¬ OverrideEdge E f g)
  | some d, none => (b = rootVertex E ∧ OverrideFrontier E c key d) ∨
      (b = topVertex E ∧ Active E c key d ∧ ∀ g, ¬ OverrideEdge E d g)
  | none, none => False

def adjacentB (E : Env) (c key : Node E) (a b : GraphVertex E) : Bool :=
  match realNode E a, realNode E b with
  | some d, some f => activeB E c key d && activeB E c key f &&
      (overrideEdgeB E d f || overrideEdgeB E f d)
  | none, some f => (a == rootVertex E && overrideFrontierB E c key f) ||
      (a == topVertex E && activeB E c key f && !((nodes E).any fun g => overrideEdgeB E f g))
  | some d, none => (b == rootVertex E && overrideFrontierB E c key d) ||
      (b == topVertex E && activeB E c key d && !((nodes E).any fun g => overrideEdgeB E d g))
  | none, none => false

/-- Delete all incident edges, retaining endpoint identity. -/
def Avoiding (E : Env) (c key removed : Node E) (a b : GraphVertex E) : Prop :=
  Adjacent E c key a b ∧ a ≠ realVertex removed ∧ b ≠ realVertex removed

def avoidingB (E : Env) (c key removed : Node E) (a b : GraphVertex E) : Bool :=
  adjacentB E c key a b && a != realVertex removed && b != realVertex removed

/-- A real active cut vertex disconnects two other vertices that were connected. -/
def CutVertex (E : Env) (c key v : Node E) : Prop :=
  Active E c key v ∧ ∃ a b : GraphVertex E, a ≠ realVertex v ∧ b ≠ realVertex v ∧
    RelRoute (Adjacent E c key) (vertices E) a b ∧
    ¬ RelRoute (Avoiding E c key v) (vertices E) a b

def cutVertexB (E : Env) (c key v : Node E) : Bool :=
  activeB E c key v && (vertices E).any fun a => a != realVertex v &&
    (vertices E).any fun b => b != realVertex v &&
      routeB (adjacentB E c key) (vertices E) a b &&
      !routeB (avoidingB E c key v) (vertices E) a b

/-- An inherited declaration survives when no cut vertex overrides it, and
when it is not itself an unimplemented cut vertex (solc 6480 pruning). -/
def Retained (E : Env) (c key f : Node E) : Prop :=
  OverrideFrontier E c key f ∧ ∀ v, CutVertex E c key v →
    ¬ (v ≠ f ∧ RelRoute (OverrideEdge E) (nodes E) v f) ∧
    (v = f → implemented f.decl = true)

def retainedB (E : Env) (c key f : Node E) : Bool :=
  overrideFrontierB E c key f && (nodes E).all fun v => !cutVertexB E c key v ||
    ((v == f || !routeB (overrideEdgeB E) (nodes E) v f) &&
      (v != f || implemented f.decl))

def survivors (E : Env) (c key : Node E) : List (Node E) :=
  (nodes E).filter (retainedB E c key)

theorem any_fin_iff {n : Nat} {p : Fin n → Bool} :
    (List.finRange n).any p = true ↔ ∃ v, p v = true := by
  simp only [List.any_eq_true]
  exact ⟨fun ⟨v, _, hv⟩ => ⟨v, hv⟩,
    fun ⟨v, hv⟩ => ⟨v, List.mem_ofFn.mpr ⟨v, rfl⟩, hv⟩⟩

theorem all_nodes_iff {E : Env} {p : Node E → Bool} :
    (nodes E).all p = true ↔ ∀ v, p v = true := by
  simp only [List.all_eq_true]
  exact ⟨fun h v => h v (mem_nodes v), fun h v _ => h v⟩

theorem overrideEdgeB_iff {E : Env} {d f : Node E} :
    overrideEdgeB E d f = true ↔ OverrideEdge E d f := by
  simp only [overrideEdgeB, OverrideEdge, any_nodes_iff, Bool.and_eq_true, ownB_iff, overrideFrontierB_iff]

theorem activeB_iff {E : Env} {c key d : Node E} : activeB E c key d = true ↔ Active E c key d := by
  simp only [activeB, Active, any_nodes_iff, Bool.and_eq_true, overrideFrontierB_iff,
    routeB_rel_iff (fun _ _ => overrideEdgeB_iff)]

theorem adjacentB_iff {E : Env} {c key : Node E} {a b : GraphVertex E} :
    adjacentB E c key a b = true ↔ Adjacent E c key a b := by
  cases ha : realNode E a <;> cases hb : realNode E b <;>
    simp only [adjacentB, Adjacent, ha, hb, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq, activeB_iff, overrideEdgeB_iff, overrideFrontierB_iff, Bool.not_eq_true',
      Bool.eq_false_iff, ne_eq, any_nodes_iff, not_exists, and_assoc, Bool.false_eq_true]

theorem avoidingB_iff {E : Env} {c key v : Node E} {a b : GraphVertex E} :
    avoidingB E c key v a b = true ↔ Avoiding E c key v a b := by
  simp only [avoidingB, Avoiding, Bool.and_eq_true, adjacentB_iff, bne_iff_ne, and_assoc]

theorem cutVertexB_iff {E : Env} {c key v : Node E} :
    cutVertexB E c key v = true ↔ CutVertex E c key v := by
  simp only [cutVertexB, CutVertex, vertices, any_fin_iff, Bool.and_eq_true, bne_iff_ne,
    activeB_iff, routeB_rel_iff (fun _ _ => adjacentB_iff), Bool.not_eq_true',
    Bool.eq_false_iff, ne_eq, routeB_rel_iff (fun _ _ => avoidingB_iff)]
  constructor
  · rintro ⟨ha, a, hna, b, ⟨hnb, hp⟩, hn⟩
    exact ⟨ha, a, b, hna, hnb, hp, hn⟩
  · rintro ⟨ha, a, b, hna, hnb, hp, hn⟩
    exact ⟨ha, a, hna, b, ⟨hnb, hp⟩, hn⟩

theorem retainedB_iff {E : Env} {c key f : Node E} :
    retainedB E c key f = true ↔ Retained E c key f := by
  simp only [retainedB, Retained, Bool.and_eq_true, overrideFrontierB_iff, all_nodes_iff,
    Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, cutVertexB_iff,
    routeB_rel_iff (fun _ _ => overrideEdgeB_iff), beq_iff_eq, bne_iff_ne]
  grind

theorem mem_survivors_iff {E : Env} {c key f : Node E} :
    f ∈ survivors E c key ↔ Retained E c key f := by
  simp only [survivors, List.mem_filter, mem_nodes, true_and, retainedB_iff]

end Solidity.Frontend.OverrideValidation
