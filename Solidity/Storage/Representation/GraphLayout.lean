import Solidity.Storage.Representation.Words
import Solidity.Semantics.RecursiveStorage.Paths

/-! Full-word inline sizes and symbolic locations for the existing declaration
 graph. Private fuel follows the certified inline rank, never runtime path
 depth. Public path composition has no depth cutoff. -/
namespace Solidity.Storage.Representation.Graph

private def sizeBelow {n : Nat} (G : TypeGraph.Schema n) : Nat → TypeGraph.Ty n → Nat
  | 0, _ => 0
  | _ + 1, .prim _ => 1
  | k + 1, .node i => ((G.fields i).map (fun f => sizeBelow G k f.2)).sum
  | _ + 1, .array _ => 1
  | k + 1, .fixed E m => m.val * sizeBelow G k E
  | _ + 1, .mapping _ _ => 1

private theorem sizeBelow_stable {n : Nat} (G : TypeGraph.Schema n) (a : Nat) :
    ∀ (b : Nat) (T : TypeGraph.Ty n), T.inlineRank G.rank < a → T.inlineRank G.rank < b →
      sizeBelow G a T = sizeBelow G b T := by
  induction a with
  | zero => intro b T ha _; omega
  | succ a ih =>
    intro b T ha hb
    cases b with
    | zero => omega
    | succ b =>
      cases T with
      | prim p => rfl
      | array E => rfl
      | mapping K V => rfl
      | fixed E m =>
        simp only [TypeGraph.Ty.inlineRank] at ha hb
        exact congrArg (fun s => m.val * s) (ih b E (by omega) (by omega))
      | node i =>
        simp only [sizeBelow]
        apply congrArg List.sum
        apply List.map_congr_left
        intro f hf
        have rank : f.2.inlineRank G.rank < G.rank i := G.guarded i f hf
        exact ih b f.2 (by change G.rank i < a + 1 at ha; omega)
          (by change G.rank i < b + 1 at hb; omega)

/-- Canonical full-word inline size, stopping at mapping/dynamic-array headers. -/
def inlineSize {n : Nat} (G : TypeGraph.Schema n) (T : TypeGraph.Ty n) : Nat :=
  sizeBelow G (T.inlineRank G.rank + 1) T

theorem inlineSize_prim {n : Nat} (G : TypeGraph.Schema n) (p : PrimTy) :
    inlineSize G (.prim p) = 1 := rfl

theorem inlineSize_mapping {n : Nat} (G : TypeGraph.Schema n) (K : PrimTy) (V : TypeGraph.Ty n) :
    inlineSize G (.mapping K V) = 1 := rfl

theorem inlineSize_array {n : Nat} (G : TypeGraph.Schema n) (E : TypeGraph.Ty n) :
    inlineSize G (.array E) = 1 := rfl

theorem inlineSize_fixed {n : Nat} (G : TypeGraph.Schema n) (E : TypeGraph.Ty n)
    (m : TypeGraph.FixedSize) : inlineSize G (.fixed E m) = m.val * inlineSize G E := rfl

theorem inlineSize_node {n : Nat} (G : TypeGraph.Schema n) (i : Fin n) :
    inlineSize G (.node i) = ((G.fields i).map (fun f => inlineSize G f.2)).sum := by
  unfold inlineSize
  simp only [TypeGraph.Ty.inlineRank, sizeBelow]
  apply congrArg List.sum
  apply List.map_congr_left
  intro f hf
  exact sizeBelow_stable G (G.rank i) (f.2.inlineRank G.rank + 1) f.2
    (G.guarded i f hf) (Nat.lt_succ_self _)

/-- Existing typed steps interpreted with the same Loc/add/hash/data formulas.
Recursors preserve Gate G0; no alternate untyped path language is introduced. -/
noncomputable def stepLoc {n : Nat} {G : TypeGraph.Schema n} {A B : TypeGraph.Ty n}
    (s : TypeGraph.Step G A B) (l : Loc) : Loc :=
  @TypeGraph.Step.rec n G (fun _ _ _ => Loc → Loc)
    (fun {i _} position l => l.add (((G.fields i).take position.toNat).map
      (fun f => inlineSize G f.2)).sum)
    (fun {E} i l => .data l (i.val * inlineSize G E))
    (fun {E _} i l => l.add (i.val * inlineSize G E))
    (fun {_ _} k l => .hash (keyWord k) l 0) A B s l

noncomputable def pathLoc {n : Nat} {G : TypeGraph.Schema n} {A B : TypeGraph.Ty n}
    (p : TypeGraph.Path G A B) (l : Loc) : Loc :=
  @TypeGraph.Path.rec n G (fun _ _ _ => Loc → Loc) (fun {_} l => l)
    (fun {_ _ _} step _ ih l => ih (stepLoc step l)) A B p l

noncomputable def StepSupported {n : Nat} {G : TypeGraph.Schema n} {A B : TypeGraph.Ty n}
    (s : TypeGraph.Step G A B) : Prop :=
  @TypeGraph.Step.rec n G (fun _ _ _ => Prop) (fun {_ _} _ => True)
    (fun {_} i => i.val < lmax) (fun {_ m} i => i.val < m.val)
    (fun {_ _} _ => True) A B s

noncomputable def PathSupported {n : Nat} {G : TypeGraph.Schema n} {A B : TypeGraph.Ty n}
    (p : TypeGraph.Path G A B) : Prop :=
  @TypeGraph.Path.rec n G (fun _ _ _ => Prop) (fun {_} => True)
    (fun {_ _ _} step _ ih => StepSupported step ∧ ih) A B p

/-- Arbitrarily long finite graph paths compose symbolically without truncation. -/
theorem pathLoc_append {n : Nat} {G : TypeGraph.Schema n} {A B C : TypeGraph.Ty n}
    (p : TypeGraph.Path G A B) (q : TypeGraph.Path G B C) (l : Loc) :
    pathLoc (p.append q) l = pathLoc q (pathLoc p l) := by
  induction p generalizing l with
  | nil => rfl
  | cons s p ih => exact ih q (stepLoc s l)

theorem path_append_nil {n : Nat} {G : TypeGraph.Schema n} {A B : TypeGraph.Ty n}
    (p : TypeGraph.Path G A B) : p.append .nil = p := by
  induction p with
  | nil => rfl
  | cons s p ih => exact congrArg (TypeGraph.Path.cons s) ih

theorem PathSupported_append {n : Nat} {G : TypeGraph.Schema n} {A B C : TypeGraph.Ty n}
    (p : TypeGraph.Path G A B) (q : TypeGraph.Path G B C) :
    PathSupported (p.append q) ↔ PathSupported p ∧ PathSupported q := by
  induction p with
  | nil => exact ⟨fun h => ⟨True.intro, h⟩, fun h => h.2⟩
  | cons s p ih =>
    change (StepSupported s ∧ PathSupported (p.append q)) ↔
      (StepSupported s ∧ PathSupported p) ∧ PathSupported q
    rw [ih]
    exact and_assoc.symm

end Solidity.Storage.Representation.Graph
