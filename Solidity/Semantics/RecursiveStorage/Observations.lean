import Solidity.Semantics.RecursiveStorage.Arrays

namespace Solidity.TypeGraph

/-- A suffix observes exactly the subtree returned by the prefix, including
failure at either stage. -/
theorem Value.observe_append {n : Nat} {G : Schema n} {A B C : Ty n}
    (root : Value G A) (p : Path G A B) (q : Path G B C) :
    root.observe (p.append q) = (root.find p).bind (fun v => v.observe q) := by
  unfold Value.observe Value.find
  rw [Path.read_append]
  cases p.read Value.dflt root <;> rfl

theorem Value.ObsEq.refl {n : Nat} {G : Schema n} {T : Ty n}
    (v : Value G T) : v.ObsEq v := fun _ => rfl

theorem Value.ObsEq.symm {n : Nat} {G : Schema n} {T : Ty n}
    {v w : Value G T} (h : v.ObsEq w) : w.ObsEq v := fun p => (h p).symm

theorem Value.ObsEq.trans {n : Nat} {G : Schema n} {T : Ty n}
    {u v w : Value G T} (h : u.ObsEq v) (k : v.ObsEq w) : u.ObsEq w :=
  fun p => (h p).trans (k p)

/-- Observational equivalence descends to every successfully read subtree.
The relation observes extents as well as live lengths. -/
theorem Value.ObsEq.at {n : Nat} {G : Schema n} {A B : Ty n}
    {v w : Value G A} (h : v.ObsEq w) (p : Path G A B)
    {a b : Value G B} (ha : v.find p = some a) (hb : w.find p = some b) :
    a.ObsEq b := by
  intro U q
  have eq : v.observe (p.append q) = w.observe (p.append q) := h (p.append q)
  simpa only [Value.observe_append, ha, hb, Option.bind_some] using eq

/-- Normalizing an implicit mapping fallback to an explicit default preserves
all finite observations, even when the value type recursively refers back to
its declaration. Raw constructor equality is unnecessary. -/
theorem Value.mapping_defaults_obsEq {n : Nat} {G : Schema n} {K : PrimTy} {V : Ty n} :
    (Value.mapping (fun _ : K.Denote => (Slot.absent : Slot G V))).ObsEq
      (.mapping (fun _ => .present (Value.dflt V))) := by
  intro U p
  cases p with
  | nil => rfl
  | cons s rest => cases s; rfl

end Solidity.TypeGraph
