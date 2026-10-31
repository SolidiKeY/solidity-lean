import Solidity.Theory.Typed.Mem

/-!
# Finite, typed realizations for fresh memory structs

A witness lists actual child-first allocations. Each object can refer only
into the preceding heap typing; reusing a reference preserves sharing.
The telescope is computed from the list, as `MFields` is from its fields.
No extra heap objects or disjointness of children are assumed.

These are constructive auxiliaries for the memory cut, not new SolKey
rules. The observation and frame proofs use the typed `readOnAddM` laws.
-/

namespace Solidity.MemoryWitness

open Semantics (structDef lookupBy)

/-- The final typing after a finite list of append allocations. -/
def finalTy (H : HTy) : List RefTy → HTy
  | [] => H
  | R :: Rs => finalTy (H ++ [R]) Rs

/-- One typed object per allocation, with references into earlier objects. -/
def Plan (H : HTy) : List RefTy → Type
  | [] => Unit
  | R :: Rs => MObj H R × Plan (H ++ [R]) Rs

/-- The original typing remains a prefix. -/
def extension (H : HTy) : (Rs : List RefTy) → H <+: finalTy H Rs
  | [] => List.prefix_refl H
  | R :: Rs => (List.prefix_append H [R]).trans (extension (H ++ [R]) Rs)

/-- Realize every recorded object by the actual heap allocator. -/
def realize {H : HTy} (hp : Heap H) : (Rs : List RefTy) → Plan H Rs → Heap (finalTy H Rs)
  | [], _ => hp
  | _ :: Rs, w => realize (hp.alloc w.1).1 Rs w.2

/-- Realization adds exactly the recorded objects. -/
theorem finalTy_length (H : HTy) (Rs : List RefTy) :
    (finalTy H Rs).length = H.length + Rs.length := by
  induction Rs generalizing H with
  | nil => rfl
  | cons R Rs ih =>
    simp only [finalTy, ih, List.length_append, List.length_cons, List.length_nil]
    omega

/-- Every original object survives with precisely its weakened references. -/
theorem keeps {H : HTy} (hp : Heap H) (Rs : List RefTy) (w : Plan H Rs) :
    Heap.Keeps (extension H Rs) hp (realize hp Rs w) := by
  induction Rs generalizing H with
  | nil => exact Heap.Keeps.refl hp
  | cons R Rs ih => exact Heap.Keeps.trans (Heap.keeps_alloc hp w.1) (ih (hp.alloc w.1).1 w.2)

/-- A witness is an admissible heap growth for a state or a formula. -/
def grown {H : HTy} (hp : Heap H) (Rs : List RefTy) (w : Plan H Rs) :
    Grown H (fun _ => Unit) := ⟨extension H Rs, realize hp Rs w, ()⟩

/-- Allocate the fresh root after realizing its children. -/
def root {H : HTy} {R : RefTy} (hp : Heap H) (Rs : List RefTy) (w : Plan H Rs)
    (o : MObj (finalTy H Rs) R) : Grown H (MVal · (.ref R)) :=
  Grown.alloc ⟨extension H Rs, realize hp Rs w, o⟩

/-- Child realization followed by root allocation preserves the original heap. -/
theorem root_keeps {H : HTy} {R : RefTy} (hp : Heap H) (Rs : List RefTy) (w : Plan H Rs)
    (o : MObj (finalTy H Rs) R) :
    Heap.Keeps (root hp Rs w o).ext hp (root hp Rs w o).heap :=
  Grown.keeps_alloc _ (keeps hp Rs w)

/-- The fresh root is distinct from every child, including reused old objects. -/
theorem root_fresh {H : HTy} {R S : RefTy} (hp : Heap H) (Rs : List RefTy) (w : Plan H Rs)
    (o : MObj (finalTy H Rs) R) (r : HRef (finalTy H Rs) S) :
    (root hp Rs w o).val.id ≠ r.id := by
  have hr : r.id < (finalTy H Rs).length := (List.getElem?_eq_some_iff.mp r.get?).1
  change (finalTy H Rs).length ≠ r.id
  omega

/-- Weakening preserves both equality and inequality of child identities. -/
theorem sharing {H K : HTy} {R S : RefTy} (e : H <+: K) (r : HRef H R) (s : HRef H S) :
    (r.wk e).id = (s.wk e).id ↔ r.id = s.id := Iff.rfl

/-- Read back any root field, including a reference shared by several fields. -/
theorem root_field {H : HTy} {s f : Name} {T : Ty} (hp : Heap H) (Rs : List RefTy)
    (w : Plan H Rs) (o : MObj (finalTy H Rs) (.struct s))
    (hf : lookupBy f (structDef s) = some T) :
    (root hp Rs w o).heap.field (root hp Rs w o).val hf =
      MVal.wk (List.prefix_append (finalTy H Rs) [.struct s]) T
        (MFields.get (structDef s) o hf) :=
  Grown.alloc_field _ hf

/-- Exact scalar allocation cut at every heap, including the vacuous case.
Realizability is explicit: it cannot be silently assumed at an empty heap. -/
theorem word_cut {H : HTy} {s f : Name} {p : PrimTy} (hp : Heap H)
    (hf : lookupBy f (structDef s) = some (.prim p)) (Q : p.Denote → Prop) :
    (∀ o : MObj H (.struct s), Q ((hp.alloc o).1.field (hp.alloc o).2 hf)) ↔
      (Nonempty (MObj H (.struct s)) → ∀ v : p.Denote, Q v) := by
  have obs (o : MObj H (.struct s)) :
      (hp.alloc o).1.field (hp.alloc o).2 hf = MFields.get (structDef s) o hf := by
    change MFields.get _ ((hp.alloc o).1.get (hp.alloc o).2) hf = _
    rw [Heap.get_alloc]
    change MFields.get _ (MFields.wk _ _ o) hf = _
    rw [MFields.get_wk]
    rfl
  constructor
  · intro h ⟨seed⟩ v
    have hv : Q ((hp.alloc (R := .struct s) (MFields.set (structDef s) seed hf v)).1.field
        (hp.alloc (R := .struct s) (MFields.set (structDef s) seed hf v)).2 hf) := h _
    rw [obs, MFields.get_set_same] at hv
    exact hv
  · intro h o
    rw [obs]
    exact h ⟨o⟩ _

/-- Construct children of a supported finite struct from typed default fields.
This fallback establishes existence; explicit plans retain chosen sharing. -/
def children {H : HTy} (hp : Heap H) (s : Name)
    (h : ∀ fT ∈ structDef s, fT.2.mapFree = true) : Grown H (MObj · (.struct s)) :=
  SFields.copyStToM hp (SFields.dflt (structDef s)) h

/-- The constructed children preserve all original objects. -/
theorem children_keeps {H : HTy} (hp : Heap H) (s : Name)
    (h : ∀ fT ∈ structDef s, fT.2.mapFree = true) :
    Heap.Keeps (children hp s h).ext hp (children hp s h).heap :=
  SFields.keeps_copyStToM (SFields.dflt (structDef s)) h hp

/-- The scalar cut is globally exact once children are constructible.
The reverse direction uses an explicitly realized heap, not the empty heap. -/
theorem word_cut_global {s f : Name} {p : PrimTy}
    (hf : lookupBy f (structDef s) = some (.prim p))
    (h : ∀ fT ∈ structDef s, fT.2.mapFree = true) (Q : p.Denote → Prop) :
    (∀ (H : HTy) (hp : Heap H) (o : MObj H (.struct s)),
      Q ((hp.alloc o).1.field (hp.alloc o).2 hf)) ↔ ∀ v : p.Denote, Q v := by
  constructor
  · intro hall
    let g : Grown [] (MObj · (.struct s)) := children Heap.empty s h
    exact (word_cut g.heap hf Q).1 (hall g.H' g.heap) ⟨g.val⟩
  · intro hall H hp o
    exact hall _

/-- A mapping object cannot occur in a witness. -/
theorem no_mapping {H : HTy} {K : PrimTy} {T : Ty} : ¬ Nonempty (MObj H (.mapping K T)) :=
  fun ⟨o⟩ => o.elim

#print axioms word_cut_global
#print axioms children_keeps
#print axioms keeps
#print axioms root_keeps
#print axioms root_fresh
#print axioms root_field
#print axioms word_cut

end Solidity.MemoryWitness
