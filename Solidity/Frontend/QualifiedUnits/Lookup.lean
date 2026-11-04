import Solidity.Frontend.QualifiedUnits.Relation
import Solidity.Frontend.Static.Units

/-!
# Executable qualified lookup

Finite import saturation is reused unchanged. Each recursive call consumes
one path component. Namespace declarations keep the unit and position of
the original graph. The raw candidate relation is separate from refusal
policy: a nonempty answer is not by itself an acceptance certificate.
-/
namespace Solidity.Frontend.QualifiedUnits
open Solidity.Source Solidity.Frontend.Static

/-- Direct declaration members, indexed in the original unit. -/
def members (P : UnitSet) (i : DeclId) (x : String) : List DeclId :=
  match P.decl? i, P.unit? i.unit with
  | some d, some s =>
    if Container d.kind then
      ((idxWhere (fun e => e.scope == some d.name && e.name == x && x != "") s.decls 0).filter
        (fun j => decide (i.idx < j ∧ j ≤ i.idx + memberCount d))).map
        (fun j => ⟨i.unit, j⟩)
    else []
  | _, _ => []

/-- All candidates for one namespace component. -/
def step (P : UnitSet) (R : List Remapping) (a : Sym) (x : String) : List Sym :=
  match a with
  | .unit u => P.globals R u x
  | .decl i => (members P i x).map Sym.decl

/-- Raw suffix lookup; structural recursion gives termination for arbitrary
finite paths, even when import namespaces point back to earlier units. -/
def through (P : UnitSet) (R : List Remapping) (a : Sym) : List String → List Sym
  | [] => [a]
  | x :: xs => (step P R a x).flatMap (fun b => through P R b xs)

/-- Raw lookup of an existing nonempty syntax path. -/
def lookup (P : UnitSet) (R : List Remapping) (u : String) (p : IdPath) : List Sym :=
  (P.globals R u p.head).flatMap (fun a => through P R a p.tail)

theorem mem_members {P : UnitSet} {i j : DeclId} {x : String} :
    j ∈ members P i x ↔ Member P i x j := by
  unfold members
  cases hd : P.decl? i with
  | none =>
    constructor
    · intro h; cases h
    · intro h; cases h with
      | intro h _ _ _ _ _ _ _ _ => rw [hd] at h; cases h
  | some d =>
    cases hu : P.unit? i.unit with
    | none =>
      constructor
      · intro h; cases h
      · intro h
        have hi : P.decl? i = none := by simp only [UnitSet.decl?, hu, Option.bind_none]
        rw [hi] at hd
        cases hd
    | some s =>
      simp only
      split
      · rename_i hc
        have hm := mem_idxWhere
          (fun e : Decl => e.scope == some d.name && e.name == x && x != "") s.decls []
        simp only [List.length_nil, List.nil_append, Nat.zero_le, true_and] at hm
        constructor
        · intro h
          obtain ⟨k, hk, hj⟩ := List.mem_map.mp h
          have hkf := List.mem_filter.mp hk
          obtain ⟨e, he, hp⟩ := (hm k).mp hkf.1
          have hr : i.idx < k ∧ k ≤ i.idx + memberCount d := of_decide_eq_true hkf.2
          simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hp
          subst hj
          exact .intro hd hc (by simp only [UnitSet.decl?, hu, Option.bind_some]; exact he)
            rfl hp.1.1 hp.1.2 hp.2 hr.1 hr.2
        · intro h
          cases h with
          | @intro child d' e x' hd' hc' he hj hs hn hx hlo hhi =>
            have ed : d = d' := Option.some.inj (hd.symm.trans hd')
            subst ed
            rcases j with ⟨v, k⟩
            simp only at hj
            subst hj
            apply List.mem_map.mpr
            refine ⟨k, List.mem_filter.mpr ⟨(hm k).mpr ⟨e, ?_, ?_⟩, ?_⟩, rfl⟩
            · simpa only [UnitSet.decl?, hu, Option.bind_some] using he
            · simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
              exact ⟨⟨hs, hn⟩, hx⟩
            · exact decide_eq_true ⟨hlo, hhi⟩
      · rename_i hc
        constructor
        · intro h; cases h
        · intro h; cases h with
          | intro hd' hc' _ _ _ _ _ _ _ =>
            cases Option.some.inj (hd.symm.trans hd')
            exact False.elim (hc hc')

theorem mem_step {P : UnitSet} {R : List Remapping} {a b : Sym} {x : String} :
    b ∈ step P R a x ↔ Step P R a x b := by
  cases a with
  | unit u =>
    constructor
    · intro h; exact .unit (globals_sound h)
    · intro h; cases h with
      | unit hs => exact globals_complete hs
  | decl i =>
    constructor
    · intro h
      obtain ⟨j, hj, hb⟩ := List.mem_map.mp h
      subst hb
      exact .decl (mem_members.mp hj)
    · intro h; cases h with
      | decl hm => exact List.mem_map.mpr ⟨_, mem_members.mpr hm, rfl⟩

theorem mem_through {P : UnitSet} {R : List Remapping} {a b : Sym} {xs : List String} :
    b ∈ through P R a xs ↔ Through P R a xs b := by
  induction xs generalizing a with
  | nil =>
    constructor
    · intro h; cases List.mem_singleton.mp h; exact .done _
    · intro h; cases h; exact List.mem_singleton.mpr rfl
  | cons x xs ih =>
    constructor
    · intro h
      obtain ⟨c, hc, hb⟩ := List.mem_flatMap.mp h
      exact .next (mem_step.mp hc) (ih.mp hb)
    · intro h; cases h with
      | next hs ht => exact List.mem_flatMap.mpr ⟨_, mem_step.mpr hs, ih.mpr ht⟩

/-- Soundness and completeness against the independent declarative relation. -/
theorem mem_lookup {P : UnitSet} {R : List Remapping} {u : String} {p : IdPath} {s : Sym} :
    s ∈ lookup P R u p ↔ Qualified P R u p s := by
  constructor
  · intro h
    obtain ⟨a, ha, hs⟩ := List.mem_flatMap.mp h
    exact ⟨a, globals_sound ha, mem_through.mp hs⟩
  · intro ⟨a, ha, hs⟩
    exact List.mem_flatMap.mpr ⟨a, globals_complete ha, mem_through.mpr hs⟩

end Solidity.Frontend.QualifiedUnits
