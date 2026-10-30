import Solidity.Source.Units
import Solidity.Frontend.Static.Closure

/-!
# The import resolver (G12)

Decides G12's relations of `Solidity/Source/Units.lean` over S00 syntax:

- `UnitSet.globals P R u x`: what the file-level name `x` denotes in unit
  `u`, as the leaves (own declarations and namespace imports) of the
  `(unit, name)` nodes reachable through `import "p"` and `{a as b}` edges
  (`Closure.lean`'s saturation).  `globals_sound` and `globals_complete`
  prove it equals `Sees`; so the resolver terminates on import cycles and
  misses no route.
- `UnitSet.unitsOK`: distinct unit names, every import and imported symbol
  found and no clash in any file-level scope, decided exactly (`unitsOK_iff`).
- **Identity**: a resolved declaration identity names a file-level
  declaration of the program (`Sees.decl_exists`); a name reached along two
  routes is one identity, so it is no clash.
- **Against S01**: with any imports, every declaration S01's file-level
  `Env.lookup` finds is in the resolver's answer at its identity
  (`lookup_sub_globals`); in a unit without imports the two are equal
  (`globals_lookup`).  S01's typing reads one unit's `Env`; feeding it the
  resolved cross-unit identities is a handoff (frontend-static.md).

The universe bounding the saturation is `UnitSet.nodes`: the unit names and
import targets, crossed with the queried name and every aliased symbol.
-/

namespace Solidity.Frontend.Static

open Solidity.Source

/-! ## Indices of matching elements -/

/-- The positions (from `k`) of the elements satisfying `p`. -/
def idxWhere {α : Type} (p : α → Bool) : List α → Nat → List Nat
  | [], _ => []
  | a :: l, k => if p a then k :: idxWhere p l (k + 1) else idxWhere p l (k + 1)

theorem idxWhere_filterMap {α : Type} (p : α → Bool) :
    ∀ (l pre : List α), (idxWhere p l pre.length).filterMap (fun i => (pre ++ l)[i]?) = l.filter p
  | [], _ => rfl
  | a :: l, pre => by
    have ih := idxWhere_filterMap p l (pre ++ [a])
    simp only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append] at ih
    have ha : (pre ++ a :: l)[pre.length]? = Option.some a := by
      simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
    by_cases hp : p a = true
    · simp only [idxWhere, hp, if_true, List.filterMap_cons, ha, List.filter_cons, ih]
    · simp only [idxWhere, hp, List.filter_cons, Bool.false_eq_true, if_false]
      exact ih

theorem mem_idxWhere {α : Type} (p : α → Bool) :
    ∀ (l pre : List α) (i : Nat), i ∈ idxWhere p l pre.length ↔
      ∃ a, (pre ++ l)[i]? = Option.some a ∧ pre.length ≤ i ∧ p a = true
  | [], pre, i => by
    simp only [idxWhere, List.not_mem_nil, List.append_nil, false_iff]
    intro ⟨a, h, hle, _⟩
    have : pre.length ≤ i := hle
    rw [List.getElem?_eq_none this] at h
    cases h
  | a :: l, pre, i => by
    have ih := mem_idxWhere p l (pre ++ [a]) i
    simp only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append] at ih
    have ha : (pre ++ a :: l)[pre.length]? = Option.some a := by
      simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
    constructor
    · intro h
      have h' : i ∈ (if p a = true then pre.length :: idxWhere p l (pre.length + 1)
          else idxWhere p l (pre.length + 1)) := h
      split at h'
      · rcases List.mem_cons.mp h' with e | e
        · subst e; exact ⟨a, ha, Nat.le_refl _, by assumption⟩
        · obtain ⟨b, hb, hle, hpb⟩ := ih.mp e
          exact ⟨b, hb, Nat.le_of_succ_le hle, hpb⟩
      · obtain ⟨b, hb, hle, hpb⟩ := ih.mp h'
        exact ⟨b, hb, Nat.le_of_succ_le hle, hpb⟩
    · intro ⟨b, hb, hle, hpb⟩
      show i ∈ (if p a = true then pre.length :: idxWhere p l (pre.length + 1)
          else idxWhere p l (pre.length + 1))
      by_cases e : i = pre.length
      · subst e
        rw [ha] at hb
        cases hb
        simp only [hpb, if_true]
        exact List.mem_cons_self
      · have hlt : pre.length + 1 ≤ i := Nat.lt_of_le_of_ne hle (Ne.symm e)
        have hm := ih.mpr ⟨b, hb, hlt, hpb⟩
        split
        · exact List.mem_cons_of_mem _ hm
        · exact hm

/-! ## The resolver -/

/-- A node of the import graph: a unit and a name in its file-level scope. -/
abbrev Node := String × String

/-- The positions of a unit's own file-level declarations of a name. -/
def ownIdx (s : Syn .unit) (x : String) : List Nat :=
  idxWhere (fun d => d.scope == Option.none && d.name == x && x != "") s.decls 0

/-- The edges out of a node: `import "p"` keeps the name, `{a as x}` renames. -/
def _root_.Solidity.Source.UnitSet.succ (P : UnitSet) (R : List Remapping) (n : Node) : List Node :=
  match P.unit? n.1 with
  | Option.none => []
  | Option.some s => s.imports.filterMap fun i =>
    match i with
    | .all p => Option.some (UnitSet.target R n.1 p, n.2)
    | .sym p a b => if b = n.2 then Option.some (UnitSet.target R n.1 p, a) else Option.none
    | .ns _ _ => Option.none

/-- The symbols a node denotes directly: own declarations and namespaces. -/
def _root_.Solidity.Source.UnitSet.leaves (P : UnitSet) (R : List Remapping) (n : Node) : List Sym :=
  match P.unit? n.1 with
  | Option.none => []
  | Option.some s =>
    (ownIdx s n.2).map (fun i => Sym.decl ⟨n.1, i⟩) ++
      s.imports.filterMap fun i =>
        match i with
        | .ns p b => if b = n.2 then Option.some (Sym.unit (UnitSet.target R n.1 p)) else Option.none
        | _ => Option.none

/-- Unit names that can occur in a node: the program's, the import targets'
and `u`. -/
def _root_.Solidity.Source.UnitSet.unitNames (P : UnitSet) (R : List Remapping) (u : String) : List String :=
  u :: P.units.map Prod.fst ++ P.units.flatMap fun (v, s) => s.imports.map fun i => UnitSet.target R v i.path

/-- Names that can occur in a node: `x` and every aliased symbol. -/
def _root_.Solidity.Source.UnitSet.symNames (P : UnitSet) (x : String) : List String :=
  x :: P.units.flatMap fun (_, s) => s.imports.filterMap fun i =>
    match i with
    | .sym _ a _ => Option.some a
    | _ => Option.none

/-- The universe of the saturation from `(u, x)`. -/
def _root_.Solidity.Source.UnitSet.nodes (P : UnitSet) (R : List Remapping) (u x : String) : List Node :=
  (P.unitNames R u).flatMap fun v => (P.symNames x).map (v, ·)

/-- **The resolver**: everything `x` denotes in `u`'s file-level scope. -/
def _root_.Solidity.Source.UnitSet.globals (P : UnitSet) (R : List Remapping) (u x : String) : List Sym :=
  (reachable (P.succ R) (P.nodes R u x) (u, x)).flatMap (P.leaves R)

/-! ## Correctness -/

theorem _root_.Solidity.Source.UnitSet.unit?_mem {P : UnitSet} {u : String} {s : Syn .unit} (h : P.unit? u = Option.some s) :
    (u, s) ∈ P.units := by
  unfold UnitSet.unit? at h
  cases hf : P.units.find? (·.1 == u) with
  | none => rw [hf] at h; cases h
  | some p =>
    rw [hf] at h
    cases h
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    have e : p.1 = u := by simpa using hp
    cases p
    simp only at e
    subst e
    exact hm

theorem mem_ownIdx {s : Syn .unit} {x : String} {i : Nat} :
    i ∈ ownIdx s x ↔ ∃ d, s.decls[i]? = Option.some d ∧ d.scope = Option.none ∧ d.name = x ∧ x ≠ "" := by
  have h := mem_idxWhere (fun d : Decl => d.scope == Option.none && d.name == x && x != "") s.decls [] i
  simp only [List.length_nil, List.nil_append, Nat.zero_le, true_and] at h
  unfold ownIdx
  rw [h]
  constructor
  · intro ⟨d, hd, hp⟩
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hp
    exact ⟨d, hd, hp.1.1, hp.1.2, hp.2⟩
  · intro ⟨d, hd, h1, h2, h3⟩
    refine ⟨d, hd, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
    exact ⟨⟨h1, h2⟩, h3⟩

theorem mem_succ {P : UnitSet} {R : List Remapping} {n m : Node} :
    m ∈ P.succ R n ↔ ∃ s, P.unit? n.1 = Option.some s ∧
      ((∃ p, Import.all p ∈ s.imports ∧ m = (UnitSet.target R n.1 p, n.2)) ∨
       (∃ p a, Import.sym p a n.2 ∈ s.imports ∧ m = (UnitSet.target R n.1 p, a))) := by
  unfold UnitSet.succ
  cases hu : P.unit? n.1 with
  | none => simp only [List.not_mem_nil, reduceCtorEq, false_and, exists_false]
  | some s =>
    simp only [List.mem_filterMap, Option.some.injEq, exists_eq_left']
    constructor
    · intro ⟨i, hi, hm⟩
      cases i with
      | all p => exact .inl ⟨p, hi, (Option.some.inj hm).symm⟩
      | ns p b => cases hm
      | sym p a b =>
        simp only at hm
        split at hm
        · rename_i e
          subst e
          exact .inr ⟨p, a, hi, (Option.some.inj hm).symm⟩
        · cases hm
    · intro h
      rcases h with ⟨p, hi, e⟩ | ⟨p, a, hi, e⟩
      · exact ⟨.all p, hi, by rw [e]⟩
      · exact ⟨.sym p a n.2, hi, by simp only [if_true, e]⟩

theorem mem_leaves {P : UnitSet} {R : List Remapping} {n : Node} {σ : Sym} :
    σ ∈ P.leaves R n ↔ ∃ s, P.unit? n.1 = Option.some s ∧
      ((∃ i d, σ = .decl ⟨n.1, i⟩ ∧ s.decls[i]? = Option.some d ∧ d.scope = Option.none ∧
          d.name = n.2 ∧ n.2 ≠ "") ∨
       (∃ p, Import.ns p n.2 ∈ s.imports ∧ σ = .unit (UnitSet.target R n.1 p))) := by
  unfold UnitSet.leaves
  cases hu : P.unit? n.1 with
  | none => simp only [List.not_mem_nil, reduceCtorEq, false_and, exists_false]
  | some s =>
    simp only [List.mem_append, List.mem_map, List.mem_filterMap, Option.some.injEq, exists_eq_left']
    constructor
    · intro h
      rcases h with ⟨i, hi, e⟩ | ⟨imp, hi, hm⟩
      · obtain ⟨d, hd, h1, h2, h3⟩ := mem_ownIdx.mp hi
        exact .inl ⟨i, d, e.symm, hd, h1, h2, h3⟩
      · cases imp with
        | all p => cases hm
        | sym p a b => cases hm
        | ns p b =>
          simp only at hm
          split at hm
          · rename_i e
            subst e
            exact .inr ⟨p, hi, (Option.some.inj hm).symm⟩
          · cases hm
    · intro h
      rcases h with ⟨i, d, e, hd, h1, h2, h3⟩ | ⟨p, hi, e⟩
      · exact .inl ⟨i, mem_ownIdx.mpr ⟨d, hd, h1, h2, h3⟩, e.symm⟩
      · exact .inr ⟨.ns p n.2, hi, by simp only [if_true, e]⟩

/-- `Sees` is reachability to a leaf. -/
theorem _root_.Solidity.Source.Sees.reach {P : UnitSet} {R : List Remapping} {u x : String} {σ : Sym}
    (h : Sees P R u x σ) : ∃ n, Reach (P.succ R) (u, x) n ∧ σ ∈ P.leaves R n := by
  induction h with
  | own hu hd hs hn hx =>
    exact ⟨_, .refl _, mem_leaves.mpr ⟨_, hu, .inl ⟨_, _, rfl, hd, hs, hn, hx⟩⟩⟩
  | ns hu hi => exact ⟨_, .refl _, mem_leaves.mpr ⟨_, hu, .inr ⟨_, hi, rfl⟩⟩⟩
  | all hu hi _ ih =>
    obtain ⟨n, hr, hl⟩ := ih
    exact ⟨n, .step (mem_succ.mpr ⟨_, hu, .inl ⟨_, hi, rfl⟩⟩) hr, hl⟩
  | sym hu hi _ ih =>
    obtain ⟨n, hr, hl⟩ := ih
    exact ⟨n, .step (mem_succ.mpr ⟨_, hu, .inr ⟨_, _, hi, rfl⟩⟩) hr, hl⟩

theorem _root_.Solidity.Source.Sees.of_reach {P : UnitSet} {R : List Remapping} {a n : Node} {σ : Sym}
    (h : Reach (P.succ R) a n) (hl : σ ∈ P.leaves R n) : Sees P R a.1 a.2 σ := by
  induction h with
  | refl =>
    obtain ⟨s, hu, h⟩ := mem_leaves.mp hl
    rcases h with ⟨i, d, e, hd, h1, h2, h3⟩ | ⟨p, hi, e⟩
    · rw [e]; exact .own hu hd h1 h2 h3
    · rw [e]; exact .ns hu hi
  | step hb _ ih =>
    obtain ⟨s, hu, h⟩ := mem_succ.mp hb
    rcases h with ⟨p, hi, e⟩ | ⟨p, a', hi, e⟩
    · subst e; exact .all hu hi (ih hl)
    · subst e; exact .sym hu hi (ih hl)

/-- The universe is closed under the edges. -/
theorem _root_.Solidity.Source.UnitSet.nodes_closed (P : UnitSet) (R : List Remapping) (u x : String) :
    ∀ a, a ∈ P.nodes R u x → ∀ b, b ∈ P.succ R a → b ∈ P.nodes R u x := by
  intro a ha b hb
  obtain ⟨s, hu, h⟩ := mem_succ.mp hb
  have hmem := UnitSet.unit?_mem hu
  have ha' := List.mem_flatMap.mp ha
  obtain ⟨v, _, hv⟩ := ha'
  obtain ⟨y, hy, e⟩ := List.mem_map.mp hv
  have hpath : ∀ (i : Import) p, i ∈ s.imports → i.path = p →
      UnitSet.target R a.1 p ∈ P.unitNames R u := by
    intro i p hi hp
    refine List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨(a.1, s), hmem, ?_⟩))
    exact List.mem_map.mpr ⟨i, hi, by rw [hp]⟩
  rcases h with ⟨p, hi, eb⟩ | ⟨p, a', hi, eb⟩
  · subst eb
    refine List.mem_flatMap.mpr ⟨_, hpath _ p hi rfl, List.mem_map.mpr ⟨a.2, ?_, rfl⟩⟩
    rw [← e]; exact hy
  · subst eb
    refine List.mem_flatMap.mpr ⟨_, hpath _ p hi rfl, List.mem_map.mpr ⟨a', ?_, rfl⟩⟩
    refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨(a.1, s), hmem, ?_⟩)
    exact List.mem_filterMap.mpr ⟨_, hi, rfl⟩

theorem _root_.Solidity.Source.UnitSet.start_mem (P : UnitSet) (R : List Remapping) (u x : String) :
    (u, x) ∈ P.nodes R u x :=
  List.mem_flatMap.mpr ⟨u, List.mem_cons_self, List.mem_map.mpr ⟨x, List.mem_cons_self, rfl⟩⟩

/-- **Sound**: everything the resolver returns is in the file-level scope. -/
theorem globals_sound {P : UnitSet} {R : List Remapping} {u x : String} {σ : Sym}
    (h : σ ∈ P.globals R u x) : Sees P R u x σ := by
  obtain ⟨n, hn, hl⟩ := List.mem_flatMap.mp h
  have hr := (mem_reachable (P.nodes_closed R u x) (P.start_mem R u x)).mp hn
  exact Sees.of_reach hr hl

/-- **Complete**: the resolver returns everything in the file-level scope,
through import cycles and every route. -/
theorem globals_complete {P : UnitSet} {R : List Remapping} {u x : String} {σ : Sym}
    (h : Sees P R u x σ) : σ ∈ P.globals R u x := by
  obtain ⟨n, hr, hl⟩ := h.reach
  exact List.mem_flatMap.mpr
    ⟨n, (mem_reachable (P.nodes_closed R u x) (P.start_mem R u x)).mpr hr, hl⟩

theorem mem_globals {P : UnitSet} {R : List Remapping} {u x : String} {σ : Sym} :
    σ ∈ P.globals R u x ↔ Sees P R u x σ := ⟨globals_sound, globals_complete⟩

/-! ## Identity -/

/-- **Declaration identity**: a declaration a file-level name denotes,
along any route, is a file-level declaration of the program at that
identity. -/
theorem _root_.Solidity.Source.Sees.decl_exists {P : UnitSet} {R : List Remapping} {u x : String} {i : DeclId}
    (h : Sees P R u x (.decl i)) : ∃ d, P.decl? i = Option.some d ∧ d.scope = Option.none := by
  generalize e : Sym.decl i = σ at h
  induction h with
  | own hu hd hs _ _ =>
    cases e
    exact ⟨_, by simp only [UnitSet.decl?, hu, Option.bind_some, hd], hs⟩
  | ns _ _ => cases e
  | all _ _ _ ih => exact ih e
  | sym _ _ _ ih => exact ih e

/-- A unit's scope names only units of the program and their names. -/
theorem _root_.Solidity.Source.Sees.unit_mem {P : UnitSet} {R : List Remapping} {u x : String} {σ : Sym}
    (h : Sees P R u x σ) : ∃ s, P.unit? u = Option.some s := by
  cases h <;> exact ⟨_, by assumption⟩

/-! ## Against S01's lookup -/

/-- **Agreement with S01**: in a unit without imports, the declarations the
resolver returns are exactly S01's file-level `Env.lookup`. -/
theorem globals_lookup {P : UnitSet} {R : List Remapping} {u x : String} {s : Syn .unit}
    (hu : P.unit? u = Option.some s) (hi : s.imports = []) :
    (P.globals R u x).filterMap (fun σ => match σ with
      | .decl i => P.decl? i
      | .unit _ => Option.none) = (Syn.env s).lookup Option.none x := by
  have hc : Closed (P.succ R) [(u, x)] := by
    intro a ha b hb
    have e : a = (u, x) := List.mem_singleton.mp ha
    subst e
    obtain ⟨s', hu', h⟩ := mem_succ.mp hb
    rw [hu] at hu'
    cases hu'
    rcases h with ⟨_, him, _⟩ | ⟨_, _, him, _⟩ <;> (rw [hi] at him; cases him)
  have hr : reachable (P.succ R) (P.nodes R u x) (u, x) = [(u, x)] := iter_closed hc _
  have hl : P.leaves R (u, x) = (ownIdx s x).map (fun i => Sym.decl ⟨u, i⟩) := by
    simp only [UnitSet.leaves, hu, hi, List.filterMap_nil, List.append_nil]
  simp only [UnitSet.globals, hr, List.flatMap_cons, List.flatMap_nil, List.append_nil, hl,
    List.filterMap_map]
  have hf := idxWhere_filterMap (fun d : Decl => d.scope == Option.none && d.name == x && x != "")
    s.decls []
  simp only [List.length_nil, List.nil_append] at hf
  have e : (fun i => match Sym.decl ⟨u, i⟩ with
      | .decl i => P.decl? i
      | .unit _ => Option.none) = fun i => s.decls[i]? := by
    funext i
    simp only [UnitSet.decl?, hu, Option.bind_some]
  simp only [Function.comp_def]
  rw [e]
  unfold ownIdx
  rw [hf]
  rfl

/-! ## The program check -/

/-- Every name a unit's scope can contain: declared and aliased names. -/
def _root_.Solidity.Source.UnitSet.allNames (P : UnitSet) : List String :=
  P.units.flatMap fun (_, s) => s.decls.map Decl.name ++ s.imports.filterMap fun i =>
    match i with
    | .all _ => Option.none
    | .ns _ b => Option.some b
    | .sym _ _ b => Option.some b

theorem _root_.Solidity.Source.Sees.name_mem {P : UnitSet} {R : List Remapping} {u x : String} {σ : Sym}
    (h : Sees P R u x σ) : x ∈ P.allNames := by
  induction h with
  | own hu hd _ hn _ =>
    refine List.mem_flatMap.mpr ⟨_, UnitSet.unit?_mem hu, List.mem_append_left _ ?_⟩
    exact List.mem_map.mpr ⟨_, List.mem_of_getElem? hd, hn⟩
  | ns hu hi =>
    exact List.mem_flatMap.mpr ⟨_, UnitSet.unit?_mem hu,
      List.mem_append_right _ (List.mem_filterMap.mpr ⟨_, hi, rfl⟩)⟩
  | all _ _ _ ih => exact ih
  | sym hu hi _ _ =>
    exact List.mem_flatMap.mpr ⟨_, UnitSet.unit?_mem hu,
      List.mem_append_right _ (List.mem_filterMap.mpr ⟨_, hi, rfl⟩)⟩

/-- Whether two symbols may share a name: overloadable declarations of one
kind. -/
def _root_.Solidity.Source.UnitSet.compatible (P : UnitSet) : Sym → Sym → Bool
  | .decl i, .decl i' =>
    match P.decl? i, P.decl? i' with
    | Option.some d, Option.some d' => d.kind == d'.kind && d.kind.overloads
    | _, _ => false
  | _, _ => false

/-- No two different symbols of a list clash. -/
def _root_.Solidity.Source.UnitSet.noClash (P : UnitSet) (L : List Sym) : Bool :=
  L.all fun σ => L.all fun σ' => σ == σ' || P.compatible σ σ'

/-- Duplicate-freedom, decided. -/
def nodupB : List String → Bool
  | [] => true
  | a :: l => !l.contains a && nodupB l

theorem nodupB_iff : ∀ l : List String, nodupB l = true ↔ l.Nodup
  | [] => by simp only [nodupB, List.nodup_nil]
  | a :: l => by
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not, List.nodup_cons, nodupB_iff l]

/-- Whether an import's symbol (if any) is found. -/
def _root_.Solidity.Source.UnitSet.symFound (P : UnitSet) (R : List Remapping) (u : String) :
    Import → Bool
  | .sym p a _ => !(P.globals R (UnitSet.target R u p) a).isEmpty
  | _ => true

/-- **The program check**: distinct unit names, every import and imported
symbol found, no clash in any unit's file-level scope. -/
def _root_.Solidity.Source.UnitSet.unitsOK (P : UnitSet) (R : List Remapping) : Bool :=
  nodupB (P.units.map Prod.fst) &&
  P.units.all (fun (u, s) => s.imports.all fun i => (P.unit? (UnitSet.target R u i.path)).isSome) &&
  P.units.all (fun (u, s) => s.imports.all (P.symFound R u)) &&
  P.units.all (fun (u, _) => P.allNames.all fun x => P.noClash (P.globals R u x))

theorem compatible_spec {P : UnitSet} {σ σ' : Sym} (h : P.compatible σ σ' = true) :
    ∃ i i' d d', σ = .decl i ∧ σ' = .decl i' ∧ P.decl? i = Option.some d ∧
      P.decl? i' = Option.some d' ∧ d.kind = d'.kind ∧ d.kind.overloads = true := by
  cases σ with
  | unit _ => cases h
  | decl i =>
    cases σ' with
    | unit _ => cases h
    | decl i' =>
      simp only [UnitSet.compatible] at h
      split at h
      · rename_i d d' hd hd'
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        exact ⟨i, i', d, d', rfl, rfl, hd, hd', h.1, h.2⟩
      · cases h

theorem symFound_iff {P : UnitSet} {R : List Remapping} {u : String} {s : Syn .unit} :
    (∀ i, i ∈ s.imports → P.symFound R u i = true) ↔
      ∀ p a b, Import.sym p a b ∈ s.imports → ∃ σ, Sees P R (UnitSet.target R u p) a σ := by
  constructor
  · intro h p a b hi
    have hf := h _ hi
    simp only [UnitSet.symFound, Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem] at hf
    obtain ⟨σ, hσ⟩ := hf
    exact ⟨σ, globals_sound hσ⟩
  · intro h i hi
    cases i with
    | sym p a b =>
      obtain ⟨σ, hσ⟩ := h p a b hi
      simp only [UnitSet.symFound, Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem]
      exact ⟨σ, globals_complete hσ⟩
    | all _ => rfl
    | ns _ _ => rfl

/-- **The check decides G12's judgment.** -/
theorem unitsOK_iff {P : UnitSet} {R : List Remapping} : P.unitsOK R = true ↔ UnitsOK P R := by
  simp only [UnitSet.unitsOK, Bool.and_eq_true, List.all_eq_true, nodupB_iff, Option.isSome_iff_exists]
  constructor
  · intro ⟨⟨⟨hd, hi⟩, hy⟩, hs⟩
    refine ⟨hd, fun u s hm i hi' => hi (u, s) hm i hi',
      fun u s hm => symFound_iff.mp (hy (u, s) hm), ?_⟩
    intro u x σ σ' h h' hne
    obtain ⟨s, hu⟩ := h.unit_mem
    have hc := hs (u, s) (UnitSet.unit?_mem hu) x h.name_mem
    simp only [UnitSet.noClash, List.all_eq_true] at hc
    have hb := hc σ (globals_complete h) σ' (globals_complete h')
    simp only [Bool.or_eq_true, beq_iff_eq] at hb
    rcases hb with e | o
    · exact absurd e hne
    · exact compatible_spec o
  · intro ⟨hd, hi, hy, hs⟩
    refine ⟨⟨⟨hd, fun p hm i hi' => hi p.1 p.2 hm i hi'⟩,
      fun p hm => symFound_iff.mpr (hy p.1 p.2 hm)⟩, ?_⟩
    intro p _ x _
    simp only [UnitSet.noClash, List.all_eq_true, Bool.or_eq_true, beq_iff_eq]
    intro σ hσ σ' hσ'
    by_cases e : σ = σ'
    · exact .inl e
    · obtain ⟨i, i', d, d', e1, e2, h1, h2, ek, o⟩ :=
        hs _ _ _ _ (globals_sound hσ) (globals_sound hσ') e
      subst e1 e2
      right
      simp only [UnitSet.compatible, h1, h2, ek, beq_self_eq_true, Bool.true_and]
      rw [← ek]; exact o

/-- **Conservative over S01**: with any imports, every declaration S01's
file-level lookup finds in a unit is in the resolver's answer, at its own
identity. -/
theorem lookup_sub_globals {P : UnitSet} {R : List Remapping} {u x : String} {s : Syn .unit}
    (hu : P.unit? u = Option.some s) {d : Decl} (hd : d ∈ (Syn.env s).lookup Option.none x) :
    ∃ i, s.decls[i]? = Option.some d ∧ Sym.decl ⟨u, i⟩ ∈ P.globals R u x := by
  have hd' : d ∈ s.decls.filter fun d => d.scope == Option.none && d.name == x && x != "" := hd
  obtain ⟨hm, hp⟩ := List.mem_filter.mp hd'
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hp
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  exact ⟨i, hi, globals_complete (.own hu hi hp.1.1 hp.1.2 hp.2)⟩

end Solidity.Frontend.Static
