import Solidity.Source.Overloads

/-!
# Overload sets across bases and overload selection (G12)

Decides `Solidity/Source/Overloads.lean`'s `InheritedFn`:
`Env.inheritedFns E c x` walks `c`'s linearization, most derived first, and
keeps each visible function named `x` unless an earlier scope has one with
its parameter types (`mem_inheritedFns`).  It extends S01's lookup: the
functions S01's `Env.lookup` finds in the first declaring scope are all in
it (`lookup_sub_inheritedFns`).

`selectOverload` is solc's overload resolution of a call: the overloads
whose parameters accept the argument types; the call resolves only when
exactly one does (`selectOverload_unique`), as S01's `Typed.callInternal`
requires of its own candidate list.  Two accepting overloads are refused
("No unique declaration found after argument-dependent lookup").
-/

namespace Solidity.Frontend.Static

open Solidity.Source

/-- The walk: `seen` are the functions of the scopes already passed. -/
def inheritedGo (E : Env) (c x : String) : List String → List Decl → List Decl
  | [], _ => []
  | b :: bs, seen =>
    (E.visibleFns c b x).filter (fun d => seen.all fun d' => !d'.sameParams E d) ++
      inheritedGo E c x bs (seen ++ E.visibleFns c b x)

/-- **The inherited overload set** of `x` in contract `c`. -/
def _root_.Solidity.Source.Env.inheritedFns (E : Env) (c x : String) : List Decl :=
  inheritedGo E c x (E.chain c) []

theorem mem_inheritedGo (E : Env) (c x : String) (d : Decl) :
    ∀ (L : List String) (seen : List Decl), d ∈ inheritedGo E c x L seen ↔
      ∃ pre b post, L = pre ++ b :: post ∧ d ∈ E.visibleFns c b x ∧
        ∀ d', d' ∈ seen ++ pre.flatMap (E.visibleFns c · x) → d'.sameParams E d = false
  | [], seen => by
    simp only [inheritedGo, List.not_mem_nil, false_iff]
    intro ⟨pre, b, post, e, _⟩
    cases pre <;> cases e
  | b :: bs, seen => by
    show d ∈ (E.visibleFns c b x).filter _ ++ inheritedGo E c x bs (seen ++ E.visibleFns c b x) ↔ _
    rw [List.mem_append, List.mem_filter, List.all_eq_true, mem_inheritedGo E c x d bs]
    constructor
    · intro h
      rcases h with ⟨hd, hs⟩ | ⟨pre, b', post, e, hd, hs⟩
      · refine ⟨[], b, bs, rfl, hd, fun d' hd' => ?_⟩
        simp only [List.flatMap_nil, List.append_nil] at hd'
        have := hs d' hd'
        simpa only [Bool.not_eq_true'] using this
      · refine ⟨b :: pre, b', post, by rw [e]; rfl, hd, ?_⟩
        intro d' hd'
        apply hs d'
        simpa only [List.flatMap_cons, List.append_assoc] using hd'
    · intro ⟨pre, b', post, e, hd, hs⟩
      cases pre with
      | nil =>
        cases e
        left
        refine ⟨hd, fun d' hd' => ?_⟩
        have := hs d' (by simp only [List.flatMap_nil, List.append_nil]; exact hd')
        simp only [this, Bool.not_false]
      | cons b'' pre =>
        cases e
        right
        refine ⟨pre, b', post, rfl, hd, fun d' hd' => hs d' ?_⟩
        simpa only [List.flatMap_cons, List.append_assoc] using hd'

/-- **The checker decides the relation.** -/
theorem mem_inheritedFns {E : Env} {c x : String} {d : Decl} :
    d ∈ E.inheritedFns c x ↔ InheritedFn E c x d := by
  unfold Env.inheritedFns InheritedFn
  rw [mem_inheritedGo E c x d]
  constructor
  · intro ⟨pre, b, post, e, hd, hs⟩
    refine ⟨pre, b, post, e, hd, fun b' hb' d' hd' => hs d' ?_⟩
    simp only [List.nil_append]
    exact List.mem_flatMap.mpr ⟨b', hb', hd'⟩
  · intro ⟨pre, b, post, e, hd, hs⟩
    refine ⟨pre, b, post, e, hd, fun d' hd' => ?_⟩
    simp only [List.nil_append] at hd'
    obtain ⟨b', hb', hd''⟩ := List.mem_flatMap.mp hd'
    exact hs b' hb' d' hd''

/-- The first scope's functions are never hidden. -/
theorem first_sub_inheritedFns {E : Env} {c x b : String} {post : List String}
    (h : E.chain c = b :: post) : ∀ d, d ∈ E.visibleFns c b x → d ∈ E.inheritedFns c x := by
  intro d hd
  exact mem_inheritedFns.mpr ⟨[], b, post, by rw [h]; rfl, hd, fun _ hb' => nomatch hb'⟩

/-- **Extends S01's lookup**: every function S01's `Env.lookup` finds in a
contract scope of `c`'s linearization, callable from `c`, is in the
inherited overload set. -/
theorem lookup_sub_inheritedFns {E : Env} {c x : String} {d : Decl}
    (hd : d ∈ E.lookup (Option.some c) x) (hf : d.kind = .function)
    (hc : d.callableFrom (Option.some c) = true) (hs : d.scope ≠ Option.none) :
    d ∈ E.inheritedFns c x := by
  unfold Env.lookup at hd
  simp only at hd
  split at hd
  · rename_i s hfind
    obtain ⟨_, as, bs, e, hpre⟩ := List.find?_eq_some_iff_append.mp hfind
    obtain ⟨as', rest, e1, e2, e3⟩ := List.map_eq_append_iff.mp e
    obtain ⟨b, post, e4, e5, _⟩ := List.map_eq_cons_iff.mp e3
    subst e4 e5
    refine mem_inheritedFns.mpr ⟨as', b, post, e1, ?_, ?_⟩
    · exact List.mem_filter.mpr ⟨hd, by simp only [hf, hc, beq_self_eq_true, Bool.and_self]⟩
    · intro b' hb' d' hd'
      have hv := hpre (Option.some b') (by rw [← e2]; exact List.mem_map_of_mem hb')
      simp only [Bool.not_eq_true', Bool.not_eq_false', List.isEmpty_iff] at hv
      simp only [Env.visibleFns, hv, List.filter_nil, List.not_mem_nil] at hd'
  · have hm : d ∈ E.decls.filter fun d => d.scope == Option.none && d.name == x && x != "" := hd
    have := (List.mem_filter.mp hm).2
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact absurd this.1.1 hs

/-- The parameter types of a function, if they elaborate. -/
def paramsOf (E : Env) (d : Decl) : Option (List STy) := (d.fnSig E).map Prod.fst

/-- Whether a function's parameters accept the argument types. -/
def accepts (E : Env) (isBase : DeclName → DeclName → Bool) (σs : List STy) (d : Decl) : Bool :=
  match paramsOf E d with
  | Option.some ps => argsFit isBase σs ps
  | Option.none => false

/-- **Overload selection**: the candidates whose parameters accept the
argument types; resolved when exactly one does. -/
def selectOverload (E : Env) (isBase : DeclName → DeclName → Bool) (cands : List Decl)
    (σs : List STy) : Option Decl :=
  match cands.filter (accepts E isBase σs) with
  | [d] => Option.some d
  | _ => Option.none

theorem selectOverload_unique {E : Env} {isBase : DeclName → DeclName → Bool} {cands : List Decl}
    {σs : List STy} {d : Decl} (h : selectOverload E isBase cands σs = Option.some d) :
    d ∈ cands ∧ ∀ d', d' ∈ cands → accepts E isBase σs d' = true → d' = d := by
  unfold selectOverload at h
  split at h
  · rename_i d₀ hf
    cases h
    have hm : d ∈ cands.filter (accepts E isBase σs) := by rw [hf]; exact List.mem_singleton.mpr rfl
    refine ⟨(List.mem_filter.mp hm).1, fun d' hd' hfit => ?_⟩
    have : d' ∈ cands.filter (accepts E isBase σs) := List.mem_filter.mpr ⟨hd', hfit⟩
    rw [hf] at this
    exact List.mem_singleton.mp this
  · cases h

end Solidity.Frontend.Static
