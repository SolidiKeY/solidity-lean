import Solidity.Typing.Values

/-!
# The leaves of a type, and the expansions they give

A value of a *finite shape* (`Ty.Finite`, its test `Ty.finiteShape`: words,
members, fixed-size arrays of finite shape, mappings left as they are, no
dynamic array) is the words at its primitive leaves (`Ty.leaves`): the
paths through members and in-range fixed indices that end at a word.  So a
`delete` there, and a copy `a = b`, is one word written per leaf:

* in the interpreter, at every shape with a leaf, with no premise on the
  storage (`Storage.delete_expand`, `Storage.write_expand`,
  `Storage.write_find_expand`): the storage a delete leaves is the one the
  writes of the leaves' defaults leave, and a copy's is the one the writes of
  the source's leaves, read before the copy, leave;
* in the Theory (`Obs.delAt_expand`, `Obs.copyTo_find_expand`), where a value
  is its observations: provided the locations are shaped as the typed
  storage shapes them (`TVal.Shaped`, true of every typed value,
  `SVal.obs_shaped`): a delete keeps whether a location is there, which a
  word written makes true, and resets the words past a fixed array's end,
  which no leaf reaches.

**Why the leaves skip mappings.**  `delete` and a copy keep a mapping as it
is (`SVal.defaultOf`, `SVal.overlay`), so its entries are no leaf of
anything; a dynamic array is not of finite shape, since a delete truncates
it, which no word written expresses.

**Why `T.leaves ≠ []` in the interpreter.**  A delete saves at its location
even where nothing is below it to reset (a `uint[0]`, a struct of mappings):
through a mapping's default that save adds the key's entry, which reads as
the default (the Theory cannot tell, `Obs` has no entries) but is another
typed value.  With one leaf, the leaf's write adds the same entry.

**Push and pop of a word** (`Obs.push_prim`, `Obs.pop_prim`,
`Storage.push_prim`, `Storage.pop_prim`): a push is one more live slot,
then a save at index `len`; a pop of a word is the slot at `len - 1`
deleted, then the length shrunk keeping it.

The leaves are computed by fuel over a rank bound, as `SVal.dflt` is
(`Semantics/Storage.lean`); a fixed array's length is part of its type, so a
`uint[2^200]` has that many leaves: a user of the expansion bounds
`Ty.leafCount`.
-/

namespace Solidity

open Semantics (structDef lookupBy setBy tyRank fieldsRank structRank nodupKeysB)

/-! ## Finite shapes -/

/-- A type whose values are their words: no dynamic array outside a
mapping, a fixed array addressable at every index (`n ≤ 2^256`). -/
inductive Ty.Finite : Ty → Prop where
  | prim (P : PrimTy) : Ty.Finite (.prim P)
  | mapping (K : PrimTy) (V : Ty) : Ty.Finite (.ref (.mapping K V))
  | struct (s : Name)
      (h : ∀ (f : Name) (T : Ty), lookupBy f (structDef s) = some T → Ty.Finite T) :
      Ty.Finite (.ref (.struct s))
  | fixed (E : Ty) (n : Nat) (hn : n ≤ 2 ^ 256) (h : Ty.Finite E) :
      Ty.Finite (.ref (.fixed E n))

/-- `Ty.Finite`'s test, by fuel. -/
def Ty.finiteShapeAt : Nat → Ty → Bool
  | 0, _ => false
  | _ + 1, .prim _ => true
  | k + 1, .ref (.struct s) => (structDef s).all fun fT => Ty.finiteShapeAt k fT.2
  | k + 1, .ref (.fixed E n) => decide (n ≤ 2 ^ 256) && Ty.finiteShapeAt k E
  | _ + 1, .ref (.array _) => false
  | _ + 1, .ref (.mapping _ _) => true

/-- **A finite shape**: the values of `T` are their words at the leaves. -/
def Ty.finiteShape (T : Ty) : Bool := Ty.finiteShapeAt (rankBound T + 1) T

theorem Ty.finite_of_finiteShapeAt : (k : Nat) → (T : Ty) → Ty.finiteShapeAt k T = true →
    T.Finite
  | 0, _, h => by simp only [Ty.finiteShapeAt, Bool.false_eq_true] at h
  | _ + 1, .prim P, _ => .prim P
  | k + 1, .ref (.struct s), h => by
    simp only [Ty.finiteShapeAt, List.all_eq_true] at h
    exact .struct s fun f T hf =>
      Ty.finite_of_finiteShapeAt k T (h (f, T) (Semantics.lookupBy_eq_some_mem hf))
  | k + 1, .ref (.fixed E n), h => by
    simp only [Ty.finiteShapeAt, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .fixed E n h.1 (Ty.finite_of_finiteShapeAt k E h.2)
  | _ + 1, .ref (.array _), h => by simp only [Ty.finiteShapeAt, Bool.false_eq_true] at h
  | _ + 1, .ref (.mapping K V), _ => .mapping K V

theorem Ty.finite_of_finiteShape {T : Ty} (h : T.finiteShape = true) : T.Finite :=
  Ty.finite_of_finiteShapeAt _ T h

/-! ## Leaves -/

/-- A word below a `T`: its type and its path. -/
abbrev Leaf (T : Ty) := (P : PrimTy) × Path T (.prim P)

/-- A member's leaf, below the struct. -/
def Leaf.field {s f : Name} {T : Ty} (h : lookupBy f (structDef s) = some T) (l : Leaf T) :
    Leaf (.ref (.struct s)) := ⟨l.1, .field h l.2⟩

/-- An element's leaf, below the fixed array. -/
def Leaf.atF {E : Ty} {n : Nat} (i : PrimTy.uint.Denote) (l : Leaf E) :
    Leaf (.ref (.fixed E n)) := ⟨l.1, .atF i l.2⟩

/-- A member of a list with distinct keys is what the list looks it up as. -/
theorem lookupBy_of_mem_nodup {k : Name} {v : Ty} :
    {l : List (Name × Ty)} → nodupKeysB l = true → (k, v) ∈ l → lookupBy k l = some v
  | [], _, hm => absurd hm List.not_mem_nil
  | (k', v') :: l, hn, hm => by
    simp only [nodupKeysB, Bool.and_eq_true, Option.isNone_iff_eq_none] at hn
    rcases List.mem_cons.mp hm with e | hm'
    · cases e; simp only [lookupBy, ↓reduceIte]
    · have hk : k ≠ k' := fun e => by
        subst e; rw [lookupBy_of_mem_nodup hn.2 hm'] at hn; exact Option.noConfusion hn.1
      simp only [lookupBy, hk, ↓reduceIte]
      exact lookupBy_of_mem_nodup hn.2 hm'

/-- The leaves of `T` with fuel `k`: a word's own, each member's below it,
each element's below it; none below a mapping or a dynamic array. -/
def Ty.leavesAt : Nat → (T : Ty) → List (Leaf T)
  | 0, _ => []
  | _ + 1, .prim P => [⟨P, .nil⟩]
  | k + 1, .ref (.struct s) =>
    (structDef s).attach.flatMap fun fT =>
      (Ty.leavesAt k fT.1.2).map (Leaf.field (lookupBy_of_mem_nodup (structDef_nodup s) fT.2))
  | k + 1, .ref (.fixed E _n) =>
    (List.range _n).flatMap fun i => (Ty.leavesAt k E).map (Leaf.atF (uintOfNat i))
  | _ + 1, .ref (.array _) => []
  | _ + 1, .ref (.mapping _ _) => []

/-- **The leaves of `T`**: its words, by members and in-range fixed indices,
in the members' and the indices' order. -/
def Ty.leaves (T : Ty) : List (Leaf T) := Ty.leavesAt (rankBound T + 1) T

/-- How many words a `T` is. -/
def Ty.leafCount (T : Ty) : Nat := T.leaves.length

/-! ## Direct paths -/

namespace Path

/-- A path through members and fixed indices only: no mapping key, no
dynamic index. -/
def direct : {T U : Ty} → Path T U → Bool
  | _, _, .nil => true
  | _, _, .field _ p => p.direct
  | _, _, .atF _ p => p.direct
  | _, _, .at _ _ => false
  | _, _, .key _ _ => false

/-- A path that goes past a fixed array's end before any key or dynamic
index: nothing is there. -/
def out : {T U : Ty} → Path T U → Bool
  | _, _, .nil => false
  | _, _, .field _ p => p.out
  | _, _, @Path.atF _ _ n i p => decide (n ≤ i.1.toNat) || p.out
  | _, _, .at _ _ => false
  | _, _, .key _ _ => false

end Path

/-- A `uint` is the `uintOfNat` of its value. -/
theorem uintOfNat_toNat (i : PrimTy.uint.Denote) : uintOfNat i.1.toNat = i := by
  have hi : 0 ≤ i.1 ∧ i.1 < ((2 ^ 256 : Nat) : Int) := by
    have h := i.2
    simp only [PrimTy.inRange, decide_eq_true_eq] at h
    exact h
  have hlt : i.1.toNat < 2 ^ 256 := by omega
  rw [uintOfNat_eq_lenU hlt]
  apply Subtype.ext
  show ((i.1.toNat : Nat) : Int) = i.1
  omega

/-- An index below a length is below it as a `uint` too. -/
theorem uintOfNat_toNat_lt {i n : Nat} (h : i < n) : (uintOfNat i).1.toNat < n := by
  by_cases hb : i < 2 ^ 256
  · rw [uintOfNat_val hb]; simp only [Int.toNat_natCast]; exact h
  · simp only [uintOfNat, hb, dite_false]
    show (0 : Int).toNat < n
    omega

/-- A member's type is of a rank below its struct's. -/
theorem tyRank_lt_of_lookup {s f : Name} {T : Ty} (h : lookupBy f (structDef s) = some T) :
    tyRank T < structRank s := by
  have hm := Semantics.lookupBy_eq_some_mem h
  have hle : ∀ (l : List (Name × Ty)), (f, T) ∈ l → tyRank T ≤ fieldsRank l := by
    intro l
    induction l with
    | nil => intro hm; exact absurd hm List.not_mem_nil
    | cons hd tl ih =>
      intro hm
      simp only [fieldsRank]
      rcases List.mem_cons.mp hm with e | hm'
      · subst e; exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hm') (Nat.le_max_right _ _)
  exact Nat.lt_of_le_of_lt (hle _ hm) (Semantics.structDef_rank_lt s)

/-- Every leaf is a direct path inside the value. -/
theorem Ty.leavesAt_direct : (k : Nat) → (T : Ty) → ∀ l ∈ Ty.leavesAt k T,
    l.2.direct = true ∧ l.2.out = false
  | 0, _, l, hl => absurd hl List.not_mem_nil
  | _ + 1, .prim P, l, hl => by
    simp only [Ty.leavesAt, List.mem_singleton] at hl
    subst hl; exact ⟨rfl, rfl⟩
  | k + 1, .ref (.struct s), l, hl => by
    simp only [Ty.leavesAt, List.mem_flatMap, List.mem_map] at hl
    obtain ⟨_, _, l', hl', rfl⟩ := hl
    exact Ty.leavesAt_direct k _ l' hl'
  | k + 1, .ref (.fixed E n), l, hl => by
    simp only [Ty.leavesAt, List.mem_flatMap, List.mem_range, List.mem_map] at hl
    obtain ⟨i, hi, l', hl', rfl⟩ := hl
    obtain ⟨h1, h2⟩ := Ty.leavesAt_direct k E l' hl'
    refine ⟨h1, ?_⟩
    simp only [Leaf.atF, Path.out, h2, Bool.or_false, decide_eq_false_iff_not, Nat.not_le]
    exact uintOfNat_toNat_lt hi
  | _ + 1, .ref (.array _), l, hl => absurd hl List.not_mem_nil
  | _ + 1, .ref (.mapping _ _), l, hl => absurd hl List.not_mem_nil

/-- Every direct path to a word inside the value is a leaf, given the fuel. -/
theorem Ty.mem_leavesAt_of_direct {P : PrimTy} : {T : Ty} → (r : Path T (.prim P)) →
    (k : Nat) → tyRank T < k → r.direct = true → r.out = false →
    (⟨P, r⟩ : Leaf T) ∈ Ty.leavesAt k T
  | _, .nil, 0, hk, _, _ => absurd hk (Nat.not_lt_zero _)
  | _, .nil, _ + 1, _, _, _ => by simp only [Ty.leavesAt, List.mem_singleton]
  | _, .field h p, 0, hk, _, _ => absurd hk (Nat.not_lt_zero _)
  | _, @Path.field s f T _ h p, k + 1, hk, hd, ho => by
    simp only [tyRank] at hk
    have hk' : tyRank T < k := Nat.lt_of_lt_of_le (tyRank_lt_of_lookup h) (Nat.le_of_lt_succ hk)
    have ih := Ty.mem_leavesAt_of_direct p k hk' hd ho
    simp only [Ty.leavesAt, List.mem_flatMap, List.mem_map]
    exact ⟨⟨(f, T), Semantics.lookupBy_eq_some_mem h⟩, List.mem_attach _ _, ⟨P, p⟩, ih, rfl⟩
  | _, .atF i p, 0, hk, _, _ => absurd hk (Nat.not_lt_zero _)
  | _, @Path.atF E _ n i p, k + 1, hk, hd, ho => by
    simp only [tyRank] at hk
    simp only [Path.out, Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_le] at ho
    simp only [Path.direct] at hd
    have ih := Ty.mem_leavesAt_of_direct p k (by omega) hd ho.2
    simp only [Ty.leavesAt, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨i.1.toNat, ho.1, ⟨P, p⟩, ih, by rw [uintOfNat_toNat]; rfl⟩
  | _, .at _ _, _, _, hd, _ => by simp only [Path.direct, Bool.false_eq_true] at hd
  | _, .key _ _, _, _, hd, _ => by simp only [Path.direct, Bool.false_eq_true] at hd

/-- **The leaves are the direct paths to a word that stay inside the value.** -/
theorem Ty.mem_leaves {T : Ty} {P : PrimTy} (r : Path T (.prim P)) :
    (⟨P, r⟩ : Leaf T) ∈ T.leaves ↔ r.direct = true ∧ r.out = false :=
  ⟨fun h => Ty.leavesAt_direct _ T _ h,
   fun h => Ty.mem_leavesAt_of_direct r _
     (Nat.lt_succ_of_le (tyRank_le_rankBound T)) h.1 h.2⟩

/-! ## Distinct leaves are disjoint -/

/-- Nothing goes on below a word: a path that goes through a word's path is
that path. -/
theorem Path.eq_of_strip?_prim {T V : Ty} {P : PrimTy} (l : Path T (.prim P)) (r : Path T V)
    {s : Path (.prim P) V} (h : Path.strip? l r = some s) :
    (⟨V, r⟩ : (V : Ty) × Path T V) = ⟨.prim P, l⟩ := by
  have e := Path.eq_of_strip? l r h
  cases s with
  | nil => subst e; rw [Path.append_nil_right]

/-- A word's path, past itself. -/
theorem Path.strip?_self {T U : Ty} (p : Path T U) : Path.strip? p p = some .nil := by
  have e := Path.strip?_append p .nil
  rwa [Path.append_nil_right] at e

/-- **Distinct leaves are disjoint**: neither goes through the other. -/
theorem Leaf.strip?_ne {T : Ty} {l l' : Leaf T} (h : l ≠ l') :
    Path.strip? l.2 l'.2 = none := by
  cases hs : Path.strip? l.2 l'.2 with
  | none => rfl
  | some s =>
    have e := Path.eq_of_strip?_prim l.2 l'.2 hs
    obtain ⟨P, l⟩ := l
    obtain ⟨P', l'⟩ := l'
    simp only [Sigma.mk.injEq, Ty.prim.injEq] at e
    obtain ⟨rfl, e⟩ := e
    exact absurd (by rw [eq_of_heq e]) h

theorem Ty.leaves_strip?_ne {T : Ty} {l l' : Leaf T} (_ : l ∈ T.leaves) (_ : l' ∈ T.leaves)
    (h : l ≠ l') : Path.strip? l.2 l'.2 = none :=
  Leaf.strip?_ne h

/-! ## Direct paths, below a value -/

theorem Path.out_append {T U W : Ty} : (p : Path T U) → (s : Path U W) → p.direct = true →
    (p.append s).out = (p.out || s.out)
  | .nil, s, _ => by rw [Path.append_nil]; simp only [Path.out, Bool.false_or]
  | .field h p, s, hd => by
    rw [Path.append_field]; exact Path.out_append p s hd
  | .atF i p, s, hd => by
    rw [Path.append_atF]
    simp only [Path.out, Path.out_append p s hd, Bool.or_assoc]
  | .at _ _, _, hd => by simp only [Path.direct, Bool.false_eq_true] at hd
  | .key _ _, _, hd => by simp only [Path.direct, Bool.false_eq_true] at hd

theorem Path.direct_append_of {T U W : Ty} : (p : Path T U) → (s : Path U W) →
    (p.append s).direct = true → p.direct = true
  | .nil, _, _ => rfl
  | .field h p, s, hd => by rw [Path.append_field] at hd; exact Path.direct_append_of p s hd
  | .atF i p, s, hd => by rw [Path.append_atF] at hd; exact Path.direct_append_of p s hd
  | .at _ _, _, hd => by rw [Path.append_at] at hd; exact hd
  | .key _ _, _, hd => by rw [Path.append_key] at hd; exact hd

/-- A direct path from a finite shape reaches no dynamic array. -/
theorem Ty.Finite.not_array {E : Ty} : {T : Ty} → T.Finite → (r : Path T (.ref (.array E))) →
    r.direct = true → False
  | _, hT, .nil, _ => by cases hT
  | _, hT, .field h r, hd => by
    cases hT with
    | struct s hs => exact Ty.Finite.not_array (hs _ _ h) r hd
  | _, hT, .atF _ r, hd => by
    cases hT with
    | fixed E n _ hE => exact Ty.Finite.not_array hE r hd
  | _, _, .at _ _, hd => by simp only [Path.direct, Bool.false_eq_true] at hd
  | _, _, .key _ _, hd => by simp only [Path.direct, Bool.false_eq_true] at hd

/-! ## Shaped values -/

/-- **Shaped as the typed storage shapes it**: every location a direct path
reaches inside the value is there, and nothing is there past a fixed array's
end.  The Theory's delete and copy reset or copy what is there; a word
written makes its location there. -/
structure TVal.Shaped {T : Ty} (v : TVal T) : Prop where
  has_in : ∀ {V : Ty} (r : Path T V), r.direct = true → r.out = false → v.has r = true
  absent_out : ∀ {V : Ty} {α : Type} (c : Comp V α) (r : Path T V), r.out = true →
    c.read v r = c.absent

theorem SVal.findM_direct : {T V : Ty} → (v : SVal T) → (r : Path T V) → r.direct = true →
    r.out = false → (v.findM r).isSome = true
  | _, _, v, .nil, _, _ => by rw [SVal.findM_nil']; rfl
  | _, _, .struct fs, .field h r, hd, ho => SVal.findM_direct (fs.get h) r hd ho
  | _, _, .fixed e, .atF i r, hd, ho => by
    simp only [Path.out, Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_le] at ho
    rw [SVal.findM_atF']
    have hl : i.1.toNat < e.toList.length := by rw [SVec.length_toList]; exact ho.1
    rw [List.getElem?_eq_getElem hl, Option.bind_some]
    exact SVal.findM_direct _ r hd ho.2
  | _, _, _, .at _ _, hd, _ => by simp only [Path.direct, Bool.false_eq_true] at hd
  | _, _, _, .key _ _, hd, _ => by simp only [Path.direct, Bool.false_eq_true] at hd

theorem SVal.findM_out : {T V : Ty} → (v : SVal T) → (r : Path T V) → r.out = true →
    v.findM r = none
  | _, _, _, .nil, ho => by simp only [Path.out, Bool.false_eq_true] at ho
  | _, _, .struct fs, .field h r, ho => SVal.findM_out (fs.get h) r ho
  | _, _, @SVal.fixed _ n e, .atF i r, ho => by
    rw [SVal.findM_atF']
    by_cases hi : n ≤ i.1.toNat
    · have hl : e.toList.length ≤ i.1.toNat := by rw [SVec.length_toList]; exact hi
      rw [List.getElem?_eq_none hl]; rfl
    · simp only [Path.out, hi, decide_false, Bool.false_or] at ho
      cases e.toList[i.1.toNat]? with
      | none => rfl
      | some x => exact SVal.findM_out x r ho
  | _, _, _, .at _ _, ho => by simp only [Path.out, Bool.false_eq_true] at ho
  | _, _, _, .key _ _, ho => by simp only [Path.out, Bool.false_eq_true] at ho

/-- **Every typed value is shaped.** -/
theorem SVal.obs_shaped {T : Ty} (v : SVal T) : v.obs.Shaped where
  has_in r hd ho := SVal.findM_direct v r hd ho
  absent_out c r ho := by
    rw [SVal.obs, c.read_obsOpt, Option.bind_some, SVal.findM_out v r ho]

/-- **The storage is shaped at every location it has.** -/
theorem Storage.obs_shaped {C : Contract} {U : Ty} (st : Storage C) (r : SRef C U) {v : SVal U}
    (h : st.find r = some v) : (st.obs.find (.ref r)).Shaped := by
  rw [Storage.obs_find, h]
  exact SVal.obs_shaped v

/-! ## Words written at leaves, read -/

namespace Obs

variable {L : Ty → Type} [ObsLoc L]

/-- A copy to a word is a save. -/
theorem copyTo_prim (o : Obs L) {P : PrimTy} (q : L (.prim P)) (v : TVal (.prim P)) :
    o.copyTo q v = o.save q v := by
  rw [copyTo, TVal.overlay_prim]

/-- Below a location not below `p`, nothing below `p` is. -/
theorem strip?_app_none {T U : Ty} {p : L T} {q : L U} (h : ObsLoc.strip? p q = none)
    {V : Ty} (r : Path T V) : ObsLoc.strip? (ObsLoc.app p r) q = none := by
  cases hs : ObsLoc.strip? (ObsLoc.app p r) q with
  | none => rfl
  | some s =>
    have e := ObsLoc.eq_of_strip? _ q hs
    rw [ObsLoc.app_app] at e
    rw [e, ObsLoc.strip?_app] at h
    cases h

/-- The words `g` written at the leaves `ls` below `p`. -/
abbrev writeLeaves (o : Obs L) {T : Ty} (p : L T) (ls : List (Leaf T))
    (g : (l : Leaf T) → l.1.Denote) : Obs L :=
  ls.foldl (fun a l => a.copyTo (ObsLoc.app p l.2) (TVal.ofWord (g l))) o

theorem writeLeaves_len {T : Ty} (p : L T) (g : (l : Leaf T) → l.1.Denote) :
    (ls : List (Leaf T)) → (o : Obs L) → {E : Ty} → (q : L (.ref (.array E))) →
    (o.writeLeaves p ls g).len q = o.len q
  | [], _, _, _ => rfl
  | l :: ls, o, E, q => by
    simp only [writeLeaves, List.foldl_cons]
    rw [writeLeaves_len p g ls, copyTo_prim]
    simp only [save]
    split
    · rename_i s hs
      have e := ObsLoc.eq_of_strip? _ q hs
      cases s
    · rfl

theorem writeLeaves_frame {T : Ty} {p : L T} (g : (l : Leaf T) → l.1.Denote) :
    (ls : List (Leaf T)) → (o : Obs L) → {U : Ty} → (q : L U) → ObsLoc.strip? p q = none →
    ((o.writeLeaves p ls g).has q = o.has q) ∧
    (∀ {P : PrimTy} (e : U = .prim P), (o.writeLeaves p ls g).word (e ▸ q) = o.word (e ▸ q))
  | [], _, _, _, _ => ⟨rfl, fun _ => rfl⟩
  | l :: ls, o, U, q, hq => by
    simp only [writeLeaves, List.foldl_cons]
    obtain ⟨ih1, ih2⟩ := writeLeaves_frame g ls (o.copyTo (ObsLoc.app p l.2) (TVal.ofWord (g l))) q hq
    have hn := strip?_app_none hq l.2
    refine ⟨?_, fun e => ?_⟩
    · rw [ih1, copyTo_prim]; simp only [save, hn]
    · rw [ih2 e, copyTo_prim]; subst e; simp only [save, hn]

theorem writeLeaves_word_not_mem {T : Ty} (p : L T) (g : (l : Leaf T) → l.1.Denote)
    {P : PrimTy} (r : Path T (.prim P)) : (ls : List (Leaf T)) → (o : Obs L) →
    (⟨P, r⟩ : Leaf T) ∉ ls →
    (o.writeLeaves p ls g).word (ObsLoc.app p r) = o.word (ObsLoc.app p r)
  | [], _, _ => rfl
  | l :: ls, o, hm => by
    simp only [writeLeaves, List.foldl_cons]
    have hm' : (⟨P, r⟩ : Leaf T) ∉ ls := fun h => hm (List.mem_cons_of_mem _ h)
    rw [writeLeaves_word_not_mem p g r ls _ hm', copyTo_prim]
    have hne : l ≠ ⟨P, r⟩ := fun e => hm (e ▸ List.mem_cons_self)
    simp only [save, ObsLoc.strip?_app_app, Leaf.strip?_ne hne]

theorem writeLeaves_word_mem {T : Ty} (p : L T) (g : (l : Leaf T) → l.1.Denote) {P : PrimTy}
    (r : Path T (.prim P)) : (ls : List (Leaf T)) → (o : Obs L) → (⟨P, r⟩ : Leaf T) ∈ ls →
    (o.writeLeaves p ls g).word (ObsLoc.app p r) = g ⟨P, r⟩
  | [], _, h => absurd h List.not_mem_nil
  | l :: ls, o, h => by
    simp only [writeLeaves, List.foldl_cons]
    by_cases hm : (⟨P, r⟩ : Leaf T) ∈ ls
    · exact writeLeaves_word_mem p g r ls _ hm
    · have hl : l = ⟨P, r⟩ := by
        rcases List.mem_cons.mp h with e | e
        · exact e.symm
        · exact absurd e hm
      subst hl
      rw [writeLeaves_word_not_mem p g r ls _ hm, copyTo_prim]
      simp only [save, ObsLoc.strip?_app_app, Path.strip?_self]
      rfl

theorem writeLeaves_has {T : Ty} (p : L T) (g : (l : Leaf T) → l.1.Denote) {V : Ty}
    (r : Path T V) : (ls : List (Leaf T)) → (o : Obs L) →
    (o.writeLeaves p ls g).has (ObsLoc.app p r) =
      ((ls.any fun l => (Path.strip? l.2 r).isSome) || o.has (ObsLoc.app p r))
  | [], _ => by simp only [writeLeaves, List.foldl_nil, List.any_nil, Bool.false_or]
  | l :: ls, o => by
    simp only [writeLeaves, List.foldl_cons]
    rw [writeLeaves_has p g r ls, copyTo_prim]
    simp only [save, ObsLoc.strip?_app_app, List.any_cons]
    cases hs : Path.strip? l.2 r with
    | none => simp only [Option.isSome_none, Bool.false_or]
    | some s =>
      simp only [Option.isSome_some, Bool.true_or]
      have e := Path.eq_of_strip?_prim l.2 r hs
      obtain ⟨P, l⟩ := l
      simp only [Sigma.mk.injEq] at e
      obtain ⟨rfl, -⟩ := e
      cases s
      simp only [Bool.or_eq_true]
      exact Or.inr rfl

end Obs

/-! ## A delete and a copy at a finite shape, read -/

theorem Path.direct_append {T U W : Ty} : (p : Path T U) → (r : Path U W) → p.direct = true →
    (p.append r).direct = r.direct
  | .nil, r, _ => by rw [Path.append_nil]
  | .field h p, r, hd => by rw [Path.append_field]; exact Path.direct_append p r hd
  | .atF i p, r, hd => by rw [Path.append_atF]; exact Path.direct_append p r hd
  | .at _ _, _, hd => by simp only [Path.direct, Bool.false_eq_true] at hd
  | .key _ _, _, hd => by simp only [Path.direct, Bool.false_eq_true] at hd

/-- A word written at a leaf is at a direct path inside the value. -/
theorem Ty.leaves_any {T V : Ty} {r : Path T V}
    (h : (T.leaves.any fun l => (Path.strip? l.2 r).isSome) = true) :
    r.direct = true ∧ r.out = false := by
  simp only [List.any_eq_true, Option.isSome_iff_exists] at h
  obtain ⟨⟨P, l⟩, hl, s, hs⟩ := h
  have e := Path.eq_of_strip?_prim l r hs
  simp only [Sigma.mk.injEq] at e
  obtain ⟨rfl, e⟩ := e
  cases eq_of_heq e
  exact (Ty.mem_leaves _).1 hl

namespace TVal

variable {V : Ty} {α : Type}

theorem find_nil_self {T : Ty} (v : TVal T) : v.find .nil = v :=
  Obs.ext (fun _ => by simp only [Obs.find, ObsLoc.app_path, Path.append_nil])
    (fun _ => by simp only [Obs.find, ObsLoc.app_path, Path.append_nil])
    (fun _ => by simp only [Obs.find, ObsLoc.app_path, Path.append_nil])

/-- A delete at a finite shape: every direct location reset, the rest as it is. -/
theorem delR_finite (c : Comp V α) : {T : Ty} → T.Finite → (v : TVal T) → (r : Path T V) →
    TVal.delR c v r = if r.direct = true then c.reset (v.find r) else c.read v r
  | _, _, v, .nil => by simp only [TVal.delR, Path.direct, ↓reduceIte, find_nil_self]
  | _, hT, v, .field h r => by
    cases hT with
    | struct s hs =>
      rw [TVal.delR, delR_finite c (hs _ _ h) _ r, Obs.find_find, c.read_find]
      simp only [ObsLoc.app_path, Path.append_field, Path.append_nil, Path.direct]
  | _, hT, v, .atF i r => by
    cases hT with
    | fixed E n _ hE =>
      rw [TVal.delR, delR_finite c hE _ r, Obs.find_find, c.read_find]
      simp only [ObsLoc.app_path, Path.append_atF, Path.append_nil, Path.direct]
  | _, hT, _, .at _ _ => by cases hT
  | _, _, v, .key k r => rfl

/-- What a copy at a finite shape needs of its two sides: where the new one
has a direct location the old one has it, and where it has not, nothing is
below it in the old one. -/
structure Agree {T : Ty} (old new : TVal T) : Prop where
  has : ∀ {V : Ty} (r : Path T V), r.direct = true → new.has r = true → old.has r = true
  absent : ∀ {V : Ty} (r : Path T V), r.direct = true → new.has r = false →
    ∀ {W : Ty} {α : Type} (c : Comp W α) (s : Path V W), c.read old (r.append s) = c.absent

theorem Agree.find {T U : Ty} {old new : TVal T} (h : Agree old new) (p : Path T U)
    (hp : p.direct = true) : Agree (old.find p) (new.find p) where
  has r hd hn := h.has (p.append r) (by rw [Path.direct_append p r hp]; exact hd) hn
  absent := by
    intro _ r hd hn _ _ c s
    rw [c.read_find, ← Path.append_assoc]
    exact h.absent (p.append r) (by rw [Path.direct_append p r hp]; exact hd) hn c s

/-- Two shaped values agree. -/
theorem Shaped.agree {T : Ty} {old new : TVal T} (ho : old.Shaped) (hn : new.Shaped) :
    Agree old new where
  has r hd h := by
    cases hout : r.out
    · exact ho.has_in r hd hout
    · have := hn.absent_out (Comp.has _) r hout
      exact absurd (this.symm.trans h) Bool.false_ne_true
  absent := by
    intro _ r hd h _ _ c s
    cases hout : r.out
    · rw [hn.has_in r hd hout] at h; cases h
    · exact ho.absent_out c _ (by rw [Path.out_append r s hd, hout, Bool.true_or])

/-- A copy at a finite shape: the new value at every direct location, the
old one below a key. -/
theorem ovR_finite (c : Comp V α) : {T : Ty} → T.Finite → (old new : TVal T) → Agree old new →
    (r : Path T V) → TVal.ovR c old new r = if r.direct = true then c.read new r else c.read old r
  | _, _, _, _, _, .nil => rfl
  | _, hT, old, new, ha, .field h r => by
    cases hT with
    | struct s hs =>
      rw [TVal.ovR, ovR_finite c (hs _ _ h) _ _ (ha.find _ rfl) r, c.read_find, c.read_find]
      simp only [Path.append_field, Path.append_nil, Path.direct]
  | _, hT, old, new, ha, .atF i r => by
    cases hT with
    | fixed E n _ hE =>
      rw [TVal.ovR, ovR_finite c hE _ _ (ha.find _ rfl) r, c.read_find, c.read_find]
      simp only [Path.append_atF, Path.append_nil, Path.direct]
  | _, hT, _, _, _, .at _ _ => by cases hT
  | _, _, old, new, ha, .key k r => by
    simp only [TVal.ovR, Path.direct, Bool.false_eq_true, ↓reduceIte]
    cases hn : new.has .nil
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have e := ha.absent .nil rfl hn c (.key k r)
      rw [Path.append_nil] at e
      exact e.symm
    · simp only [↓reduceIte, ha.has .nil rfl hn]

end TVal

namespace Obs

variable {L : Ty → Type} [ObsLoc L]

/-- At a finite shape, the leaves' writes leave a location's presence as a
shaped value has it. -/
theorem writeLeaves_has_shaped {T V : Ty} (p : L T) (g : (l : Leaf T) → l.1.Denote) (o : Obs L)
    (hs : (o.find p).Shaped) (r : Path T V) :
    (o.writeLeaves p T.leaves g).has (ObsLoc.app p r) = o.has (ObsLoc.app p r) := by
  rw [writeLeaves_has]
  cases ha : (T.leaves.any fun l => (Path.strip? l.2 r).isSome)
  · rfl
  · obtain ⟨hd, ho⟩ := Ty.leaves_any ha
    exact (hs.has_in r hd ho).symm

/-- **`delete` at a finite shape is a word written per leaf**: the default
at each, where the value is shaped. -/
theorem delAt_expand {T : Ty} (hT : T.Finite) (o : Obs L) (p : L T) (hs : (o.find p).Shaped) :
    o.delAt p = T.leaves.foldl
      (fun a l => a.copyTo (ObsLoc.app p l.2) (TVal.ofWord (PrimTy.dflt l.1))) o := by
  show _ = o.writeLeaves p T.leaves (fun l => PrimTy.dflt l.1)
  apply Obs.ext
  · intro P q
    cases hq : ObsLoc.strip? p q with
    | none =>
      rw [delAt, save_word_frame _ _ hq]
      exact ((writeLeaves_frame _ _ _ q hq).2 rfl).symm
    | some r =>
      obtain rfl := ObsLoc.eq_of_strip? p q hq
      rw [delAt, save_word_below]
      show TVal.delR (Comp.word P) (o.find p) r = _
      rw [TVal.delR_finite _ hT]
      by_cases hd : r.direct = true
      · simp only [hd, ↓reduceIte]
        show PrimTy.dflt P = _
        cases ho : r.out
        · rw [writeLeaves_word_mem _ _ r _ _ ((Ty.mem_leaves r).2 ⟨hd, ho⟩)]
        · have hm : (⟨P, r⟩ : Leaf T) ∉ T.leaves := fun h => by
            rw [((Ty.mem_leaves r).1 h).2] at ho; cases ho
          rw [writeLeaves_word_not_mem _ _ r _ _ hm]
          exact (hs.absent_out (Comp.word P) r ho).symm
      · simp only [hd, Bool.false_eq_true, ↓reduceIte]
        have hm : (⟨P, r⟩ : Leaf T) ∉ T.leaves := fun h => hd ((Ty.mem_leaves r).1 h).1
        rw [writeLeaves_word_not_mem _ _ r _ _ hm]
        rfl
  · intro E q
    rw [writeLeaves_len]
    cases hq : ObsLoc.strip? p q with
    | none => rw [delAt, save_len_frame _ _ hq]
    | some r =>
      obtain rfl := ObsLoc.eq_of_strip? p q hq
      simp only [delAt, save, ObsLoc.strip?_app]
      show TVal.delR (Comp.len E) (o.find p) r = _
      rw [TVal.delR_finite _ hT]
      have hd : r.direct = false := by
        cases h : r.direct
        · rfl
        · exact (hT.not_array r h).elim
      simp only [hd, Bool.false_eq_true, ↓reduceIte]
      rfl
  · intro V q
    cases hq : ObsLoc.strip? p q with
    | none =>
      simp only [delAt, save, hq]
      exact ((writeLeaves_frame _ _ _ q hq).1).symm
    | some r =>
      obtain rfl := ObsLoc.eq_of_strip? p q hq
      rw [writeLeaves_has_shaped p _ o hs r]
      simp only [delAt, save, ObsLoc.strip?_app]
      show TVal.delR (Comp.has V) (o.find p) r = _
      rw [TVal.delR_finite _ hT]
      by_cases hd : r.direct = true
      · simp only [hd, ↓reduceIte]
        show (o.find p).has (ObsLoc.app r .nil) = _
        rw [ObsLoc.app_nil]
        rfl
      · simp only [hd, Bool.false_eq_true, ↓reduceIte]
        rfl

/-- **A copy at a finite shape is a word written per leaf**: the source's
word at each, read before the copy, where both sides are shaped. -/
theorem copyTo_find_expand {T : Ty} (hT : T.Finite) (o : Obs L) (p q : L T)
    (hp : (o.find p).Shaped) (hq : (o.find q).Shaped) :
    o.copyTo p (o.find q) = T.leaves.foldl
      (fun a l => a.copyTo (ObsLoc.app p l.2) (TVal.ofWord (o.word (ObsLoc.app q l.2)))) o := by
  show _ = o.writeLeaves p T.leaves (fun l => o.word (ObsLoc.app q l.2))
  have ha : TVal.Agree (o.find p) (o.find q) := TVal.Shaped.agree hp hq
  apply Obs.ext
  · intro P w
    cases hw : ObsLoc.strip? p w with
    | none =>
      rw [copyTo, save_word_frame _ _ hw]
      exact ((writeLeaves_frame _ _ _ w hw).2 rfl).symm
    | some r =>
      obtain rfl := ObsLoc.eq_of_strip? p w hw
      rw [copyTo, save_word_below]
      show TVal.ovR (Comp.word P) (o.find p) (o.find q) r = _
      rw [TVal.ovR_finite _ hT _ _ ha]
      by_cases hd : r.direct = true
      · simp only [hd, ↓reduceIte]
        cases ho : r.out
        · rw [writeLeaves_word_mem _ _ r _ _ ((Ty.mem_leaves r).2 ⟨hd, ho⟩)]
          rfl
        · have hm : (⟨P, r⟩ : Leaf T) ∉ T.leaves := fun h => by
            rw [((Ty.mem_leaves r).1 h).2] at ho; cases ho
          rw [writeLeaves_word_not_mem _ _ r _ _ hm]
          exact (hq.absent_out (Comp.word P) r ho).trans (hp.absent_out (Comp.word P) r ho).symm
      · simp only [hd, Bool.false_eq_true, ↓reduceIte]
        have hm : (⟨P, r⟩ : Leaf T) ∉ T.leaves := fun h => hd ((Ty.mem_leaves r).1 h).1
        rw [writeLeaves_word_not_mem _ _ r _ _ hm]
        rfl
  · intro E w
    rw [writeLeaves_len]
    cases hw : ObsLoc.strip? p w with
    | none => rw [copyTo, save_len_frame _ _ hw]
    | some r =>
      obtain rfl := ObsLoc.eq_of_strip? p w hw
      simp only [copyTo, save, ObsLoc.strip?_app]
      show TVal.ovR (Comp.len E) (o.find p) (o.find q) r = _
      rw [TVal.ovR_finite _ hT _ _ ha]
      have hd : r.direct = false := by
        cases h : r.direct
        · rfl
        · exact (hT.not_array r h).elim
      simp only [hd, Bool.false_eq_true, ↓reduceIte]
      rfl
  · intro V w
    cases hw : ObsLoc.strip? p w with
    | none =>
      simp only [copyTo, save, hw]
      exact ((writeLeaves_frame _ _ _ w hw).1).symm
    | some r =>
      obtain rfl := ObsLoc.eq_of_strip? p w hw
      rw [writeLeaves_has_shaped p _ o hp r]
      simp only [copyTo, save, ObsLoc.strip?_app]
      show TVal.ovR (Comp.has V) (o.find p) (o.find q) r = _
      rw [TVal.ovR_finite _ hT _ _ ha]
      by_cases hd : r.direct = true
      · simp only [hd, ↓reduceIte]
        cases ho : r.out
        · exact (hq.has_in r hd ho).trans (hp.has_in r hd ho).symm
        · exact (hq.absent_out (Comp.has V) r ho).trans (hp.absent_out (Comp.has V) r ho).symm
      · simp only [hd, Bool.false_eq_true, ↓reduceIte]
        rfl

end Obs

/-! ## Push and pop of a word -/

namespace Obs

variable {L : Ty → Type} [ObsLoc L]

/-- The last of two saves at one location wins. -/
theorem save_save_same (o : Obs L) {U : Ty} (p : L U) (a b : TVal U) :
    (o.save p a).save p b = o.save p b := by
  apply Obs.ext <;> intro _ q <;> simp only [save] <;> split <;> rfl

/-- A save over a save below it wins. -/
theorem save_save_above (o : Obs L) {U V : Ty} (p : L U) (s : Path U V) (v : TVal V)
    (Y : TVal U) : (o.save (ObsLoc.app p s) v).save p Y = o.save p Y := by
  apply Obs.ext <;> intro _ q <;> simp only [save] <;> split
  all_goals first
    | rfl
    | (rename_i hq; simp only [strip?_app_none hq s])

/-- A save below a save is made in the value saved. -/
theorem save_save_below (o : Obs L) {U V : Ty} (p : L U) (s : Path U V) (v : TVal V)
    (X : TVal U) : (o.save p X).save (ObsLoc.app p s) v = o.save p (X.save s v) := by
  apply Obs.ext <;> intro _ q
  all_goals
    cases hq : ObsLoc.strip? p q with
    | none => simp only [save, hq, strip?_app_none hq s]
    | some r =>
      obtain rfl := ObsLoc.eq_of_strip? p q hq
      simp only [save, ObsLoc.strip?_app_app, ObsLoc.strip?_app, ObsLoc.strip?_path]

end Obs

namespace TVal

/-- A slot's save leaves the length set at the array. -/
theorem setLen_save {E V : Ty} (a : TVal (.ref (.array E))) (k : Nat) (i : PrimTy.uint.Denote)
    (s : Path E V) (v : TVal V) : (a.setLen k).save (.at i s) v = TVal.setLen (a.save (.at i s) v) k := by
  apply Obs.ext <;> intro _ q
  · simp only [Obs.save, setLen]
  · simp only [Obs.save, setLen]
    cases q with
    | nil => simp only [ObsLoc.strip?_path, Path.strip?, Path.isNilB, ↓reduceIte]
    | «at» j r => simp only [Path.isNilB, Bool.false_eq_true, ↓reduceIte]
  · simp only [Obs.save, setLen]

/-- A word with its location there, deleted: the default word. -/
theorem del_prim {P : PrimTy} (v : TVal (.prim P)) (h : v.has .nil = true) :
    v.del = TVal.ofWord (PrimTy.dflt P) := by
  apply Obs.ext
  · intro _ q; cases q; rfl
  · intro _ q; cases q
  · intro _ q; cases q; exact h

end TVal

namespace Obs

variable {L : Ty → Type} [ObsLoc L]

/-- **A push of a word is one more live slot, then a save at index `len`.** -/
theorem push_prim (o : Obs L) {P : PrimTy} (p : L (.ref (.array (.prim P))))
    (v : TVal (.prim P)) :
    o.push p v = (o.extend p).copyTo (ObsLoc.app p (.at (uintOfNat (o.len p)) .nil)) v := by
  have hl : (o.find p).len .nil = o.len p := by
    show o.len (ObsLoc.app p .nil) = _
    rw [ObsLoc.app_nil]
  rw [copyTo_prim, extend, save_save_below, push]
  congr 1
  simp only [TVal.extendA, Ty.isPrimitive, Bool.true_or, ↓reduceIte, TVal.pushA, hl,
    TVal.setLen_save, save_save_same]

/-- **A pop of a word is the last slot deleted, then the length shrunk
keeping it**, at a nonempty array. -/
theorem pop_prim (o : Obs L) {P : PrimTy} (p : L (.ref (.array (.prim P))))
    (h : o.len p ≠ 0) :
    o.pop false p = (o.delAt (ObsLoc.app p (.at (uintOfNat (o.len p - 1)) .nil))).pop true p := by
  have hl : (o.find p).len .nil = o.len p := by
    show o.len (ObsLoc.app p .nil) = _
    rw [ObsLoc.app_nil]
  rw [pop, pop, delAt, find_save_below, save_save_above, ← find_find]
  congr 1
  have hl' : ((o.find p).save (.at (uintOfNat (o.len p - 1)) .nil)
      ((o.find p).find (.at (uintOfNat (o.len p - 1)) .nil)).del).len .nil = o.len p := by
    rw [← hl]; rfl
  simp only [TVal.popA, hl, hl', h, ↓reduceIte, Bool.false_eq_true]

/-- The same with the slot's default saved, where the slot is there (as it
is below the length of a typed array). -/
theorem pop_prim_copyTo (o : Obs L) {P : PrimTy} (p : L (.ref (.array (.prim P))))
    (h : o.len p ≠ 0) (hs : o.has (ObsLoc.app p (.at (uintOfNat (o.len p - 1)) .nil)) = true) :
    o.pop false p = (o.copyTo (ObsLoc.app p (.at (uintOfNat (o.len p - 1)) .nil))
      (TVal.ofWord (PrimTy.dflt P))).pop true p := by
  rw [pop_prim o p h, delAt, copyTo_prim, TVal.del_prim]
  show o.has (ObsLoc.app _ .nil) = true
  rw [ObsLoc.app_nil]
  exact hs

end Obs

/-! ## The interpreter: a typed value by its leaves -/

/-- Distinct leaves part (`Path.Diverges`). -/
theorem Leaf.diverges {T : Ty} {l l' : Leaf T} (h : l ≠ l') : Path.Diverges l.2 l'.2 := by
  rcases Path.strip?_none l.2 l'.2 (Leaf.strip?_ne h) with hd | ⟨r, hr, _⟩
  · exact hd
  · obtain ⟨P', l'⟩ := l'
    cases r with
    | nil => exact absurd Path.labels_nil hr

/-- A leaf and a direct path to a mapping part. -/
theorem Leaf.diverges_map {T : Ty} (l : Leaf T) (hl : l.2.direct = true) {K : PrimTy} {V : Ty}
    (m : Path T (.ref (.mapping K V))) (hm : m.direct = true) : Path.Diverges l.2 m := by
  cases hs : Path.strip? l.2 m with
  | some s =>
    have e := Path.eq_of_strip?_prim l.2 m hs
    simp only [Sigma.mk.injEq] at e
    exact absurd e.1 (by simp only [reduceCtorEq, not_false_eq_true])
  | none =>
    rcases Path.strip?_none l.2 m hs with hd | ⟨r, _, e⟩
    · exact hd
    · have hr : r.direct = true := by rw [← Path.direct_append m r hm, ← e]; exact hl
      cases r with
      | key _ _ => simp only [Path.direct, Bool.false_eq_true] at hr

/-- Two member lists with distinct names are equal where every member is. -/
theorem SFields.ext_nodup : {fs : List (Name × Ty)} → nodupKeysB fs = true →
    (a b : SFields fs) →
    (∀ (f : Name) (T : Ty) (h : lookupBy f fs = some T), a.get h = b.get h) → a = b
  | [], _, .nil, .nil, _ => rfl
  | (f, T) :: fs, hn, .cons va ra, .cons vb rb, h => by
    simp only [nodupKeysB, Bool.and_eq_true, Option.isNone_iff_eq_none] at hn
    have h0 : lookupBy f ((f, T) :: fs) = some T := by simp only [lookupBy, ↓reduceIte]
    have e0 := h f T h0
    simp only [SFields.get_cons, dite_true] at e0
    have er : ra = rb := SFields.ext_nodup hn.2 ra rb fun g U hg => by
      have hgf : g ≠ f := fun e => by subst e; rw [hn.1] at hg; cases hg
      have hg' : lookupBy g ((f, T) :: fs) = some U := by
        simp only [lookupBy, hgf, ↓reduceIte]; exact hg
      have e := h g U hg'
      simp only [SFields.get_cons, hgf, dite_false] at e
      exact e
    rw [e0, er]

/-- **A value of a finite shape is its leaves and its mappings.** -/
theorem SVal.ext_finite {T : Ty} (hT : T.Finite) : (x z : SVal T) →
    (∀ (P : PrimTy) (l : Path T (.prim P)), l.direct = true → l.out = false →
      x.findM l = z.findM l) →
    (∀ (K : PrimTy) (V : Ty) (m : Path T (.ref (.mapping K V))), m.direct = true →
      m.out = false → x.findM m = z.findM m) → x = z := by
  induction hT with
  | prim P =>
    intro x z hl _
    have e := hl P .nil rfl rfl
    rw [SVal.findM_nil', SVal.findM_nil'] at e
    exact Option.some.inj e
  | mapping K V =>
    intro x z _ hm
    have e := hm K V .nil rfl rfl
    rw [SVal.findM_nil', SVal.findM_nil'] at e
    exact Option.some.inj e
  | struct s _ ih =>
    intro x z hl hm
    cases x with
    | struct fs =>
      cases z with
      | struct zs =>
        congr 1
        exact SFields.ext_nodup (structDef_nodup s) fs zs fun f T h =>
          ih f T h _ _ (fun P l hd ho => hl P (.field h l) hd ho)
            (fun K V m hd ho => hm K V (.field h m) hd ho)
  | fixed E n hn _ ih =>
    intro x z hl hm
    cases x with
    | fixed e =>
      cases z with
      | fixed e' =>
        congr 1
        apply SVec.eq_of_toList_eq
        apply List.ext_getElem?
        intro i
        by_cases hi : i < n
        · have hl1 : i < e.toList.length := by rw [SVec.length_toList]; exact hi
          have hl2 : i < e'.toList.length := by rw [SVec.length_toList]; exact hi
          rw [List.getElem?_eq_getElem hl1, List.getElem?_eq_getElem hl2]
          have hu : (uintOfNat i).1.toNat = i := by
            rw [uintOfNat_val (by omega)]; simp only [Int.toNat_natCast]
          have hio : decide (n ≤ (uintOfNat i).1.toNat) = false := by
            rw [hu]; simp only [decide_eq_false_iff_not, Nat.not_le]; exact hi
          congr 1
          refine ih _ _ (fun P l hd ho => ?_) (fun K V m hd ho => ?_)
          · have e := hl P (.atF (uintOfNat i) l) hd (by simp only [Path.out, hio, ho, Bool.or_self])
            rw [SVal.findM_atF', SVal.findM_atF', hu, List.getElem?_eq_getElem hl1,
              List.getElem?_eq_getElem hl2, Option.bind_some, Option.bind_some] at e
            exact e
          · have e := hm K V (.atF (uintOfNat i) m) hd (by simp only [Path.out, hio, ho, Bool.or_self])
            rw [SVal.findM_atF', SVal.findM_atF', hu, List.getElem?_eq_getElem hl1,
              List.getElem?_eq_getElem hl2, Option.bind_some, Option.bind_some] at e
            exact e
        · rw [List.getElem?_eq_none (by rw [SVec.length_toList]; omega),
            List.getElem?_eq_none (by rw [SVec.length_toList]; omega)]

/-- A copy read along a direct path: the new value laid over the old one there. -/
theorem SVal.findM_overlay_direct : {T V : Ty} → (x y : SVal T) → (r : Path T V) →
    r.direct = true → r.out = false →
    ∃ a b, x.findM r = some a ∧ y.findM r = some b ∧ (x.overlay y).findM r = some (a.overlay b)
  | _, _, x, y, .nil, _, _ => ⟨x, y, SVal.findM_nil' x, SVal.findM_nil' y, SVal.findM_nil' _⟩
  | _, _, .struct fs, .struct ys, .field h r, hd, ho => by
    obtain ⟨a, b, ha, hb, hab⟩ := SVal.findM_overlay_direct (fs.get h) (ys.get h) r hd ho
    refine ⟨a, b, ha, hb, ?_⟩
    rw [SVal.overlay_struct, SVal.findM_field', SFields.get_overlay]
    exact hab
  | _, _, @SVal.fixed _ n e, .fixed e', .atF i r, hd, ho => by
    simp only [Path.out, Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_le] at ho
    have hl1 : i.1.toNat < e.toList.length := by rw [SVec.length_toList]; exact ho.1
    have hl2 : i.1.toNat < e'.toList.length := by rw [SVec.length_toList]; exact ho.1
    obtain ⟨a, b, ha, hb, hab⟩ := SVal.findM_overlay_direct _ _ r hd ho.2
    refine ⟨a, b, ?_, ?_, ?_⟩
    · rw [SVal.findM_atF', List.getElem?_eq_getElem hl1, Option.bind_some]; exact ha
    · rw [SVal.findM_atF', List.getElem?_eq_getElem hl2, Option.bind_some]; exact hb
    · rw [SVal.overlay_fixed, SVal.findM_atF', SVec.getElem?_overlayOn,
        List.getElem?_eq_getElem hl1, List.getElem?_eq_getElem hl2, SVal.overlayOpt_some_some,
        Option.bind_some]
      exact hab
  | _, _, _, _, .at _ _, hd, _ => by simp only [Path.direct, Bool.false_eq_true] at hd
  | _, _, _, _, .key _ _, hd, _ => by simp only [Path.direct, Bool.false_eq_true] at hd

/-- A delete read along a direct path: the value there deleted. -/
theorem SVal.findM_defaultOf_direct : {T V : Ty} → (x : SVal T) → (r : Path T V) →
    r.direct = true → r.out = false →
    ∃ a, x.findM r = some a ∧ x.defaultOf.findM r = some a.defaultOf
  | _, _, x, .nil, _, _ => ⟨x, SVal.findM_nil' x, SVal.findM_nil' _⟩
  | _, _, .struct fs, .field h r, hd, ho => by
    obtain ⟨a, ha, hab⟩ := SVal.findM_defaultOf_direct (fs.get h) r hd ho
    refine ⟨a, ha, ?_⟩
    rw [SVal.defaultOf_struct, SVal.findM_field', SFields.get_defaultOf]
    exact hab
  | _, _, @SVal.fixed _ n e, .atF i r, hd, ho => by
    simp only [Path.out, Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_le] at ho
    have hl1 : i.1.toNat < e.toList.length := by rw [SVec.length_toList]; exact ho.1
    obtain ⟨a, ha, hab⟩ := SVal.findM_defaultOf_direct _ r hd ho.2
    refine ⟨a, ?_, ?_⟩
    · rw [SVal.findM_atF', List.getElem?_eq_getElem hl1, Option.bind_some]; exact ha
    · rw [SVal.defaultOf_fixed, SVal.findM_atF', SVec.toList_defaultOf, List.getElem?_map,
        List.getElem?_eq_getElem hl1, Option.map_some, Option.bind_some]
      exact hab
  | _, _, _, .at _ _, hd, _ => by simp only [Path.direct, Bool.false_eq_true] at hd
  | _, _, _, .key _ _, hd, _ => by simp only [Path.direct, Bool.false_eq_true] at hd

/-- Words saved at leaves, read: each leaf its word, and what parts from
every leaf as it was. -/
theorem SVal.foldLeaves_read {T : Ty} (g : (l : Leaf T) → l.1.Denote) :
    (ls : List (Leaf T)) → (x : SVal T) → (∀ l ∈ ls, (x.findM l.2).isSome = true) →
    ∃ z, ls.foldlM (fun w l => w.saveM l.2 (.prim (g l))) x = some z ∧
      (∀ l ∈ ls, z.findM l.2 = some (.prim (g l))) ∧
      (∀ {W : Ty} (q : Path T W), (∀ l ∈ ls, Path.Diverges l.2 q) → z.findM q = x.findM q)
  | [], x, _ => ⟨x, rfl, fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl⟩
  | l :: ls, x, hx => by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hx l List.mem_cons_self)
    obtain ⟨x1, hx1⟩ := SVal.saveM_of_findM x l.2 hy (.prim (g l))
    have h1 : x1.findM l.2 = some (.prim (g l)) := SVal.findM_saveM x l.2 _ hx1
    have hx1' : ∀ l' ∈ ls, (x1.findM l'.2).isSome = true := by
      intro l' hl'
      by_cases e : l = l'
      · subst e; rw [h1]; rfl
      · rw [SVal.findM_saveM_diverges (Leaf.diverges e) x _ hx1]
        exact hx l' (List.mem_cons_of_mem _ hl')
    obtain ⟨z, hz, hzl, hzq⟩ := SVal.foldLeaves_read g ls x1 hx1'
    refine ⟨z, ?_, ?_, ?_⟩
    · rw [List.foldlM_cons, hx1]; exact hz
    · intro l' hl'
      by_cases hm : l' ∈ ls
      · exact hzl l' hm
      · have e : l' = l := by
          rcases List.mem_cons.mp hl' with e | e
          · exact e
          · exact absurd e hm
        subst e
        rw [hzq _ fun l'' hl'' => Leaf.diverges (fun e => hm (by rw [← e]; exact hl''))]
        exact h1
    · intro W q hq
      rw [hzq q fun l' hl' => hq l' (List.mem_cons_of_mem _ hl'),
        SVal.findM_saveM_diverges (hq l List.mem_cons_self) x _ hx1]

/-- **A copy at a finite shape, in the interpreter**: the new value's word
saved at every leaf of the old one. -/
theorem SVal.foldLeaves_overlay {T : Ty} (hT : T.Finite) (x y : SVal T) :
    T.leaves.foldlM (fun w l => w.saveM l.2 (.prim (SVal.wordOf (y.findM l.2)))) x =
      some (x.overlay y) := by
  obtain ⟨z, hz, hzl, hzq⟩ := SVal.foldLeaves_read (fun l => SVal.wordOf (y.findM l.2)) T.leaves x
    fun l hl => SVal.findM_direct x l.2 ((Ty.mem_leaves l.2).1 hl).1 ((Ty.mem_leaves l.2).1 hl).2
  rw [hz]
  congr 1
  refine SVal.ext_finite hT z (x.overlay y) (fun P l hd ho => ?_) (fun K V m hd ho => ?_)
  · rw [hzl ⟨P, l⟩ ((Ty.mem_leaves l).2 ⟨hd, ho⟩)]
    obtain ⟨a, b, _, hb, hab⟩ := SVal.findM_overlay_direct x y l hd ho
    rw [hab, hb]
    cases b
    rw [SVal.overlay_prim]
    rfl
  · rw [hzq m fun l hl => Leaf.diverges_map l ((Ty.mem_leaves l.2).1 hl).1 m hd]
    obtain ⟨a, b, ha, _, hab⟩ := SVal.findM_overlay_direct x y m hd ho
    rw [hab, ha]
    cases a; cases b
    rw [SVal.overlay_map]

/-- **A delete at a finite shape, in the interpreter**: the default word
saved at every leaf. -/
theorem SVal.foldLeaves_defaultOf {T : Ty} (hT : T.Finite) (x : SVal T) :
    T.leaves.foldlM (fun w l => w.saveM l.2 (.prim (PrimTy.dflt l.1))) x =
      some x.defaultOf := by
  obtain ⟨z, hz, hzl, hzq⟩ := SVal.foldLeaves_read (fun l => PrimTy.dflt l.1) T.leaves x
    fun l hl => SVal.findM_direct x l.2 ((Ty.mem_leaves l.2).1 hl).1 ((Ty.mem_leaves l.2).1 hl).2
  rw [hz]
  congr 1
  refine SVal.ext_finite hT z x.defaultOf (fun P l hd ho => ?_) (fun K V m hd ho => ?_)
  · rw [hzl ⟨P, l⟩ ((Ty.mem_leaves l).2 ⟨hd, ho⟩)]
    obtain ⟨a, _, hab⟩ := SVal.findM_defaultOf_direct x l hd ho
    rw [hab]
    cases a
    rw [SVal.defaultOf_prim]
  · rw [hzq m fun l hl => Leaf.diverges_map l ((Ty.mem_leaves l.2).1 hl).1 m hd]
    obtain ⟨a, ha, hab⟩ := SVal.findM_defaultOf_direct x m hd ho
    rw [hab, ha]
    cases a
    rw [SVal.defaultOf_map]

/-! ## The interpreter's storage -/

namespace Storage

variable {C : Contract}

/-- A save below a reference: the value there found, saved below, saved
back. -/
theorem save_append {U W : Ty} (st : Storage C) (r : SRef C U) (q : Path U W) (v : SVal W) :
    st.save (r.append q) v = (st.find r).bind fun x => (x.saveM q v).bind fun y => st.save r y := by
  simp only [Storage.save, Storage.find, SRef.append, SVal.save_eq_saveM, SVal.find_eq_findM,
    SVal.saveM_append_eq, Option.bind_eq_bind, Option.bind_assoc]

/-- Where a reference finds a value, a save at it lands. -/
theorem save_of_find {U : Ty} {st : Storage C} {r : SRef C U} {x : SVal U}
    (h : st.find r = some x) (v : SVal U) : ∃ st', st.save r v = some st' := by
  simp only [Storage.find, SVal.find_eq_findM] at h
  obtain ⟨x', hx'⟩ := SVal.saveM_of_findM _ r.path h v
  exact ⟨st.set r.hroot x', by simp only [Storage.save, SVal.save_eq_saveM, hx',
    Option.bind_eq_bind, Option.bind_some]⟩

/-- A save that lands finds the reference. -/
theorem find_of_save {U : Ty} {st st' : Storage C} {r : SRef C U} {v : SVal U}
    (h : st.save r v = some st') : (st.find r).isSome = true := by
  simp only [Storage.save, SVal.save_eq_saveM, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨x', hx', _⟩ := h
  have hx'' : (st.get r.hroot).saveM (r.path.append .nil) v = some x' := by
    rw [Path.append_nil_right]; exact hx'
  obtain ⟨y, _, hy, _, _⟩ := SVal.saveM_append _ r.path .nil v hx''
  simp only [Storage.find, SVal.find_eq_findM, hy, Option.isSome_some]

/-- The last of two saves at one reference wins. -/
theorem save_save {U : Ty} {st st₁ : Storage C} {r : SRef C U} {a : SVal U}
    (h : st.save r a = some st₁) (b : SVal U) : st₁.save r b = st.save r b := by
  simp only [Storage.save, SVal.save_eq_saveM, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨x₁, hx₁, rfl⟩ := h
  obtain ⟨x₂, hx₂⟩ := SVal.saveM_of_findM x₁ r.path (SVal.findM_saveM _ r.path a hx₁) b
  simp only [Storage.save, SVal.save_eq_saveM, SFields.get_set_same, hx₂,
    SVal.saveM_saveM _ r.path a b hx₁ hx₂, Option.bind_eq_bind, Option.bind_some,
    SFields.set_set]

/-- Saves below a reference, one after another, are their fold on the value
there, saved back. -/
theorem foldlM_save_append {T : Ty} (r : SRef C T) (val : (l : Leaf T) → SVal (.prim l.1)) :
    (l : Leaf T) → (ls : List (Leaf T)) → (st : Storage C) →
    (l :: ls).foldlM (fun s l => s.save (r.append l.2) (val l)) st =
      (st.find r).bind fun x =>
        ((l :: ls).foldlM (fun (w : SVal T) (l : Leaf T) => w.saveM l.2 (val l)) x).bind
          fun x' => st.save r x'
  | l, [], st => by
    simp only [List.foldlM_cons, List.foldlM_nil, save_append, bind_pure]
  | l, l₂ :: ls, st => by
    have ih := foldlM_save_append r val l₂ ls
    simp only [List.foldlM_cons] at ih ⊢
    rw [save_append]
    cases hf : st.find r with
    | none => rfl
    | some x =>
      cases hy : x.saveM l.2 (val l) with
      | none => simp only [Option.bind_eq_bind, Option.bind_some, hy, Option.bind_none]
      | some y =>
        obtain ⟨st₁, hs₁⟩ := save_of_find hf y
        simp only [Option.bind_eq_bind] at ih ⊢
        simp only [Option.bind_some, hy, hs₁, ih st₁, find_save_same hs₁, save_save hs₁]

/-- A word's write is its save. -/
theorem write_prim {P : PrimTy} (st : Storage C) (r : SRef C (.prim P)) (x : P.Denote) :
    st.write r (.prim x) = st.save r (.prim x) := by
  simp only [Storage.write, SVal.isPrim, Ty.isPrimitive, ↓reduceIte]

/-- **`delete` at a finite shape, in the interpreter, is a word written per
leaf**: the default at each.  At a shape with no leaf it is not
(`delete` still saves; through a mapping's default that adds an entry). -/
theorem delete_expand {T : Ty} (hT : T.Finite) (hne : T.leaves ≠ []) (st : Storage C)
    (r : SRef C T) :
    st.delete r = T.leaves.foldlM
      (fun s l => s.write (r.append l.2) (.prim (PrimTy.dflt l.1))) st := by
  obtain ⟨l, ls, e⟩ := List.exists_cons_of_ne_nil hne
  simp only [write_prim]
  rw [e, foldlM_save_append r (fun l => .prim (PrimTy.dflt l.1)), ← e]
  simp only [SVal.foldLeaves_defaultOf hT, Option.bind_some, Storage.delete, Option.bind_eq_bind]

/-- **A copy at a finite shape, in the interpreter, is a word written per
leaf**: the new value's word at each. -/
theorem write_expand {T : Ty} (hT : T.Finite) (hne : T.leaves ≠ []) (st : Storage C)
    (r : SRef C T) (v : SVal T) :
    st.write r v = T.leaves.foldlM
      (fun s l => s.write (r.append l.2) (.prim (SVal.wordOf (v.findM l.2)))) st := by
  obtain ⟨l, ls, e⟩ := List.exists_cons_of_ne_nil hne
  simp only [write_prim]
  rw [e, foldlM_save_append r (fun l => .prim (SVal.wordOf (v.findM l.2))), ← e]
  simp only [SVal.foldLeaves_overlay hT]
  unfold Storage.write
  cases hp : v.isPrim
  · simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  · simp only [↓reduceIte, Option.bind_some]
    cases T with
    | ref R => simp only [SVal.isPrim, Ty.isPrimitive, Bool.false_eq_true] at hp
    | prim P =>
      cases v with
      | prim x =>
        cases hf : st.find r with
        | none =>
          cases hs : st.save r (.prim x) with
          | none => rfl
          | some st' => have := find_of_save hs; rw [hf] at this; cases this
        | some y => simp only [Option.bind_some, SVal.overlay_prim]

/-- A read below a reference is the read below the value there. -/
theorem find_append {U W : Ty} (st : Storage C) (r : SRef C U) (q : Path U W) :
    st.find (r.append q) = (st.find r).bind (·.findM q) := by
  simp only [Storage.find, SRef.append, SVal.find_eq_findM, SVal.findM_append]

/-- Two folds whose steps agree on the list's elements. -/
theorem foldlM_congr_mem {α β : Type} {f g : β → α → Option β} : (ls : List α) →
    (∀ a ∈ ls, ∀ b, f b a = g b a) → ∀ b, ls.foldlM f b = ls.foldlM g b
  | [], _, _ => rfl
  | a :: ls, h, b => by
    simp only [List.foldlM_cons, h a List.mem_cons_self b]
    cases g b a with
    | none => rfl
    | some b' =>
      exact foldlM_congr_mem ls (fun a' ha' => h a' (List.mem_cons_of_mem _ ha')) b'

/-- **`a = b` at a finite shape, in the interpreter, is a word written per
leaf**: the source's word at each, read before the copy. -/
theorem write_find_expand {T : Ty} (hT : T.Finite) (hne : T.leaves ≠ []) (st : Storage C)
    (r q : SRef C T) {v : SVal T} (hv : st.find q = some v) :
    st.write r v = T.leaves.foldlM
      (fun s l => do let w ← st.find (q.append l.2); s.write (r.append l.2) w) st := by
  rw [write_expand hT hne st r v]
  have key : ∀ l ∈ T.leaves, st.find (q.append l.2) = some (.prim (SVal.wordOf (v.findM l.2))) := by
    intro l hl
    rw [find_append, hv, Option.bind_some]
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp
      (SVal.findM_direct v l.2 ((Ty.mem_leaves l.2).1 hl).1 ((Ty.mem_leaves l.2).1 hl).2)
    rw [hb]
    cases b
    rfl
  exact foldlM_congr_mem _ (fun l hl s => by
    simp only [key l hl, Option.bind_eq_bind, Option.bind_some]) st

/-- A word's slot past the end starts at its default. -/
theorem pushSlot_fst_prim {P : PrimTy} (l : List (SVal (.prim P))) :
    (pushSlot (.prim P) l).1 = SVal.dflt (.prim P) := by
  cases l <;> rfl

/-- **A push of a word is one more live slot, then a save at index `len`**,
in the interpreter. -/
theorem push_prim {P : PrimTy} (st : Storage C) (r : SRef C (.ref (.array (.prim P))))
    (x : P.Denote) :
    st.push r (fun _ => some (.prim x)) = (st.len r).bind fun i =>
      (st.push r some).bind fun st' => st'.save (r.append (.at i .nil)) (.prim x) := by
  cases hf : st.find r with
  | none => simp only [Storage.push, Storage.len, hf, Option.bind_eq_bind, Option.bind_none]
  | some a =>
    cases a with
    | array e sh hn =>
      rename_i n
      simp only [Storage.push, Storage.len, hf, Option.bind_eq_bind, Option.bind_some,
        SVal.view_array, pushSlot_fst_prim, pushSlot_snd]
      by_cases h : n + 1 < 2 ^ 256
      · rw [dif_pos h, dif_pos h]
        obtain ⟨st', hs'⟩ := save_of_find hf (SVal.array (SVec.ofList (e.toList ++
          [SVal.dflt (.prim P)])) (SList.ofList sh.toList.tail) (SVec.snoc_lt_bound e _ h))
        have hl : e.toList.length = n := SVec.length_toList e
        have hi : (lenU n hn).1.toNat = n := by simp only [lenU, Int.toNat_natCast]
        rw [hs', Option.bind_some, save_append, find_save_same hs', Option.bind_some]
        have hget : ((SVec.ofList (e.toList ++ [SVal.dflt (.prim P)])).toList ++
            (SList.ofList sh.toList.tail).toList)[(lenU n hn).1.toNat]? =
            some (SVal.dflt (.prim P)) := by
          rw [SVec.toList_ofList, hi, List.append_assoc, List.getElem?_append_right (Nat.le_of_eq hl),
            hl, Nat.sub_self, List.singleton_append, List.getElem?_cons_zero]
        simp only [SVal.saveM, hget, Option.bind_eq_bind, Option.bind_some, save_save hs']
        congr 1
        apply SVal.array_ext
        · simp only [SVec.toList_ofList, SList.toList_ofList, hi]
          simp only [List.length_append,
            List.length_cons, List.length_nil, Nat.zero_add, List.append_assoc, List.cons_append,
            List.nil_append, ← hl, Nat.le_refl, List.set_append_right, Nat.sub_self,
            List.set_cons_zero, List.take_append, Nat.add_sub_cancel_left, List.take_succ_cons,
            List.take_zero, List.append_cancel_right_eq]
          exact (List.take_of_length_le (Nat.le_succ _)).symm
        · simp only [SVec.toList_ofList, SList.toList_ofList, hi]
          simp only [List.length_append,
            List.length_cons, List.length_nil, Nat.zero_add, List.append_assoc, List.cons_append,
            List.nil_append, ← hl, Nat.le_refl, List.set_append_right, Nat.sub_self,
            List.set_cons_zero, List.drop_append, Nat.add_sub_cancel_left, List.drop_succ_cons,
            List.drop_tail, List.drop_one, List.self_eq_append_left, List.drop_eq_nil_iff,
            Nat.le_add_right]
      · simp only [dif_neg h, Option.bind_none]
/-- **A pop of a word is the last slot reset, then the length shrunk
keeping it**, in the interpreter (an empty array reverts either way). -/
theorem pop_prim {P : PrimTy} (st : Storage C) (r : SRef C (.ref (.array (.prim P)))) :
    st.pop false r = (st.len r).bind fun i =>
      (st.save (r.append (.at (uintOfNat (i.1.toNat - 1)) .nil)) (.prim (PrimTy.dflt P))).bind
        fun st₁ => st₁.pop true r := by
  cases hf : st.find r with
  | none => simp only [Storage.pop, Storage.len, hf, Option.bind_eq_bind, Option.bind_none]
  | some a =>
    cases a with
    | array e sh hn =>
      rename_i n
      have hi : (lenU n hn).1.toNat = n := by simp only [lenU, Int.toNat_natCast]
      have hl : e.toList.length = n := SVec.length_toList e
      simp only [Storage.pop, Storage.len, hf, Option.bind_eq_bind, Option.bind_some,
        SVal.view_array, hi, save_append]
      have hu : n ≠ 0 → (uintOfNat (n - 1)).1.toNat = n - 1 := fun _ => by
        rw [uintOfNat_val (by omega)]; simp only [Int.toNat_natCast]
      cases hr : e.toList.reverse with
      | nil =>
        have h0 : n = 0 := by
          rw [← hl, ← List.length_reverse, hr, List.length_nil]
        subst h0
        simp only [SVal.saveM]
        split
        · simp only [Option.bind_eq_bind, Option.bind_some]
          obtain ⟨st₁, hs₁⟩ := save_of_find hf (SVal.array
            (SVec.ofList (((e.toList ++ sh.toList).set (uintOfNat (0 - 1)).1.toNat
              (SVal.prim (PrimTy.dflt P))).take 0))
            (SList.ofList (((e.toList ++ sh.toList).set (uintOfNat (0 - 1)).1.toNat
              (SVal.prim (PrimTy.dflt P))).drop 0)) (SVal.take_lt_bound _ hn))
          rw [hs₁, Option.bind_some, find_save_same hs₁, Option.bind_some]
          simp only [SVal.view_array, SVec.toList_ofList, List.take_zero, List.reverse_nil]
        · rfl
      | cons last tl =>
        have he : e.toList = tl.reverse ++ [last] := by
          rw [← List.reverse_reverse e.toList, hr, List.reverse_cons]
        have hn0 : n ≠ 0 := by
          intro h0; rw [← hl, he, List.length_append, List.length_singleton] at h0; omega
        have htl : tl.reverse.length = n - 1 := by
          rw [← hl, he, List.length_append, List.length_singleton]; omega
        have hget : (e.toList ++ sh.toList)[(uintOfNat (n - 1)).1.toNat]? = some last := by
          rw [hu hn0, he, List.append_assoc, List.getElem?_append_right (Nat.le_of_eq htl), htl,
            Nat.sub_self, List.singleton_append, List.getElem?_cons_zero]
        have hset : (e.toList ++ sh.toList).set (uintOfNat (n - 1)).1.toNat
            (SVal.prim (PrimTy.dflt P)) = tl.reverse ++ SVal.prim (PrimTy.dflt P) :: sh.toList := by
          rw [hu hn0, he, List.append_assoc, ← htl, List.set_append_right _ _ (Nat.le_refl _),
            Nat.sub_self, List.singleton_append, List.set_cons_zero]
        simp only [SVal.saveM, hget, Option.bind_eq_bind, Option.bind_some]
        obtain ⟨st₁, hs₁⟩ := save_of_find hf (SVal.array
          (SVec.ofList (((e.toList ++ sh.toList).set (uintOfNat (n - 1)).1.toNat
            (SVal.prim (PrimTy.dflt P))).take n))
          (SList.ofList (((e.toList ++ sh.toList).set (uintOfNat (n - 1)).1.toNat
            (SVal.prim (PrimTy.dflt P))).drop n)) (SVal.take_lt_bound _ hn))
        rw [hs₁, Option.bind_some, find_save_same hs₁, Option.bind_some]
        have htake : (tl.reverse ++ SVal.prim (PrimTy.dflt P) :: sh.toList).take n =
            tl.reverse ++ [SVal.prim (PrimTy.dflt P)] := by
          rw [List.take_append, List.take_of_length_le (by omega), htl,
            show n - (n - 1) = 1 by omega, List.take_succ_cons, List.take_zero]
        have hdrop : (tl.reverse ++ SVal.prim (PrimTy.dflt P) :: sh.toList).drop n = sh.toList := by
          rw [List.drop_append, List.drop_of_length_le (by omega), htl,
            show n - (n - 1) = 1 by omega, List.drop_succ_cons, List.drop_zero, List.nil_append]
        have hrev : (SVec.ofList (((e.toList ++ sh.toList).set (uintOfNat (n - 1)).1.toNat
            (SVal.prim (PrimTy.dflt P))).take n)).toList.reverse =
            SVal.prim (PrimTy.dflt P) :: tl := by
          rw [SVec.toList_ofList, hset, htake, List.reverse_append, List.reverse_reverse]
          rfl
        have hlast : last.defaultOf = SVal.prim (PrimTy.dflt P) := by
          cases last; exact SVal.defaultOf_prim _
        simp only [SVal.view_array, hrev, Bool.false_eq_true, ↓reduceIte, save_save hs₁, hlast]
        congr 1
        apply SVal.array_ext
        · rw [SVec.toList_ofList, SVec.toList_ofList, SVec.toList_ofList, hset, htake, he,
            List.dropLast_concat, List.dropLast_concat]
        · rw [SList.toList_ofList, SList.toList_ofList, SList.toList_ofList, hset, hdrop]

end Storage

end Solidity
