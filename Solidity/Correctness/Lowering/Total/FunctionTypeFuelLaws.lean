import Solidity.Correctness.Lowering.Total.FunctionTypeDecode

/-!
# Loop lowering: fuel laws of the function-type signature reader

`FunctionTypeDecode` reads a retained spelling with fuel (`part`, `partsWith`,
`node`, `readSig`) and leaves its fuel obligations open. They are proved here,
with those definitions unchanged:

* **monotonicity** (`part_mono`, `partsWith_mono`, `readSig_part`): a reading
  that succeeds with some fuel succeeds, with the same tree, with more;
* **ordered traversal** (`partsWith_cons`, `partsWith_eq_some_iff`,
  `partsWith_eq_none_iff`): components are read pointwise, in order, none
  dropped, and the list fails exactly when one component does;
* **refusal** (`Refused`, `part_refused`): a function-type marker `fnParts?`
  refuses, at any nesting depth inside an otherwise split spelling, makes the
  whole reading fail at every fuel (failure from too little fuel is not
  preserved: more fuel may succeed);
* **sufficient and exact fuel** (`Part.Splits`, `part_of_splits`,
  `part_lt_depth`): given each function node's actual `fnParts?` equation and
  each leaf's actual reading (`fnTy? c = false`, `leaf c = t.erase`) as
  hypotheses, fuel at least the structural depth `Part.depth` reads precisely
  the tree with annotations erased, and less fuel reads nothing;
* **the bound** (`Part.depth_le_spell`, `readSig_of_splits`,
  `readSig_spell`): the depth is at most the spelling length plus one for every
  tree, so `readSig`'s fuel suffices for a canonical spelling (`t.spell`) whose
  splits are as hypothesised.

`fnParts?` is still never computed in a proof (`String.startsWith`, `drop`,
`endsWith` do not reduce in the kernel): its equations stay hypotheses
(`Part.Splits`). An arbitrary tree need not satisfy them at its own spelling:
spellings erase information (`address payable`, mutability, the type/location
boundary) and a `named` component may be empty or contain separators. That
`fnParts? (fnTyStr ps rs ext) = some (ps, rs, ext)` on well-bracketed
components, annotation agreement, full decoder coverage and semantic binding
remain with the original decoder.
-/
namespace Solidity.Correctness.Lowering.Total.FunctionTypeDecode

/-! ## Ordered traversal -/

theorem partsWith_nil (f : String → Option (Part Unit)) : partsWith f [] = some .nil := rfl

/-- The head is read first, then the rest; the tree keeps the order. -/
theorem partsWith_cons (f : String → Option (Part Unit)) (c : String) (cs : List String) :
    partsWith f (c :: cs) = (f c).bind fun p => (partsWith f cs).map (.cons p) := by
  simp only [partsWith, Option.pure_def, Option.bind_eq_bind]
  cases f c <;> cases partsWith f cs <;> rfl

/-- Components read by `f` pointwise, in order: `P` lists `f`'s reading of
each component of `cs`, none dropped. -/
def Parts.ReadBy (f : String → Option (Part Unit)) : Parts Unit → List String → Prop
  | .nil, cs => cs = []
  | .cons p ps, cs => ∃ c cs', cs = c :: cs' ∧ f c = some p ∧ ps.ReadBy f cs'

/-- `partsWith` succeeds exactly with the pointwise, ordered reading. -/
theorem partsWith_eq_some_iff (f : String → Option (Part Unit)) :
    ∀ (cs : List String) (P : Parts Unit), partsWith f cs = some P ↔ P.ReadBy f cs
  | [], P => by cases P <;> simp [partsWith, Parts.ReadBy]
  | c :: cs, P => by
    rw [partsWith_cons]
    cases P with
    | nil =>
      simp only [Parts.ReadBy, reduceCtorEq, iff_false]
      cases f c <;> cases partsWith f cs <;> simp
    | cons p ps =>
      simp only [Parts.ReadBy, List.cons.injEq]
      constructor
      · intro h
        simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Parts.cons.injEq] at h
        obtain ⟨q, hq, qs, hqs, rfl, rfl⟩ := h
        exact ⟨c, cs, ⟨rfl, rfl⟩, hq, (partsWith_eq_some_iff f cs qs).1 hqs⟩
      · rintro ⟨_, _, ⟨rfl, rfl⟩, hp, hps⟩
        rw [hp, (partsWith_eq_some_iff f _ ps).2 hps]
        rfl

/-- The list is refused exactly when some component is. -/
theorem partsWith_eq_none_iff (f : String → Option (Part Unit)) :
    ∀ cs : List String, partsWith f cs = none ↔ ∃ c ∈ cs, f c = none
  | [] => by simp [partsWith]
  | c :: cs => by
    rw [partsWith_cons]
    cases hc : f c with
    | none => simp [hc]
    | some p =>
      have ih := partsWith_eq_none_iff f cs
      cases hcs : partsWith f cs with
      | none =>
        simp only [Option.bind_some, Option.map_none, List.mem_cons, exists_eq_or_imp, hc,
          reduceCtorEq, false_or, true_iff]
        exact ih.1 hcs
      | some P =>
        simp only [Option.bind_some, Option.map_some, reduceCtorEq, List.mem_cons,
          exists_eq_or_imp, hc, false_or, false_iff]
        intro h
        exact absurd (ih.2 h) (by simp [hcs])

/-- A reader that agrees with `f` wherever `f` succeeds reads every list
`f` reads, identically. -/
theorem partsWith_mono {f g : String → Option (Part Unit)}
    (h : ∀ c p, f c = some p → g c = some p) :
    ∀ {cs : List String} {P : Parts Unit}, partsWith f cs = some P → partsWith g cs = some P
  | [], _, hP => hP
  | c :: cs, P, hP => by
    rw [partsWith_cons] at hP ⊢
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hP
    obtain ⟨p, hp, ps, hps, rfl⟩ := hP
    rw [h c p hp, partsWith_mono h hps]
    rfl

/-! ## Monotonicity -/

/-- **More fuel reads the same.** A successful reading is kept, tree for tree,
at every larger fuel. -/
theorem part_mono : ∀ {n m : Nat} {s : String} {p : Part Unit},
    part n s = some p → n ≤ m → part m s = some p
  | 0, _, _, _, h, _ => by cases h
  | n + 1, m, s, p, h, le => by
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    by_cases isFn : fnTy? s = true
    · cases parts : fnParts? s with
      | none => rw [part_malformed isFn parts] at h; cases h
      | some x =>
        obtain ⟨ps, rs, ext⟩ := x
        rw [part_fn n parts] at h
        rw [part_fn m parts]
        simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
        obtain ⟨P, hP, R, hR, rfl⟩ := h
        have step : ∀ c q, part n c = some q → part m c = some q :=
          fun _ _ hq => part_mono hq (by omega)
        exact ⟨P, partsWith_mono step hP, R, partsWith_mono step hR, rfl⟩
    · have notFn : fnTy? s = false := by simpa using isFn
      rw [part_leaf n notFn] at h
      rw [part_leaf m notFn, h]

/-- Lists of components, read with more fuel, read the same. -/
theorem partsWith_part_mono {n m : Nat} (le : n ≤ m) {cs : List String} {P : Parts Unit}
    (h : partsWith (part n) cs = some P) : partsWith (part m) cs = some P :=
  partsWith_mono (fun _ _ hq => part_mono hq le) h

/-- `readSig`'s reading is the reader's at any fuel from the spelling length on. -/
theorem readSig_part {s : String} {p : Part Unit} (h : readSig s = some p) {n : Nat}
    (le : s.length + 1 ≤ n) : part n s = some p := by
  unfold readSig at h
  split at h
  · exact part_mono h le
  · cases h

/-! ## Refusal by `fnParts?` -/

/-- A spelling whose reading `fnParts?` refuses: a function-type marker it
does not split, or a split function type with such a component among its
parameters or returns, at any depth. The equations are hypotheses. -/
inductive Refused : String → Prop
  /-- A function-type marker `fnParts?` does not split. -/
  | malformed {c : String} : fnTy? c = true → fnParts? c = none → Refused c
  /-- A split function type with a refused parameter. -/
  | param {s c : String} {ps rs : List String} {ext : Bool} :
      fnParts? s = some (ps, rs, ext) → c ∈ ps → Refused c → Refused s
  /-- A split function type with a refused return. -/
  | ret {s c : String} {ps rs : List String} {ext : Bool} :
      fnParts? s = some (ps, rs, ext) → c ∈ rs → Refused c → Refused s

/-- **Refusal is preserved.** A refused spelling, at any depth, reads as
nothing at every fuel. -/
theorem part_refused {s : String} (h : Refused s) : ∀ n, part n s = none := by
  induction h with
  | malformed isFn parts => exact part_malformed isFn parts
  | @param s c ps rs ext parts mem _ ih =>
    intro n
    cases n with
    | zero => rfl
    | succ n =>
      rw [part_fn n parts, (partsWith_eq_none_iff _ ps).2 ⟨c, mem, ih n⟩]
      rfl
  | @ret s c ps rs ext parts mem _ ih =>
    intro n
    cases n with
    | zero => rfl
    | succ n =>
      rw [part_fn n parts, (partsWith_eq_none_iff _ rs).2 ⟨c, mem, ih n⟩]
      cases partsWith (part n) ps <;> rfl

/-- A refused component refuses every list containing it, at every fuel. -/
theorem partsWith_refused {cs : List String} {c : String} (mem : c ∈ cs) (h : Refused c)
    (n : Nat) : partsWith (part n) cs = none :=
  (partsWith_eq_none_iff _ cs).2 ⟨c, mem, part_refused h n⟩

/-- A refused spelling is not a retained signature. -/
theorem readSig_refused {s : String} (h : Refused s) : readSig s = none := by
  unfold readSig
  split
  · exact part_refused h _
  · rfl

/-! ## Structural depth and sufficient fuel -/

mutual
/-- The structural reading depth: one fuel per nesting level. -/
def Part.depth {α : Type} : Part α → Nat
  | .fn _ _ ps rs => max ps.depth rs.depth + 1
  | _ => 1
/-- The deepest component, `0` for none. -/
def Parts.depth {α : Type} : Parts α → Nat
  | .nil => 0
  | .cons c cs => max c.depth cs.depth
end

mutual
/-- The reading hypotheses of a tree at a spelling: at each function node its
actual `fnParts?` equation (flag, components in order), at each leaf that the
component is no function type and its actual `leaf` reading is the erased
leaf. -/
def Part.Splits {α : Type} : Part α → String → Prop
  | .elem e, c => fnTy? c = false ∧ leaf c = .elem e
  | .named n, c => fnTy? c = false ∧ leaf c = .named n
  | .located b l, c => fnTy? c = false ∧ leaf c = .located b l
  | .fn ext _ ps rs, s => ∃ cs ds, fnParts? s = some (cs, ds, ext) ∧ ps.Splits cs ∧ rs.Splits ds
/-- The reading hypotheses of components, pointwise and in order. -/
def Parts.Splits {α : Type} : Parts α → List String → Prop
  | .nil, cs => cs = []
  | .cons t ts, cs => ∃ c cs', cs = c :: cs' ∧ t.Splits c ∧ ts.Splits cs'
end

/-- A leaf's hypotheses give its reading at any positive fuel. -/
private theorem part_leaf_of {n : Nat} {c : String} {p : Part Unit} (notFn : fnTy? c = false)
    (h : leaf c = p) : part (n + 1) c = some p := by
  rw [part_leaf n notFn, h]

mutual
/-- **Sufficient fuel.** Under its reading hypotheses, a tree is read back,
annotations erased, with any fuel at least its structural depth. -/
theorem part_of_splits {α : Type} :
    (t : Part α) → {s : String} → {n : Nat} → t.Splits s → t.depth ≤ n →
      part n s = some t.erase
  | .elem _, _, n + 1, ⟨notFn, h⟩, _ => part_leaf_of notFn h
  | .named _, _, n + 1, ⟨notFn, h⟩, _ => part_leaf_of notFn h
  | .located _ _, _, n + 1, ⟨notFn, h⟩, _ => part_leaf_of notFn h
  | .fn _ _ ps rs, _, n + 1, ⟨cs, ds, parts, hps, hrs⟩, le => by
    have le' : max ps.depth rs.depth ≤ n := by
      simp only [Part.depth] at le; omega
    rw [part_fn n parts,
      partsWith_of_splits ps hps (Nat.le_trans (Nat.le_max_left _ _) le'),
      partsWith_of_splits rs hrs (Nat.le_trans (Nat.le_max_right _ _) le')]
    rfl
  | .elem _, _, 0, _, le => by simp [Part.depth] at le
  | .named _, _, 0, _, le => by simp [Part.depth] at le
  | .located _ _, _, 0, _, le => by simp [Part.depth] at le
  | .fn _ _ _ _, _, 0, _, le => by simp [Part.depth] at le
/-- Components under their hypotheses are read back, in order, with any fuel
at least their depth. -/
theorem partsWith_of_splits {α : Type} :
    (ts : Parts α) → {cs : List String} → {n : Nat} → ts.Splits cs → ts.depth ≤ n →
      partsWith (part n) cs = some ts.erase
  | .nil, _, _, h, _ => by cases h; rfl
  | .cons t ts, _, n, ⟨c, cs', eq, ht, hts⟩, le => by
    cases eq
    have le' : max t.depth ts.depth ≤ n := le
    rw [partsWith_cons, part_of_splits t ht (Nat.le_trans (Nat.le_max_left _ _) le'),
      partsWith_of_splits ts hts (Nat.le_trans (Nat.le_max_right _ _) le')]
    rfl
end

mutual
/-- **The depth is exact.** Under its reading hypotheses, a tree is not read
with less fuel than its structural depth. -/
theorem part_lt_depth {α : Type} :
    (t : Part α) → {s : String} → {n : Nat} → t.Splits s → n < t.depth → part n s = none
  | _, _, 0, _, _ => rfl
  | .elem _, _, n + 1, _, lt => by simp [Part.depth] at lt
  | .named _, _, n + 1, _, lt => by simp [Part.depth] at lt
  | .located _ _, _, n + 1, _, lt => by simp [Part.depth] at lt
  | .fn _ _ ps rs, _, n + 1, ⟨cs, ds, parts, hps, hrs⟩, lt => by
    have lt' : n < max ps.depth rs.depth := by
      simp only [Part.depth] at lt; omega
    rw [part_fn n parts]
    by_cases hp : n < ps.depth
    · rw [partsWith_lt_depth ps hps hp]; rfl
    · have hr : n < rs.depth := by
        rcases Nat.le_total ps.depth rs.depth with h | h
        · rw [Nat.max_eq_right h] at lt'; exact lt'
        · rw [Nat.max_eq_left h] at lt'; omega
      rw [partsWith_lt_depth rs hrs hr]
      cases partsWith (part n) cs <;> rfl
/-- Components are not read with less fuel than their depth. -/
theorem partsWith_lt_depth {α : Type} :
    (ts : Parts α) → {cs : List String} → {n : Nat} → ts.Splits cs → n < ts.depth →
      partsWith (part n) cs = none
  | .nil, _, _, _, lt => by simp [Parts.depth] at lt
  | .cons t ts, _, n, ⟨c, cs', eq, ht, hts⟩, lt => by
    cases eq
    rw [partsWith_cons]
    by_cases h : n < t.depth
    · rw [part_lt_depth t ht h]; rfl
    · have h' : n < ts.depth := by
        have lt' : n < max t.depth ts.depth := lt
        rcases Nat.le_total t.depth ts.depth with le | le
        · rw [Nat.max_eq_right le] at lt'; exact lt'
        · rw [Nat.max_eq_left le] at lt'; omega
      rw [partsWith_lt_depth ts hts h']
      cases part n c <;> rfl
end

/-- Under its reading hypotheses a tree is read exactly from its depth on. -/
theorem part_splits_iff {α : Type} {t : Part α} {s : String} (h : t.Splits s) (n : Nat) :
    part n s = some t.erase ↔ t.depth ≤ n := by
  constructor
  · intro hp
    refine Nat.le_of_not_lt fun lt => ?_
    rw [part_lt_depth t h lt] at hp
    cases hp
  · exact part_of_splits t h

/-! ## The depth bound: spelling length plus one -/

/-- `intercalate`'s length: the first piece, then a separator and a piece for
each further one (its worker is private; one unfolding is `rfl`). -/
private theorem length_intercalate_cons (s : String) :
    ∀ (a : String) (l : List String), (s.intercalate (a :: l)).length =
      a.length + (l.map fun b => s.length + b.length).sum
  | a, [] => by simp; rfl
  | a, b :: l => by
    have unfold : s.intercalate (a :: b :: l) = s.intercalate ((a ++ s ++ b) :: l) := rfl
    rw [unfold, length_intercalate_cons s _ l]
    simp only [String.length_append, List.map_cons, List.sum_cons]
    omega

private theorem length_le_intercalate_cons (s a : String) (l : List String) :
    a.length ≤ (s.intercalate (a :: l)).length := by
  rw [length_intercalate_cons]
  omega

private theorem intercalate_le_cons (s a : String) :
    ∀ l : List String, (s.intercalate l).length ≤ (s.intercalate (a :: l)).length
  | [] => by simp [String.intercalate]
  | b :: l => by
    rw [length_intercalate_cons, length_intercalate_cons]
    simp only [List.map_cons, List.sum_cons]
    omega

mutual
/-- **The depth bound.** Every tree's structural depth is at most its
spelling's length plus one. -/
theorem Part.depth_le_spell {α : Type} : (t : Part α) → t.depth ≤ t.spell.length + 1
  | .elem _ => by simp [Part.depth]
  | .named _ => by simp [Part.depth]
  | .located _ _ => by simp [Part.depth]
  | .fn ext _ ps rs => by
    have hp := Parts.depth_le_spells ps
    have hr := Parts.depth_le_spells rs
    have l₁ : "function(".length = 9 := by decide
    have l₂ : ")".length = 1 := by decide
    have l₃ : "returns(".length = 8 := by decide
    have hrs : (",".intercalate rs.spells).length ≤
        (if rs.spells.isEmpty then "" else "returns(" ++ ",".intercalate rs.spells ++ ")").length := by
      split
      · rename_i e
        rw [List.isEmpty_iff.1 e]
        exact Nat.le_refl _
      · simp only [String.length_append, l₂, l₃]
        omega
    simp only [Part.depth, Part.spell, fnTyStr, String.length_append, toString, l₁, l₂]
    rw [Nat.add_le_add_iff_right, Nat.max_le]
    constructor <;> omega
/-- Components' depth is at most their comma-separated spelling's length plus one. -/
theorem Parts.depth_le_spells {α : Type} :
    (ts : Parts α) → ts.depth ≤ (",".intercalate ts.spells).length + 1
  | .nil => by simp [Parts.depth]
  | .cons t ts => by
    have ht := Part.depth_le_spell t
    have hts := Parts.depth_le_spells ts
    have a := length_le_intercalate_cons "," t.spell ts.spells
    have b := intercalate_le_cons "," t.spell ts.spells
    simp only [Parts.depth, Parts.spells, Nat.max_def]
    split <;> omega
end

/-- **`readSig`'s fuel suffices.** A function-type spelling under a tree's
reading hypotheses, whose length plus one is at least the tree's depth, is
read back by `readSig` with annotations erased. -/
theorem readSig_of_splits {α : Type} {t : Part α} {s : String} (h : t.Splits s)
    (isFn : fnTy? s = true) (le : t.depth ≤ s.length + 1) : readSig s = some t.erase := by
  unfold readSig
  rw [if_pos isFn]
  exact part_of_splits t h le

/-- **Canonical spellings.** A function type whose own spelling satisfies its
reading hypotheses is read back by `readSig`, annotations erased. -/
theorem readSig_spell {α : Type} {ext : Bool} {a : α} {ps rs : Parts α}
    (h : (Part.fn ext a ps rs).Splits (Part.fn ext a ps rs).spell) :
    readSig (Part.fn ext a ps rs).spell = some (Part.fn ext a ps rs).erase := by
  have ⟨_, _, parts, _, _⟩ := h
  exact readSig_of_splits h (fnTy_of_parts parts) (Part.depth_le_spell _)

end Solidity.Correctness.Lowering.Total.FunctionTypeDecode
