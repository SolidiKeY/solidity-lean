import Solidity.Hash.CollisionBound

/-!
# The hashed storage layout

A dependency-free model of solc's storage layout at word granularity, for
G27.05: slot terms are mapped to words through a hash parameter, and distinct
slot terms of one run denote distinct words under the per-run hash premises
(`docs/feature-work/storage-hashed-layout.md`).

* **Slot terms** (`Loc`) mirror `Solidity.Evm.Slot`: a root word, a mapping
  entry `keccak(k ‖ p) + off`, or a dynamic array's data
  `keccak(p) + off`. The preimages (`Pre`) carry the *word* of the inner
  term, as the EVM hashes it.
* **Words** (`Loc.word N H`) read a term with `N` words and a hash parameter
  `H : Pre → Nat`; no property of `H` is assumed beyond `H p < N` and the
  run's premises. `Solidity/Storage/HashedKeccak.lean` instantiates `H` with
  keccak-256 over the ABI encoding.
* **Layout** (`STy`, `STy.locate`): a word, a struct, a static array, a
  dynamic array of length below `lmax = 2^64`, or a mapping, laid out as
  solc does without packing: members consecutively, element `i` at
  `i · size e` (from the base, or from `keccak(p)` for a dynamic array), a
  mapping's value at `keccak(k ‖ p)`. `locate_bounded` proves that every
  reached word has its offset inside its region (`Loc.Bounded L R`) when the
  root type fits in `R` words and every hashed region in `L` (`STy.Fits`).
* **Separation** (`Loc.word_inj`): two bounded terms whose preimages lie in a
  run's preimage list `P` denote the same word only if they are equal,
  assuming `RegionsDisjoint N L H (List.range R) P`. The root/region cases
  are explicit: a hashed word never lands on a root word (`Covers`), regions
  at different preimages do not overlap even across the wrap-around
  (`Near`), and within one region distinct offsets below `L ≤ N` give
  distinct words. Without the offset bound two distinct terms alias
  (`word_data_alias`).

Global injectivity is not claimed: it is impossible
(`Solidity.Evm.External.no_injective_slot_encoding`); the theorems speak of
the terms of one run.
-/

namespace Solidity.Storage

open Solidity.Hash

/-- A hash preimage of the layout: a mapping entry's key `k` and the mapping's
word `w` (`k ‖ w`), or a dynamic array's word `w`. -/
inductive Pre where
  | entry (k w : Nat)
  | data (w : Nat)
  deriving DecidableEq, Repr

/-- A slot term: `root off`, `keccak(k ‖ ⟦s⟧) + off` or `keccak(⟦s⟧) + off`. -/
inductive Loc where
  | root (off : Nat)
  | hash (k : Nat) (s : Loc) (off : Nat)
  | data (s : Loc) (off : Nat)
  deriving DecidableEq, Repr

namespace Loc

/-- Adding to a slot term adds to its offset. -/
def add : Loc → Nat → Loc
  | root o, i => root (o + i)
  | hash k s o, i => hash k s (o + i)
  | data s o, i => data s (o + i)

theorem add_zero (l : Loc) : l.add 0 = l := by
  cases l <;> simp only [add, Nat.add_zero]

theorem add_add (l : Loc) (i j : Nat) : (l.add i).add j = l.add (i + j) := by
  cases l <;> simp only [add, Nat.add_assoc]

section Word
variable (N : Nat) (H : Pre → Nat)

/-- The word a slot term denotes: offsets wrap modulo `N`. -/
def word : Loc → Nat
  | root o => o % N
  | hash k s o => (H (.entry k (word s)) + o) % N
  | data s o => (H (.data (word s)) + o) % N

/-- The preimages a slot term hashes, innermost first. -/
def pres : Loc → List Pre
  | root _ => []
  | hash k s _ => pres s ++ [.entry k (word N H s)]
  | data s _ => pres s ++ [.data (word N H s)]

/-- Adding to the offset hashes nothing new. -/
theorem pres_add (l : Loc) (i : Nat) : pres N H (l.add i) = pres N H l := by
  cases l <;> rfl

end Word

/-- The offsets of a slot term stay inside their regions: a root offset below
`R` (the root words), a hashed offset below `L` (the region length). -/
def Bounded (L R : Nat) : Loc → Prop
  | root o => o < R
  | hash _ s o => Bounded L R s ∧ o < L
  | data s o => Bounded L R s ∧ o < L

/-- Within one region, distinct offsets below `N` give distinct words. -/
theorem off_eq_of_mod_eq {N a i j : Nat} (ha : a < N) (hi : i < N) (hj : j < N)
    (h : (a + i) % N = (a + j) % N) : i = j := by
  have hu : (a + i) / N < 2 := Nat.div_lt_of_lt_mul (by omega)
  have hv : (a + j) / N < 2 := Nat.div_lt_of_lt_mul (by omega)
  have eu : N * ((a + i) / N) + (a + i) % N = a + i := Nat.div_add_mod (a + i) N
  have ev : N * ((a + j) / N) + (a + j) % N = a + j := Nat.div_add_mod (a + j) N
  generalize (a + i) / N = u at hu eu
  generalize (a + j) / N = v at hv ev
  generalize (a + i) % N = m at eu h
  generalize (a + j) % N = n at ev h
  rcases (by omega : u = 0 ∨ u = 1) with rfl | rfl <;>
    rcases (by omega : v = 0 ∨ v = 1) with rfl | rfl <;> omega

/-- Without the offset bound, distinct slot terms alias: an array's data at
offset `0` and at offset `N` are one word. -/
theorem word_data_alias (N : Nat) (H : Pre → Nat) (s : Loc) (hN : 0 < N) :
    data s 0 ≠ data s N ∧ word N H (data s 0) = word N H (data s N) := by
  refine ⟨fun h => by cases h; omega, ?_⟩
  simp only [word, Nat.add_zero, Nat.add_mod_right]

section Separation
variable {N L R : Nat} {H : Pre → Nat} {P : List Pre}

/-- A hashed word never lands on a root word. -/
theorem hashed_ne_root (hH : ∀ p, H p < N) (hL : L ≤ N) (hR : R ≤ N)
    (hRD : RegionsDisjoint N L H (List.range R) P) {p : Pre} (hp : p ∈ P) {o r : Nat}
    (ho : o < L) (hr : r < R) : (H p + o) % N ≠ r % N := by
  intro h
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hr hR)] at h
  exact hRD.2 p hp r (List.mem_range.mpr hr) (covers_of_hit (hH p) hL ho h)

/-- Two hashed words at different preimages differ. -/
theorem hashed_ne_hashed (hH : ∀ p, H p < N) (hL : L ≤ N)
    (hRD : RegionsDisjoint N L H (List.range R) P) {p p' : Pre} (hp : p ∈ P) (hp' : p' ∈ P)
    (hne : p ≠ p') {o o' : Nat} (ho : o < L) (ho' : o' < L) :
    (H p + o) % N ≠ (H p' + o') % N := fun h =>
  hRD.1 p hp p' hp' hne (near_of_overlap (hH p) (hH p') hL ho ho' h)

/-- **Separation.** Under the run's region premise, two bounded slot terms
whose preimages the run hashed denote the same word only if they are the same
term. -/
theorem word_inj (hH : ∀ p, H p < N) (hL : L ≤ N) (hR : R ≤ N)
    (hRD : RegionsDisjoint N L H (List.range R) P) :
    ∀ (l₁ l₂ : Loc), Bounded L R l₁ → Bounded L R l₂ → (∀ p ∈ pres N H l₁, p ∈ P) →
      (∀ p ∈ pres N H l₂, p ∈ P) → word N H l₁ = word N H l₂ → l₁ = l₂
  | root a, root b, ha, hb, _, _, h => by
    simp only [word] at h
    simp only [Bounded] at ha hb
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
    rw [h]
  | root a, hash k s o, ha, hb, _, hP, h => by
    simp only [Bounded] at ha hb
    have hp : Pre.entry k (word N H s) ∈ P := hP _ (by simp only [pres, List.mem_append,
      List.mem_singleton, or_true])
    exact absurd h.symm (hashed_ne_root hH hL hR hRD hp hb.2 ha)
  | root a, data s o, ha, hb, _, hP, h => by
    simp only [Bounded] at ha hb
    have hp : Pre.data (word N H s) ∈ P := hP _ (by simp only [pres, List.mem_append,
      List.mem_singleton, or_true])
    exact absurd h.symm (hashed_ne_root hH hL hR hRD hp hb.2 ha)
  | hash k s o, root b, ha, hb, hP, _, h => by
    simp only [Bounded] at ha hb
    have hp : Pre.entry k (word N H s) ∈ P := hP _ (by simp only [pres, List.mem_append,
      List.mem_singleton, or_true])
    exact absurd h (hashed_ne_root hH hL hR hRD hp ha.2 hb)
  | data s o, root b, ha, hb, hP, _, h => by
    simp only [Bounded] at ha hb
    have hp : Pre.data (word N H s) ∈ P := hP _ (by simp only [pres, List.mem_append,
      List.mem_singleton, or_true])
    exact absurd h (hashed_ne_root hH hL hR hRD hp ha.2 hb)
  | hash k s o, data s' o', ha, hb, hP, hP', h => by
    simp only [Bounded] at ha hb
    have hp : Pre.entry k (word N H s) ∈ P := hP _ (by simp only [pres, List.mem_append,
      List.mem_singleton, or_true])
    have hp' : Pre.data (word N H s') ∈ P := hP' _ (by simp only [pres, List.mem_append,
      List.mem_singleton, or_true])
    exact absurd h (hashed_ne_hashed hH hL hRD hp hp' (fun e => by cases e) ha.2 hb.2)
  | data s o, hash k s' o', ha, hb, hP, hP', h => by
    simp only [Bounded] at ha hb
    have hp : Pre.data (word N H s) ∈ P := hP _ (by simp only [pres, List.mem_append,
      List.mem_singleton, or_true])
    have hp' : Pre.entry k (word N H s') ∈ P := hP' _ (by simp only [pres, List.mem_append,
      List.mem_singleton, or_true])
    exact absurd h (hashed_ne_hashed hH hL hRD hp hp' (fun e => by cases e) ha.2 hb.2)
  | hash k s o, hash k' s' o', ha, hb, hP, hP', h => by
    simp only [Bounded] at ha hb
    have hp : Pre.entry k (word N H s) ∈ P := hP _ (by simp only [pres, List.mem_append,
      List.mem_singleton, or_true])
    have hp' : Pre.entry k' (word N H s') ∈ P := hP' _ (by simp only [pres, List.mem_append,
      List.mem_singleton, or_true])
    by_cases hpe : Pre.entry k (word N H s) = Pre.entry k' (word N H s')
    · obtain ⟨rfl, hw⟩ := Pre.entry.inj hpe
      have hs : s = s' := word_inj hH hL hR hRD s s' ha.1 hb.1
        (fun p hq => hP p (by simp only [pres, List.mem_append]; exact Or.inl hq))
        (fun p hq => hP' p (by simp only [pres, List.mem_append]; exact Or.inl hq)) hw
      subst hs
      simp only [word] at h
      rw [off_eq_of_mod_eq (hH _) (by omega) (by omega) h]
    · exact absurd h (hashed_ne_hashed hH hL hRD hp hp' hpe ha.2 hb.2)
  | data s o, data s' o', ha, hb, hP, hP', h => by
    simp only [Bounded] at ha hb
    have hp : Pre.data (word N H s) ∈ P := hP _ (by simp only [pres, List.mem_append,
      List.mem_singleton, or_true])
    have hp' : Pre.data (word N H s') ∈ P := hP' _ (by simp only [pres, List.mem_append,
      List.mem_singleton, or_true])
    by_cases hpe : Pre.data (word N H s) = Pre.data (word N H s')
    · have hw : word N H s = word N H s' := Pre.data.inj hpe
      have hs : s = s' := word_inj hH hL hR hRD s s' ha.1 hb.1
        (fun p hq => hP p (by simp only [pres, List.mem_append]; exact Or.inl hq))
        (fun p hq => hP' p (by simp only [pres, List.mem_append]; exact Or.inl hq)) hw
      subst hs
      simp only [word] at h
      rw [off_eq_of_mod_eq (hH _) (by omega) (by omega) h]
    · exact absurd h (hashed_ne_hashed hH hL hRD hp hp' hpe ha.2 hb.2)

/-- The run reading: the slot terms `ls` a run reaches, bounded and with
their preimages in `P`, denote pairwise distinct words when they are
pairwise distinct terms. -/
theorem nodup_map_word (hH : ∀ p, H p < N) (hL : L ≤ N) (hR : R ≤ N)
    (hRD : RegionsDisjoint N L H (List.range R) P) {ls : List Loc}
    (hb : ∀ l ∈ ls, Bounded L R l) (hP : ∀ l ∈ ls, ∀ p ∈ pres N H l, p ∈ P)
    (hnd : ls.Nodup) : (ls.map (word N H)).Nodup := by
  refine List.pairwise_map.mpr (hnd.imp_of_mem fun h₁ h₂ hne e => hne ?_)
  exact word_inj hH hL hR hRD _ _ (hb _ h₁) (hb _ h₂) (hP _ h₁) (hP _ h₂) e

end Separation

end Loc

/-! ## The layout of a type -/

/-- solc's maximum storage array length, `2^64` (`Solidity.Evm.Lmax`). -/
def lmax : Nat := 2 ^ 64

/-- Storage types at word granularity (no packing): a word, a struct, a static
array of `n` elements, a dynamic array, a mapping. -/
inductive STy where
  | word
  | strct (fs : List STy)
  | sarr (e : STy) (n : Nat)
  | darr (e : STy)
  | map (v : STy)
  deriving Repr

mutual
/-- The number of words a value of the type occupies in place: a dynamic
array and a mapping take one (the length, resp. an unused word). -/
def STy.size : STy → Nat
  | .word => 1
  | .strct fs => STy.sizes fs
  | .sarr e n => n * e.size
  | .darr _ => 1
  | .map _ => 1

/-- The total size of a list of members. -/
def STy.sizes : List STy → Nat
  | [] => 0
  | t :: ts => t.size + STy.sizes ts
end

mutual
/-- Every hashed region inside the type fits in `L` words: a mapping's value
type, and `lmax` elements of a dynamic array's element type. -/
def STy.Fits (L : Nat) : STy → Prop
  | .word => True
  | .strct fs => STy.FitsAll L fs
  | .sarr e _ => e.Fits L
  | .darr e => lmax * e.size ≤ L ∧ e.Fits L
  | .map v => v.size ≤ L ∧ v.Fits L

/-- Every member fits. -/
def STy.FitsAll (L : Nat) : List STy → Prop
  | [] => True
  | t :: ts => t.Fits L ∧ STy.FitsAll L ts
end

/-- One step of an access path: a struct member, an array index, a mapping
key. -/
inductive Step where
  | field (i : Nat)
  | index (i : Nat)
  | key (k : Nat)
  deriving DecidableEq, Repr

/-- The type and the first word reached by an access path from a value of type
`t` at `l`; `none` for an ill-typed path or an index out of bounds (a
dynamic array's index is bounded by `lmax`, the most its length can be). -/
def STy.locate : STy → Loc → List Step → Option (STy × Loc)
  | t, l, [] => some (t, l)
  | .strct fs, l, .field i :: p =>
    match fs[i]? with
    | some t => t.locate (l.add (STy.sizes (fs.take i))) p
    | none => none
  | .sarr e n, l, .index i :: p => if i < n then e.locate (l.add (i * e.size)) p else none
  | .darr e, l, .index i :: p => if i < lmax then e.locate (.data l (i * e.size)) p else none
  | .map v, l, .key k :: p => v.locate (.hash k l 0) p
  | _, _, _ :: _ => none

theorem STy.fits_of_mem {L : Nat} : ∀ {fs : List STy} {t : STy}, STy.FitsAll L fs → t ∈ fs →
    t.Fits L
  | _ :: _, _, h, .head _ => h.1
  | _ :: _, _, h, .tail _ ht => STy.fits_of_mem h.2 ht

theorem STy.sizes_take_add_le : ∀ {fs : List STy} {i : Nat} {t : STy}, fs[i]? = some t →
    STy.sizes (fs.take i) + t.size ≤ STy.sizes fs
  | _ :: _, 0, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [List.take_zero, STy.sizes]; omega
  | f :: fs, i + 1, t, h => by
    simp only [List.getElem?_cons_succ] at h
    have ih : STy.sizes (fs.take i) + t.size ≤ STy.sizes fs := STy.sizes_take_add_le h
    simp only [List.take_succ_cons, STy.sizes]; omega

/-- A value of type `t` at `l` has all its in-place words inside their
regions. -/
def Placed (L R : Nat) (t : STy) (l : Loc) : Prop := ∀ j < t.size, Loc.Bounded L R (l.add j)

/-- **Bounded offsets.** Following a path from a placed value whose type fits
reaches a placed value whose type fits: every reached word's offset lies
inside its region. -/
theorem STy.locate_bounded {L R : Nat} :
    ∀ (t : STy) (l : Loc) (p : List Step) {t' : STy} {l' : Loc}, t.Fits L → Placed L R t l →
      t.locate l p = some (t', l') → t'.Fits L ∧ Placed L R t' l'
  | t, l, [], _, _, hf, hpl, h => by
    simp only [STy.locate, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hf, hpl⟩
  | .strct fs, l, .field i :: p, _, _, hf, hpl, h => by
    simp only [STy.locate] at h
    split at h
    · rename_i t ht
      have hle : STy.sizes (fs.take i) + t.size ≤ STy.sizes fs := STy.sizes_take_add_le ht
      refine STy.locate_bounded t _ p (STy.fits_of_mem hf (List.mem_of_getElem? ht)) ?_ h
      intro j hj
      rw [Loc.add_add]
      exact hpl _ (by simp only [STy.size]; omega)
    · cases h
  | .sarr e n, l, .index i :: p, _, _, hf, hpl, h => by
    simp only [STy.locate] at h
    split at h
    · rename_i hi
      refine STy.locate_bounded e _ p hf ?_ h
      intro j hj
      rw [Loc.add_add]
      have hle : i * e.size + e.size ≤ n * e.size := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
      exact hpl _ (by simp only [STy.size]; omega)
    · cases h
  | .darr e, l, .index i :: p, _, _, hf, hpl, h => by
    simp only [STy.locate] at h
    split at h
    · rename_i hi
      refine STy.locate_bounded e _ p hf.2 ?_ h
      intro j hj
      have hl : Loc.Bounded L R l := by
        have h0 : Loc.Bounded L R (l.add 0) := hpl 0 (by simp only [STy.size]; omega)
        rwa [Loc.add_zero] at h0
      have hle : i * e.size + e.size ≤ lmax * e.size := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
      have hfit : lmax * e.size ≤ L := hf.1
      simp only [Loc.add, Loc.Bounded]
      exact ⟨hl, by omega⟩
    · cases h
  | .map v, l, .key k :: p, _, _, hf, hpl, h => by
    simp only [STy.locate] at h
    refine STy.locate_bounded v _ p hf.2 ?_ h
    intro j hj
    have hl : Loc.Bounded L R l := by
      have h0 : Loc.Bounded L R (l.add 0) := hpl 0 (by simp only [STy.size]; omega)
      rwa [Loc.add_zero] at h0
    have hfit : v.size ≤ L := hf.1
    simp only [Loc.add, Loc.Bounded]
    exact ⟨hl, by omega⟩
  | .word, _, _ :: _, _, _, _, _, h => by cases h
  | .strct _, _, .index _ :: _, _, _, _, _, h => by cases h
  | .strct _, _, .key _ :: _, _, _, _, _, h => by cases h
  | .sarr _ _, _, .field _ :: _, _, _, _, _, h => by cases h
  | .sarr _ _, _, .key _ :: _, _, _, _, _, h => by cases h
  | .darr _, _, .field _ :: _, _, _, _, _, h => by cases h
  | .darr _, _, .key _ :: _, _, _, _, _, h => by cases h
  | .map _, _, .field _ :: _, _, _, _, _, h => by cases h
  | .map _, _, .index _ :: _, _, _, _, _, h => by cases h

/-- The contract's state is placed at root `0` when its type takes at most `R`
words. -/
theorem placed_root {L R : Nat} {t : STy} (h : t.size ≤ R) : Placed L R t (.root 0) := by
  intro j hj
  simp only [Loc.add, Loc.Bounded]
  omega

/-- **The layout separates.** For the contract's state type `t` (at most `R`
words, every hashed region fitting in `L ≤ N`), two words reached by access
paths, whose preimages the run hashed, are equal only if they are the same
slot term — under the run's region premise. -/
theorem located_word_inj {N L R : Nat} {H : Pre → Nat} {P : List Pre} (hH : ∀ p, H p < N)
    (hL : L ≤ N) (hR : R ≤ N) (hRD : RegionsDisjoint N L H (List.range R) P)
    {t : STy} (hf : t.Fits L) (ht : t.size ≤ R)
    {p₁ p₂ : List Step} {t₁ t₂ : STy} {l₁ l₂ : Loc}
    (h₁ : t.locate (.root 0) p₁ = some (t₁, l₁)) (h₂ : t.locate (.root 0) p₂ = some (t₂, l₂))
    {j₁ j₂ : Nat} (hj₁ : j₁ < t₁.size) (hj₂ : j₂ < t₂.size)
    (hP₁ : ∀ p ∈ Loc.pres N H l₁, p ∈ P) (hP₂ : ∀ p ∈ Loc.pres N H l₂, p ∈ P)
    (h : Loc.word N H (l₁.add j₁) = Loc.word N H (l₂.add j₂)) : l₁.add j₁ = l₂.add j₂ := by
  have hb₁ : Placed L R t₁ l₁ := (STy.locate_bounded t _ p₁ hf (placed_root ht) h₁).2
  have hb₂ : Placed L R t₂ l₂ := (STy.locate_bounded t _ p₂ hf (placed_root ht) h₂).2
  refine Loc.word_inj hH hL hR hRD _ _ (hb₁ j₁ hj₁) (hb₂ j₂ hj₂) ?_ ?_ h
  · rw [Loc.pres_add]; exact hP₁
  · rw [Loc.pres_add]; exact hP₂

end Solidity.Storage

/-- info: 'Solidity.Storage.Loc.word_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Storage.Loc.word_inj

/-- info: 'Solidity.Storage.located_word_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Storage.located_word_inj
