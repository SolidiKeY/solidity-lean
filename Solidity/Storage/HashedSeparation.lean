import Solidity.Storage.HashedLayout

/-!
# Separation of struct members, mapping entries and array elements

The G27.01–G27.03 separation statements over the hashed layout of
`Solidity/Storage/HashedLayout.lean`
(`docs/feature-work/storage-hashed-layout.md`, "Checkpoint 4").

`Occ t l x`: the slot term `x` belongs to a value of type `t` laid out at `l`
(a word's own slot, a dynamic array's length slot and every element's, every
entry of a mapping). Two members of a struct, two entries of a mapping at
different keys, two elements of an array at different indices, and a
dynamic array's length and its elements occupy disjoint sets of slot terms
(`occ_fields_disjoint`, `occ_keys_disjoint`, `occ_sarr_disjoint`,
`occ_darr_disjoint`, `occ_darr_len_elem`). The proof reads a term's
ancestry, as `Solidity/Evm/Layout.lean` does for `Evm.Slot`: every term a
value at `l` occupies is reached from one in-place word `l + j`, `j < size`,
by hashing (`occ_reach`), and a term has one ancestor per depth
(`reach_unique`).

These are symbolic statements; no hash premise is used. With the region
premise and bounded offsets (`occ_bounded`) they become statements about
256-bit words (`occ_word_ne`): writing one member, entry or element does not
touch the words of another.
-/

namespace Solidity.Storage

open Solidity.Hash

namespace Loc

/-- The number of hashes a slot term nests. -/
def depth : Loc → Nat
  | root _ => 0
  | hash _ s _ => s.depth + 1
  | data s _ => s.depth + 1

theorem depth_add (l : Loc) (i : Nat) : (l.add i).depth = l.depth := by
  cases l <;> rfl

theorem add_inj {l : Loc} {i j : Nat} (h : l.add i = l.add j) : i = j := by
  cases l <;> simp only [add, root.injEq, hash.injEq, data.injEq] at h <;> omega

end Loc

/-- `Reach b x`: `x` is `b` or is obtained from `b` by hashing. -/
inductive Reach (b : Loc) : Loc → Prop
  | self : Reach b b
  | hash (k : Nat) {s : Loc} (o : Nat) : Reach b s → Reach b (.hash k s o)
  | data {s : Loc} (o : Nat) : Reach b s → Reach b (.data s o)

theorem Reach.trans {a b x : Loc} (hab : Reach a b) (hbx : Reach b x) : Reach a x := by
  induction hbx with
  | self => exact hab
  | hash k o _ ih => exact .hash k o ih
  | data o _ ih => exact .data o ih

theorem Reach.eq_or_lt {b x : Loc} (h : Reach b x) : b = x ∨ b.depth < x.depth := by
  induction h with
  | self => exact Or.inl rfl
  | hash k o _ ih =>
    right; simp only [Loc.depth]
    rcases ih with e | lt
    · rw [e]; omega
    · omega
  | data o _ ih =>
    right; simp only [Loc.depth]
    rcases ih with e | lt
    · rw [e]; omega
    · omega

/-- A term has one ancestor at each depth. -/
theorem reach_unique {b b' x : Loc} (h : Reach b x) (h' : Reach b' x)
    (hd : b.depth = b'.depth) : b = b' := by
  induction h with
  | self =>
    rcases h'.eq_or_lt with e | lt
    · exact e.symm
    · omega
  | hash k o hs ih =>
    cases h' with
    | self =>
      have hle : b.depth ≤ _ := (hs.eq_or_lt).elim (fun e => e ▸ Nat.le_refl _) Nat.le_of_lt
      simp only [Loc.depth] at hd; omega
    | hash _ _ hs' => exact ih hs'
  | data o hs ih =>
    cases h' with
    | self =>
      have hle : b.depth ≤ _ := (hs.eq_or_lt).elim (fun e => e ▸ Nat.le_refl _) Nat.le_of_lt
      simp only [Loc.depth] at hd; omega
    | data _ hs' => exact ih hs'

/-- `Occ t l x`: the slot term `x` belongs to a value of type `t` at `l`. -/
inductive Occ : STy → Loc → Loc → Prop
  | word {l : Loc} : Occ .word l l
  | field {fs : List STy} {i : Nat} {f : STy} {l x : Loc} : fs[i]? = some f →
      Occ f (l.add (STy.sizes (fs.take i))) x → Occ (.strct fs) l x
  | sarr {e : STy} {n i : Nat} {l x : Loc} : i < n → Occ e (l.add (i * e.size)) x →
      Occ (.sarr e n) l x
  | len {e : STy} {l : Loc} : Occ (.darr e) l l
  | darr {e : STy} {i : Nat} {l x : Loc} : i < lmax → Occ e (.data l (i * e.size)) x →
      Occ (.darr e) l x
  | entry {v : STy} {k : Nat} {l x : Loc} : Occ v (.hash k l 0) x → Occ (.map v) l x

theorem reach_add_hash {l : Loc} {k j : Nat} : Reach l ((Loc.hash k l 0).add j) := by
  simp only [Loc.add, Nat.zero_add]; exact .hash k j .self

theorem reach_add_data {l : Loc} {i j : Nat} : Reach l ((Loc.data l i).add j) := by
  simp only [Loc.add]; exact .data (i + j) .self

/-- Every term a value occupies is reached from one of its in-place words. -/
theorem occ_reach {t : STy} {l x : Loc} (h : Occ t l x) : ∃ j < t.size, Reach (l.add j) x := by
  induction h with
  | word => exact ⟨0, by simp only [STy.size]; omega, by rw [Loc.add_zero]; exact .self⟩
  | @field fs i f l x hf _ ih =>
    obtain ⟨j, hj, hr⟩ := ih
    have hle : STy.sizes (fs.take i) + f.size ≤ STy.sizes fs := STy.sizes_take_add_le hf
    refine ⟨STy.sizes (fs.take i) + j, by simp only [STy.size]; omega, ?_⟩
    rw [← Loc.add_add]; exact hr
  | @sarr e n i l x hi _ ih =>
    obtain ⟨j, hj, hr⟩ := ih
    have hle : i * e.size + e.size ≤ n * e.size := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
    refine ⟨i * e.size + j, by simp only [STy.size]; omega, ?_⟩
    rw [← Loc.add_add]; exact hr
  | len => exact ⟨0, by simp only [STy.size]; omega, by rw [Loc.add_zero]; exact .self⟩
  | darr _ _ ih =>
    obtain ⟨j, _, hr⟩ := ih
    refine ⟨0, by simp only [STy.size]; omega, ?_⟩
    rw [Loc.add_zero]; exact reach_add_data.trans hr
  | entry _ ih =>
    obtain ⟨j, _, hr⟩ := ih
    refine ⟨0, by simp only [STy.size]; omega, ?_⟩
    rw [Loc.add_zero]; exact reach_add_hash.trans hr

/-- Two in-place words of one base reaching a common term are the same word. -/
theorem add_eq_of_reach {l x : Loc} {i j : Nat} (h : Reach (l.add i) x) (h' : Reach (l.add j) x) :
    i = j :=
  Loc.add_inj (reach_unique h h' (by simp only [Loc.depth_add]))

theorem sizes_take_lt {f : STy} : ∀ {fs : List STy} {i i' : Nat}, i < i' → fs[i]? = some f →
    STy.sizes (fs.take i) + f.size ≤ STy.sizes (fs.take i')
  | _ :: _, 0, _ + 1, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [List.take_zero, List.take_succ_cons, STy.sizes]; omega
  | _ :: fs, i + 1, i' + 1, hlt, h => by
    simp only [List.getElem?_cons_succ] at h
    have ih : STy.sizes (fs.take i) + f.size ≤ STy.sizes (fs.take i') :=
      sizes_take_lt (by omega) h
    simp only [List.take_succ_cons, STy.sizes]; omega

/-- **G27.01, struct members.** Two different members of a struct occupy
disjoint slot terms. -/
theorem occ_fields_disjoint {fs : List STy} {i i' : Nat} {f f' : STy} {l x : Loc}
    (hf : fs[i]? = some f) (hf' : fs[i']? = some f') (hne : i ≠ i')
    (h : Occ f (l.add (STy.sizes (fs.take i))) x)
    (h' : Occ f' (l.add (STy.sizes (fs.take i'))) x) : False := by
  obtain ⟨j, hj, hr⟩ := occ_reach h
  obtain ⟨j', hj', hr'⟩ := occ_reach h'
  rw [Loc.add_add] at hr hr'
  have e : STy.sizes (fs.take i) + j = STy.sizes (fs.take i') + j' := add_eq_of_reach hr hr'
  rcases Nat.lt_or_gt_of_ne hne with lt | gt
  · have hle : STy.sizes (fs.take i) + f.size ≤ STy.sizes (fs.take i') := sizes_take_lt lt hf
    omega
  · have hle : STy.sizes (fs.take i') + f'.size ≤ STy.sizes (fs.take i) := sizes_take_lt gt hf'
    omega

/-- Elements at different indices with in-place offsets below the element size
differ. -/
theorem index_eq_of_mul_add {s i i' j j' : Nat} (hj : j < s) (hj' : j' < s)
    (h : i * s + j = i' * s + j') : i = i' := by
  rcases Nat.lt_trichotomy i i' with lt | eq | gt
  · have hle : i * s + s ≤ i' * s := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ lt
    omega
  · exact eq
  · have hle : i' * s + s ≤ i * s := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ gt
    omega

/-- **G27.03, static arrays.** Elements at different indices occupy disjoint
slot terms. -/
theorem occ_sarr_disjoint {e : STy} {i i' : Nat} {l x : Loc} (hne : i ≠ i')
    (h : Occ e (l.add (i * e.size)) x) (h' : Occ e (l.add (i' * e.size)) x) : False := by
  obtain ⟨j, hj, hr⟩ := occ_reach h
  obtain ⟨j', hj', hr'⟩ := occ_reach h'
  rw [Loc.add_add] at hr hr'
  exact hne (index_eq_of_mul_add hj hj' (add_eq_of_reach hr hr'))

/-- **G27.03, dynamic arrays.** Elements at different indices occupy disjoint
slot terms. -/
theorem occ_darr_disjoint {e : STy} {i i' : Nat} {l x : Loc} (hne : i ≠ i')
    (h : Occ e (.data l (i * e.size)) x) (h' : Occ e (.data l (i' * e.size)) x) : False := by
  obtain ⟨j, hj, hr⟩ := occ_reach h
  obtain ⟨j', hj', hr'⟩ := occ_reach h'
  have e' : Loc.data l (i * e.size + j) = Loc.data l (i' * e.size + j') :=
    reach_unique hr hr' (by simp only [Loc.depth])
  simp only [Loc.data.injEq, true_and] at e'
  exact hne (index_eq_of_mul_add hj hj' e')

/-- **G27.03, dynamic array header.** The length slot is not an element's. -/
theorem occ_darr_len_elem {e : STy} {i : Nat} {l : Loc} (h : Occ e (.data l (i * e.size)) l) :
    False := by
  obtain ⟨j, _, hr⟩ := occ_reach h
  rcases hr.eq_or_lt with eq | lt
  · have hd : ((Loc.data l (i * e.size)).add j).depth = l.depth := by rw [eq]
    simp only [Loc.add, Loc.depth] at hd; omega
  · simp only [Loc.add, Loc.depth] at lt; omega

/-- **G27.02, mappings.** Entries at different keys occupy disjoint slot terms,
for every key (as a word) and nested paths below. -/
theorem occ_keys_disjoint {v v' : STy} {k k' : Nat} {l x : Loc} (hne : k ≠ k')
    (h : Occ v (.hash k l 0) x) (h' : Occ v' (.hash k' l 0) x) : False := by
  obtain ⟨j, _, hr⟩ := occ_reach h
  obtain ⟨j', _, hr'⟩ := occ_reach h'
  have e : Loc.hash k l (0 + j) = Loc.hash k' l (0 + j') :=
    reach_unique hr hr' (by simp only [Loc.depth])
  simp only [Loc.hash.injEq] at e
  exact hne e.1

/-- A mapping's own slot is not an entry's. -/
theorem occ_map_slot_entry {v : STy} {k : Nat} {l : Loc} (h : Occ v (.hash k l 0) l) : False := by
  obtain ⟨j, _, hr⟩ := occ_reach h
  rcases hr.eq_or_lt with eq | lt
  · have hd : ((Loc.hash k l 0).add j).depth = l.depth := by rw [eq]
    simp only [Loc.add, Loc.depth] at hd; omega
  · simp only [Loc.add, Loc.depth] at lt; omega

/-! ## Words -/

/-- Occupied terms are bounded when the value is placed and its type fits. -/
theorem occ_bounded {L R : Nat} {t : STy} {l x : Loc} (h : Occ t l x) :
    t.Fits L → Placed L R t l → Loc.Bounded L R x := by
  induction h with
  | word => intro _ hp; have h0 := hp 0 (by simp only [STy.size]; omega); rwa [Loc.add_zero] at h0
  | @field fs i f l x hf _ ih =>
    intro hfit hp
    have hle : STy.sizes (fs.take i) + f.size ≤ STy.sizes fs := STy.sizes_take_add_le hf
    refine ih (STy.fits_of_mem hfit (List.mem_of_getElem? hf)) fun j hj => ?_
    rw [Loc.add_add]; exact hp _ (by simp only [STy.size]; omega)
  | @sarr e n i l x hi _ ih =>
    intro hfit hp
    have hle : i * e.size + e.size ≤ n * e.size := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
    refine ih hfit fun j hj => ?_
    rw [Loc.add_add]; exact hp _ (by simp only [STy.size]; omega)
  | len => intro _ hp; have h0 := hp 0 (by simp only [STy.size]; omega); rwa [Loc.add_zero] at h0
  | @darr e i l x hi _ ih =>
    intro hfit hp
    have hl : Loc.Bounded L R l := by
      have h0 : Loc.Bounded L R (l.add 0) := hp 0 (by simp only [STy.size]; omega)
      rwa [Loc.add_zero] at h0
    have hfit' : lmax * e.size ≤ L := hfit.1
    have hle : i * e.size + e.size ≤ lmax * e.size := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
    refine ih hfit.2 fun j hj => ?_
    simp only [Loc.add, Loc.Bounded]
    exact ⟨hl, by omega⟩
  | @entry v k l x _ ih =>
    intro hfit hp
    have hl : Loc.Bounded L R l := by
      have h0 : Loc.Bounded L R (l.add 0) := hp 0 (by simp only [STy.size]; omega)
      rwa [Loc.add_zero] at h0
    have hfit' : v.size ≤ L := hfit.1
    refine ih hfit.2 fun j hj => ?_
    simp only [Loc.add, Loc.Bounded]
    exact ⟨hl, by omega⟩

/-- Distinct occupied terms denote distinct words under the run's region
premise: the frame property of one write. With the disjointness theorems
above, a write to one member, entry or element leaves the words of every
other one unchanged. -/
theorem occ_word_ne {N L R : Nat} {H : Pre → Nat} {P : List Pre} (hH : ∀ p, H p < N)
    (hL : L ≤ N) (hR : R ≤ N) (hRD : RegionsDisjoint N L H (List.range R) P)
    {t₁ t₂ : STy} {l₁ l₂ x y : Loc}
    (hx : Occ t₁ l₁ x) (hf₁ : t₁.Fits L) (hp₁ : Placed L R t₁ l₁)
    (hy : Occ t₂ l₂ y) (hf₂ : t₂.Fits L) (hp₂ : Placed L R t₂ l₂)
    (hPx : ∀ p ∈ Loc.pres N H x, p ∈ P) (hPy : ∀ p ∈ Loc.pres N H y, p ∈ P)
    (hne : x ≠ y) : Loc.word N H x ≠ Loc.word N H y := fun e =>
  hne (Loc.word_inj hH hL hR hRD x y (occ_bounded hx hf₁ hp₁) (occ_bounded hy hf₂ hp₂) hPx hPy e)

/-- **G27.02 on words.** Under the region premise, entries of a placed mapping
at different keys have different words. -/
theorem keys_word_ne {N L R : Nat} {H : Pre → Nat} {P : List Pre} (hH : ∀ p, H p < N)
    (hL : L ≤ N) (hR : R ≤ N) (hRD : RegionsDisjoint N L H (List.range R) P)
    {v : STy} {l x y : Loc} {k k' : Nat} (hne : k ≠ k') (hf : (STy.map v).Fits L)
    (hp : Placed L R (.map v) l) (hx : Occ v (.hash k l 0) x) (hy : Occ v (.hash k' l 0) y)
    (hPx : ∀ p ∈ Loc.pres N H x, p ∈ P) (hPy : ∀ p ∈ Loc.pres N H y, p ∈ P) :
    Loc.word N H x ≠ Loc.word N H y :=
  occ_word_ne hH hL hR hRD (.entry hx) hf hp (.entry hy) hf hp hPx hPy
    fun e => occ_keys_disjoint hne hx (e ▸ hy)

end Solidity.Storage

/-- info: 'Solidity.Storage.occ_fields_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Storage.occ_fields_disjoint

/-- info: 'Solidity.Storage.occ_keys_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Storage.occ_keys_disjoint

/-- info: 'Solidity.Storage.occ_darr_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Storage.occ_darr_disjoint

/-- info: 'Solidity.Storage.occ_word_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Storage.occ_word_ne
