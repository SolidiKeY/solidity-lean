import Solidity.Calculus.DeclarationFacts

/-!
# Realizing finite typed reads

The declaration fragment reads roots, struct fields and mapping keys. Its
finite read assignments must describe actual typed storage, not independent
values for two aliases of one location. This module constructs that storage
by the interpreter's own saves; it does not substitute an abstract store.
-/

namespace Solidity

variable {C : Contract}

/-- Every save through a declared path returns, at every endpoint type. -/
theorem Path.Declared.save_exists {T U : Ty} {p : Path T U} (hp : p.Declared)
    (x : SVal T) (v : SVal U) : ∃ y, x.save p v = some y := by
  rw [SVal.save_eq_saveM]
  induction hp with
  | nil => cases x <;> exact ⟨v, rfl⟩
  | field h _ ih =>
    cases x with
    | struct fs =>
      obtain ⟨y, hy⟩ := ih (fs.get h) v
      refine ⟨.struct (fs.set h y), ?_⟩
      rw [SVal.saveM, hy]
      rfl
  | key k _ ih =>
    cases x with
    | map entries dflt =>
      rw [SVal.saveM]
      split
      · obtain ⟨y, hy⟩ := ih _ v
        rw [hy]
        exact ⟨_, rfl⟩
      · obtain ⟨y, hy⟩ := ih dflt v
        rw [hy]
        exact ⟨_, rfl⟩

/-- A declared location can be saved without a failure fallback. -/
theorem SRef.Declared.save_exists {T : Ty} {r : SRef C T} (hr : r.Declared)
    (st : Storage C) (v : SVal T) : ∃ st', st.save r v = some st' := by
  obtain ⟨x, hx⟩ := Path.Declared.save_exists hr (st.get r.hroot) v
  refine ⟨st.set r.hroot x, ?_⟩
  unfold Storage.save
  rw [hx]
  rfl

namespace ReadRealization

/-- A primitive location with the evidence that declaration reads return. -/
structure Ref (C : Contract) where
  prim : PrimTy
  ref : SRef C (.prim prim)
  declared : ref.Declared

/-- A read's value retains its Solidity primitive type. -/
abbrev Ref.Value (r : Ref C) := r.prim.Denote

/-- Save one typed read, using the proof that the actual save succeeds. -/
def Ref.write (r : Ref C) (v : r.Value) (st : Storage C) : Storage C :=
  (st.save r.ref (.prim v)).get (Option.isSome_iff_exists.2 (r.declared.save_exists st (.prim v)))

/-- The total constructor is precisely a successful interpreter save. -/
theorem Ref.write_spec (r : Ref C) (v : r.Value) (st : Storage C) :
    st.save r.ref (.prim v) = some (r.write v st) := by
  exact (Option.some_get _).symm

/-- A realized write reads back the same typed value. -/
theorem Ref.find_write (r : Ref C) (v : r.Value) (st : Storage C) :
    (r.write v st).find r.ref = some (.prim v) := Storage.find_save_same (r.write_spec v st)

/-- Read the actual storage value at a declared location. -/
def Ref.read (r : Ref C) (st : Storage C) : r.Value :=
  ((st.find r.ref).get (Option.isSome_iff_exists.2 (r.declared.find st))).view

theorem Ref.read_spec (r : Ref C) (st : Storage C) :
    st.find r.ref = some (.prim (r.read st)) := by
  obtain ⟨v, hv⟩ := r.declared.find st
  cases v with
  | prim v => simp only [Ref.read, hv, Option.get_some]; rfl

/-- Read realization uses the same observations as the typed term theory. -/
theorem Ref.obs_read (r : Ref C) (st : Storage C) : st.obs.word (.ref r.ref) = r.read st := by
  have h := congrArg (fun o => o.word .nil) (Storage.obs_find_some (r.read_spec st))
  simpa only [Obs.find_word, ObsLoc.app_nil, SVal.obs_word, SVal.findM, SVal.wordOf] using h

/-- Two different primitive references cannot be prefixes of one another,
including references whose endpoint primitive types differ. -/
theorem Ref.strip?_ne {r q : Ref C} (hne : r ≠ q) : r.ref.strip? q.ref = none := by
  cases h : r.ref.strip? q.ref with
  | none => rfl
  | some p =>
    cases r with
    | mk R rr hr =>
      cases q with
      | mk Q qr hq =>
        cases p with
        | nil =>
          have he : qr = rr := by
            have he := SRef.eq_of_strip? rr qr h
            simpa only [SRef.append_nil] using he
          cases he
          exact (hne rfl).elim

/-- Writing one primitive read frames every different primitive read. -/
theorem Ref.read_write_ne {r q : Ref C} (hne : r ≠ q) (v : r.Value) (st : Storage C) :
    q.read (r.write v st) = q.read st := by
  rw [← q.obs_read, ← q.obs_read, Storage.obs_save (r.write_spec v st)]
  have h : ObsLoc.strip? (SLoc.ref r.ref) (SLoc.ref q.ref) = none := Ref.strip?_ne hne
  simp only [Obs.save, h]

/-- Writing a read establishes its chosen value. -/
theorem Ref.read_write (r : Ref C) (v : r.Value) (st : Storage C) :
    r.read (r.write v st) = v := by
  have h := (r.read_spec (r.write v st)).symm.trans (r.find_write v st)
  exact SVal.prim.inj (Option.some.inj h)

/-- Compare typed primitive references by the interpreter's prefix test.
A primitive endpoint has no proper subpath, so a prefix is equality. -/
def Ref.beq (r q : Ref C) : Bool := (r.ref.strip? q.ref).isSome

theorem Ref.beq_iff (r q : Ref C) : r.beq q = true ↔ r = q := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    simp only [Ref.beq, Ref.strip?_ne hn, Option.isSome_none, Bool.false_eq_true] at h
  · rintro rfl
    have h := SRef.strip?_append r.ref Path.nil
    rw [SRef.append_nil] at h
    simp only [Ref.beq, h, Option.isSome_some]

instance : DecidableEq (Ref C) := fun r q =>
  if h : r.beq q = true then isTrue ((r.beq_iff q).1 h)
  else isFalse (fun he => h ((r.beq_iff q).2 he))

/-- Write exactly the finite requested footprint. Equal references receive
the same value because the valuation is a function on actual locations. -/
def realize (rd : (r : Ref C) → r.Value) : List (Ref C) → Storage C
  | [] => Storage.init C
  | r :: rs => r.write (rd r) (realize rd rs)

/-- Every requested read is preserved by finite materialization. -/
theorem realize_read (rd : (r : Ref C) → r.Value) : ∀ (rs : List (Ref C)) (r : Ref C),
    r ∈ rs → r.read (realize rd rs) = rd r
  | [], _, h => nomatch h
  | q :: rs, r, h => by
    by_cases he : q = r
    · subst q
      exact r.read_write (rd r) _
    · rw [realize, Ref.read_write_ne he]
      exact realize_read rd rs r ((List.mem_cons.mp h).resolve_left (Ne.symm he))

/-- A symbolic assignment records a typed value for each occurrence of a
read. Occurrences may name the same actual location. -/
abbrev Assignment (C : Contract) := List ((r : Ref C) × r.Value)

/-- Equal locations must receive equal values; no unbounded or untyped
machine word is admitted by an assignment. -/
def Assignment.Consistent (a : Assignment C) : Prop :=
  ∀ (r : Ref C) (v w : r.Value), ⟨r, v⟩ ∈ a → ⟨r, w⟩ ∈ a → v = w

/-- The first occurrence supplies a read's value; outside the footprint the
valuation uses its primitive type's default. The equality test is computable. -/
def Assignment.lookup : Assignment C → (r : Ref C) → r.Value
  | [], r => PrimTy.dflt r.prim
  | ⟨q, v⟩ :: a, r => if h : q = r then h ▸ v else Assignment.lookup a r

theorem Assignment.Consistent.tail {q : Ref C} {v : q.Value} {a : Assignment C}
    (h : Assignment.Consistent (⟨q, v⟩ :: a)) : a.Consistent :=
  fun r x y hx hy => h r x y (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hy)

/-- Lookup recovers every occurrence precisely when aliases agree. -/
theorem Assignment.lookup_of_mem : ∀ {a : Assignment C}, a.Consistent →
    ∀ {r : Ref C} {v : r.Value}, ⟨r, v⟩ ∈ a → Assignment.lookup a r = v
  | [], _, _, _, h => nomatch h
  | ⟨q, w⟩ :: a, hc, r, v, hm => by
    by_cases he : q = r
    · subst q
      rw [Assignment.lookup, dif_pos rfl]
      exact hc r w v (List.mem_cons_self) hm
    · rw [Assignment.lookup, dif_neg he]
      apply Assignment.lookup_of_mem hc.tail
      rcases List.mem_cons.mp hm with h | h
      · exact (he (congrArg Sigma.fst h).symm).elim
      · exact h

/-- Check the finite alias constraints without enumerating mapping keys or
the primitive value range. -/
def Assignment.consistentB (a : Assignment C) : Bool :=
  a.all fun ⟨r, v⟩ => decide (Assignment.lookup a r = v)

theorem Assignment.consistentB_iff (a : Assignment C) :
    a.consistentB = true ↔ a.Consistent := by
  simp only [Assignment.consistentB, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h r v w hv hw
    exact (h ⟨r, v⟩ hv).symm.trans (h ⟨r, w⟩ hw)
  · intro h x hx
    exact Assignment.lookup_of_mem h hx

/-- Reconstruct actual typed storage for a finite assignment. -/
def Assignment.realize (a : Assignment C) : Storage C :=
  ReadRealization.realize (Assignment.lookup a) (a.map Sigma.fst)

/-- Every consistent finite assignment has the exact requested reads in
the materialized interpreter storage, including repeated and aliased reads. -/
theorem Assignment.realize_spec {a : Assignment C} (hc : a.Consistent)
    {r : Ref C} {v : r.Value} (hm : ⟨r, v⟩ ∈ a) :
    a.realize.find r.ref = some (.prim v) := by
  have hr := realize_read (Assignment.lookup a) (a.map Sigma.fst) r (List.mem_map.mpr ⟨⟨r, v⟩, hm, rfl⟩)
  rw [Assignment.lookup_of_mem hc hm] at hr
  have hs := r.read_spec a.realize
  rw [show r.read a.realize = v from hr] at hs
  exact hs

/-- Alias consistency is exactly what finite primitive reads require of
storage. Both directions use actual typed interpreter reads. -/
theorem Assignment.realizable_iff (a : Assignment C) :
    a.Consistent ↔ ∃ st : Storage C,
      ∀ (r : Ref C) (v : r.Value), ⟨r, v⟩ ∈ a → st.find r.ref = some (.prim v) := by
  constructor
  · intro h
    exact ⟨a.realize, fun _ _ hm => Assignment.realize_spec h hm⟩
  · rintro ⟨st, hs⟩ r v w hv hw
    exact SVal.prim.inj (Option.some.inj ((hs r v hv).symm.trans (hs r w hw)))

end ReadRealization

end Solidity
