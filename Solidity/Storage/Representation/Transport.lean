import Solidity.Storage.Representation.Arrays
import Solidity.Theory.Typed.Obs.Values

/-! Finite touched-set transport through the committed `Loc.word`.
All hash/region conditions below are exactly the existing per-run conditions.
There is no injectivity claim outside the explicitly covered touched list. -/
namespace Solidity.Storage.Representation

open Solidity.Hash

abbrev WordStore : Type := Nat → Semantics.Word

/-- A bundle of existing conditions, not a new cryptographic premise. -/
structure FiniteRun (N L R : Nat) (H : Pre → Nat) (P : List Pre) (touched : List Loc) : Prop where
  hash_bound : ∀ p, H p < N
  region_bound : L ≤ N
  root_bound : R ≤ N
  regions : RegionsDisjoint N L H (List.range R) P
  bounded : ∀ l ∈ touched, Loc.Bounded L R l
  covered : ∀ l ∈ touched, ∀ p ∈ Loc.pres N H l, p ∈ P

/-- The numeric store agrees at exactly the finite covered symbolic locations. -/
def Transport (N : Nat) (H : Pre → Nat) (touched : List Loc) (w : Store) (m : WordStore) : Prop :=
  ∀ l ∈ touched, m (Loc.word N H l) = w l

theorem FiniteRun.word_inj {N L R : Nat} {H : Pre → Nat} {P : List Pre} {xs : List Loc}
    (run : FiniteRun N L R H P xs) {a b : Loc} (ha : a ∈ xs) (hb : b ∈ xs)
    (eq : Loc.word N H a = Loc.word N H b) : a = b :=
  Loc.word_inj run.hash_bound run.region_bound run.root_bound run.regions a b
    (run.bounded a ha) (run.bounded b hb) (run.covered a ha) (run.covered b hb) eq

theorem FiniteRun.restrict {N L R : Nat} {H : Pre → Nat} {P : List Pre} {xs ys : List Loc}
    (run : FiniteRun N L R H P xs) (subset : ∀ l ∈ ys, l ∈ xs) : FiniteRun N L R H P ys :=
  ⟨run.hash_bound, run.region_bound, run.root_bound, run.regions,
    fun l hl => run.bounded l (subset l hl), fun l hl => run.covered l (subset l hl)⟩

theorem Transport.restrict {N : Nat} {H : Pre → Nat} {xs ys : List Loc} {w : Store} {m : WordStore}
    (h : Transport N H xs w m) (subset : ∀ l ∈ ys, l ∈ xs) : Transport N H ys w m :=
  fun l hl => h l (subset l hl)

/-- Realize a finite symbolic observation set while preserving all other words.
This is a witness constructor, never a definition of source reads. -/
def realize (N : Nat) (H : Pre → Nat) (base : WordStore) (w : Store) : List Loc → WordStore
  | [] => base
  | l :: ls => fun a => if a = Loc.word N H l then w l else realize N H base w ls a

theorem realize_transport {N : Nat} {H : Pre → Nat} (base : WordStore) (w : Store)
    (xs : List Loc)
    (injective : ∀ a ∈ xs, ∀ b ∈ xs, Loc.word N H a = Loc.word N H b → a = b) :
    Transport N H xs w (realize N H base w xs) := by
  induction xs with
  | nil => intro l hl; cases hl
  | cons a rest ih =>
    intro l hl
    rcases List.mem_cons.mp hl with eq | inside
    · subst l
      exact if_pos rfl
    · by_cases eq : Loc.word N H l = Loc.word N H a
      · have same : l = a := injective l (List.mem_cons.mpr (Or.inr inside)) a
          (List.mem_cons.mpr (Or.inl rfl)) eq
        subst l
        exact if_pos rfl
      · simp only [realize, if_neg eq]
        apply ih (fun x hx y hy he => injective x (List.mem_cons.mpr (Or.inr hx)) y
          (List.mem_cons.mpr (Or.inr hy)) he) l inside

/-- An inhabited numeric representation exists for every covered finite run. -/
theorem transport_exists {N L R : Nat} {H : Pre → Nat} {P : List Pre} {xs : List Loc}
    (run : FiniteRun N L R H P xs) (base : WordStore) (w : Store) :
    ∃ m, Transport N H xs w m ∧
      ∀ a, a ∉ xs.map (Loc.word N H) → m a = base a := by
  refine ⟨realize N H base w xs, realize_transport base w xs
    (fun a ha b hb eq => run.word_inj ha hb eq), ?_⟩
  intro a outside
  induction xs with
  | nil => rfl
  | cons l rest ih =>
    have ne : a ≠ Loc.word N H l := by
      intro eq
      exact outside (List.mem_map.mpr ⟨l, List.mem_cons_self, eq.symm⟩)
    simp only [realize, if_neg ne]
    apply ih
    · exact run.restrict (fun x hx => List.mem_cons.mpr (Or.inr hx))
    · intro member
      exact outside (List.mem_map.mpr (by
        obtain ⟨x, hx, eq⟩ := List.mem_map.mp member
        exact ⟨x, List.mem_cons.mpr (Or.inr hx), eq⟩))

/-- Extending observation coverage preserves every already related observation.
The region premise is required for the extended run, not inferred from its prefix. -/
theorem transport_extend {N L R : Nat} {H : Pre → Nat} {P : List Pre} {xs ys : List Loc}
    (run : FiniteRun N L R H P (xs ++ ys)) {w : Store} {base : WordStore}
    (initial : Transport N H xs w base) :
    ∃ m, Transport N H (xs ++ ys) w m ∧
      (∀ x ∈ xs, m (Loc.word N H x) = base (Loc.word N H x)) ∧
      (∀ a, a ∉ (xs ++ ys).map (Loc.word N H) → m a = base a) := by
  obtain ⟨m, represented, outside⟩ := transport_exists run base w
  exact ⟨m, represented, fun x hx =>
    (represented x (List.mem_append.mpr (Or.inl hx))).trans (initial x hx).symm, outside⟩

/-- A numeric write at the interpreted word. -/
def writeWord (m : WordStore) (a : Nat) (v : Semantics.Word) : WordStore :=
  fun b => if b = a then v else m b

/-- One covered write commutes with finite transport, including all frames. -/
theorem transport_write {N L R : Nat} {H : Pre → Nat} {P : List Pre} {xs : List Loc}
    (run : FiniteRun N L R H P xs) {w : Store} {m : WordStore}
    (h : Transport N H xs w m) (l : Loc) (member : l ∈ xs) (v : Semantics.Word) :
    Transport N H xs (write w l v) (writeWord m (Loc.word N H l) v) := by
  intro x hx
  by_cases eq : x = l
  · subst x
    rw [write_same]
    exact if_pos rfl
  · rw [write_other w l x v eq]
    have ne : Loc.word N H x ≠ Loc.word N H l := fun same => eq (run.word_inj hx member same)
    simp only [writeWord, if_neg ne]
    exact h x hx

/-- Every finite sequence of covered writes commutes with transport. -/
theorem transport_sequence {N L R : Nat} {H : Pre → Nat} {P : List Pre} {xs : List Loc}
    (run : FiniteRun N L R H P xs) {w : Store} {m : WordStore}
    (initial : Transport N H xs w m) (updates : List (Loc × Semantics.Word))
    (covered : ∀ op ∈ updates, op.1 ∈ xs) :
    Transport N H xs
      (updates.foldl (fun store op => write store op.1 op.2) w)
      (updates.foldl (fun store op => writeWord store (Loc.word N H op.1) op.2) m) := by
  induction updates generalizing w m with
  | nil => exact initial
  | cons op rest ih =>
    simp only [List.foldl_cons]
    exact ih (transport_write run initial op.1 (covered op List.mem_cons_self) op.2)
      (fun next member => covered next (List.mem_cons.mpr (Or.inr member)))

/-- Overlapping numeric observations must agree even without a region premise.
Negative controls use this to expose the need for finite separation. -/
theorem transport_alias_consistent {N : Nat} {H : Pre → Nat} {xs ys : List Loc}
    {w v : Store} {m : WordStore} {x y : Loc}
    (hx : Transport N H xs w m) (hy : Transport N H ys v m)
    (mx : x ∈ xs) (my : y ∈ ys) (alias : Loc.word N H x = Loc.word N H y) :
    w x = v y := (hx x mx).symm.trans ((congrArg m alias).trans (hy y my))

/-- Numeric writes frame every address outside their finite image. -/
theorem sequence_outside_frame (N : Nat) (H : Pre → Nat) (m : WordStore)
    (updates : List (Loc × Semantics.Word)) (a : Nat)
    (outside : ∀ op ∈ updates, a ≠ Loc.word N H op.1) :
    (updates.foldl (fun store op => writeWord store (Loc.word N H op.1) op.2) m) a = m a := by
  induction updates generalizing m with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.foldl_cons]
    exact (ih (writeWord m (Loc.word N H op.1) op.2)
      (fun next member => outside next (List.mem_cons.mpr (Or.inr member)))).trans
      (if_neg (outside op List.mem_cons_self))

/-- Abstract subtree replacement is transported only on the selected finite set. -/
theorem transport_patch {N L R : Nat} {H : Pre → Nat} {P : List Pre} {xs : List Loc}
    (run : FiniteRun N L R H P xs) (base : WordStore) (w replacement : Store)
    (t : STy) (l : Loc) :
    ∃ m, Transport N H xs (patch w replacement t l) m ∧
      ∀ a, a ∉ xs.map (Loc.word N H) → m a = base a :=
  transport_exists run base (patch w replacement t l)

/-- Starting from a related store, finite patch realization preserves every
covered cell outside the symbolic target and every word outside the image. -/
theorem transport_patch_frames {N L R : Nat} {H : Pre → Nat} {P : List Pre} {xs : List Loc}
    (run : FiniteRun N L R H P xs) {base : WordStore} {w : Store}
    (initial : Transport N H xs w base) (replacement : Store) (t : STy) (l : Loc) :
    ∃ m, Transport N H xs (patch w replacement t l) m ∧
      (∀ x ∈ xs, ¬ Occ t l x → m (Loc.word N H x) = base (Loc.word N H x)) ∧
      (∀ a, a ∉ xs.map (Loc.word N H) → m a = base a) := by
  obtain ⟨m, represented, outside⟩ := transport_patch run base w replacement t l
  exact ⟨m, represented, fun x hx apart =>
    (represented x hx).trans ((patch_outside w replacement t l x apart).trans (initial x hx).symm),
    outside⟩

/-- Failed source reads have an exact presence observation independently of memory. -/
theorem source_failed_presence {T U : Ty} {source : SVal T} {path : Path T U}
    (missing : source.find path = none) : source.obs.has path = false := by
  rw [SVal.obs_has, ← SVal.find_eq_findM, missing]
  rfl

/-- The existing source observation returns its typed default for a missing word.
This does not authorize reading an unguarded numeric cell at that path. -/
theorem source_failed_word_default {T : Ty} {p : PrimTy} {source : SVal T}
    {path : Path T (.prim p)} (missing : source.find path = none) :
    source.obs.word path = PrimTy.dflt p := by
  rw [SVal.obs_word, ← SVal.find_eq_findM, missing]
  rfl

/-- Exact existing source word observation, at a represented successful read.
Callers supply the independently proved source/layout read witness. -/
theorem source_word_observation {T : Ty} {p : PrimTy} {source : SVal T}
    {path : Path T (.prim p)} {v : p.Denote} {l : Loc} {w : Store}
    {N : Nat} {H : Pre → Nat} {xs : List Loc} {m : WordStore}
    (found : source.find path = some (.prim v)) (represented : ValueRep (.prim v) .word l w)
    (transported : Transport N H xs w m) (covered : l ∈ xs) :
    m (Loc.word N H l) = PrimTy.toWord (source.obs.word path) := by
  have observed : source.obs.word path = v := by
    rw [SVal.obs_word, ← SVal.find_eq_findM, found]
    rfl
  rw [observed]
  exact (transported l covered).trans (scalar_read represented)

/-- Exact existing source length observation at a represented array header. -/
theorem source_length_observation {T E : Ty} {source : SVal T}
    {path : Path T (.ref (.array E))} {n : Nat} {vs : SVec E n} {sh : SList E}
    {hn : n < 2 ^ 256} {t : STy} {l : Loc} {w : Store}
    {N : Nat} {H : Pre → Nat} {xs : List Loc} {m : WordStore}
    (found : source.find path = some (.array vs sh hn))
    (represented : ValueRep (.array vs sh hn) (.darr t) l w)
    (transported : Transport N H xs w m) (covered : l ∈ xs) :
    (m (Loc.word N H l)).val = source.obs.len path := by
  have observed : source.obs.len path = n := by
    rw [SVal.obs_len, ← SVal.find_eq_findM, found]
    rfl
  rw [observed]
  exact (congrArg Subtype.val (transported l covered)).trans (array_header represented)

end Solidity.Storage.Representation
