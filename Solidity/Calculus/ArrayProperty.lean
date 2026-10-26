import Solidity.Calculus.QuantHoist
import Solidity.Calculus.QueryReduction

/-!
# The array property fragment, instantiated (M7, step 5)

A universal block in a negative position whose body reads mappings at its
variables (`(∀ k. k < 10 → balances[k] == 0) → balances[5] == 0`) is
decided as Bradley, Manna and Sipma decide it: replaced by its instances
at the index set `U`, the goal's ground keys of those mappings and the
guards' ground operands with their successors, and `0`; the instance is
decided by the quantified pipeline.

* **Sound** (`apfInst_sound`): the block implies each instance, and it
  stands where the formula is antitone in it.
* **Exact** (`apfInst_refute`): from a state where the instantiated body
  fails, a state where the body fails: each mapping read at a block
  variable is rebuilt (`MRoot.surgery`) so that its key `i` holds what key
  `⌊i⌋` held, `⌊i⌋` the largest value of the index set at most `i`
  (`floorIn`), or its largest value where `i` lies past the second largest
  and the largest bounds no strict guard (`lastIn`).  Reads at the index
  set keep their values, so everything outside the blocks reads as before
  (`ApfTm.eval_rel`); a guard true at `i` is true at `⌊i⌋` (`GuardP.mono`:
  guards compare a variable with a ground term, or two variables by `≤`,
  `≥`, `==`, never `<`), so each block holds by its instance at `⌊i⌋`.
  A ground operand may halt (`k < x - 1`): a guard true at the keys
  returned there, so its comparisons return at the floors; but a `||`
  whose left operand was false at the keys reads that operand at the
  floors too, where a `&&` inside it may evaluate a halting right operand
  it skipped at the keys.  So such a right operand must be total
  (`GuardP`'s `ds`, `GuardP.floors`, `GuardP.defined`).

The fragment (`apfPrep`): roots of any type, read along their own paths
(`ApfTm.rroot`, `rkeyU`, `rkey`, `rfield`, `rword`).  Along a root's
mappings every `uint` key is floored (`FloorShape.of`: `floor` at a
`mapping(uint => V)`, `outer` at a mapping keyed by another type, `keep`
past the mappings): read there at a block variable or at a ground term of
the index set mentioning no binder (`m[k]`, `m[o][k]`, `m[i][3]`,
`m[3][k]` beside `m[k][3]`, `accs[k].v`); a key of another type
(`owed[a][k]`), and every key past a member, any term of the fragment with
no block variable (`ApfTm.Rel`).  The rebuilt root holds at each floored
key what the key's floor held, the whole value under it copied
(`FloorShape.rebuild`), so a read reads at its keys' floors
(`FloorShape.rebuild_word`, `SRef.floorRef`).  Block variables of type `uint`,
compared in guards (atoms in negative positions of the block body); every
other read of such a root outside the fragment.  Nested mappings `m[i][j]`
with two bound indices on one path are outside (a decision recorded in
`docs/automation.md`, M7).

A rebuilt mapping lists one entry per key below `lastBound`: the index
set's second largest value plus one where its largest value bounds no
strict guard (the keys past it read the largest value's word, the
mapping's default), the largest value otherwise.  So a refutation whose
solver places one key far (`x > 2^200`) lists a dozen entries; one whose
two largest values are both far still lists about the second.  No
construction is polynomial in the index set in general: a mapping lists
its entries one key at a time with a single default, and a sorted mapping
(`∀ i j. i <= j → m[i] <= m[j]`) read at three far keys `a < b < c` with
increasing words has, in every state that refutes such a leaf, the keys
between `a` and `b` listed or those past `c`.
-/

namespace Solidity.Decide

open Semantics ReadRealization

variable {C : Contract}

/-! ## The mappings rebuilt -/

/-- **How a root the blocks read is rebuilt**: along its mappings each
`uint` key floored (`floor`), any other key kept (`outer`); past them (a
struct, an array, a word) the value copied whole (`keep`). -/
inductive FloorShape : Ty → Type where
  | keep (T : Ty) : FloorShape T
  | floor {V : Ty} (s : FloorShape V) : FloorShape (.ref (.mapping .uint V))
  | outer (K : PrimTy) {V : Ty} (s : FloorShape V) : FloorShape (.ref (.mapping K V))

/-- **The shape of a type**: every `uint` key along its mappings floored. -/
def FloorShape.of : (T : Ty) → FloorShape T
  | .ref (.mapping .uint V) => .floor (FloorShape.of V)
  | .ref (.mapping K V) => .outer K (FloorShape.of V)
  | T => .keep T

theorem FloorShape.of_mapping_ne {K : PrimTy} {V : Ty} (h : K ≠ .uint) :
    FloorShape.of (.ref (.mapping K V)) = .outer K (FloorShape.of V) := by
  cases K
  · rfl
  · exact absurd rfl h
  · rfl

theorem FloorShape.of_struct (s : Name) : FloorShape.of (.ref (.struct s)) = .keep _ := rfl

/-- A root the blocks read. -/
structure MRoot (C : Contract) where
  name : Name
  ty : Ty
  h : C.rootType name = some ty

/-- The largest `uint`. -/
def uintMax : PrimTy.uint.Denote := uintOfNat (2 ^ 256 - 1)

/-- A mapping's value at a key: its entry, or its default. -/
def entryAt {K : PrimTy} {V : Ty} (m : SMap K V) (d : SVal V) (k : K.Denote) : SVal V :=
  (lookupBy k m.toList).getD d

/-- **The value rebuilt**: at a floored mapping the key `k` holds what
`f k` held, one entry per key below `top`, the default `f`'s at the largest
key; an outer mapping's entries and default rebuilt; the rest copied. -/
def FloorShape.rebuild (f : PrimTy.uint.Denote → PrimTy.uint.Denote) (top : Nat) :
    {T : Ty} → FloorShape T → SVal T → SVal T
  | _, .keep _, v => v
  | _, .floor s, .map m d => SVal.map (SMap.ofList ((List.range top).map fun j =>
      (uintOfNat j, s.rebuild f top (entryAt m d (f (uintOfNat j))))))
      (s.rebuild f top (entryAt m d (f uintMax)))
  | _, .outer _ s, .map m d =>
    SVal.map (SMap.ofList (m.toList.map fun e => (e.1, s.rebuild f top e.2))) (s.rebuild f top d)

/-- **A path's keys at their floors**: `f` at each floored mapping, the
rest kept. -/
def FloorShape.floorPath (f : PrimTy.uint.Denote → PrimTy.uint.Denote) :
    {T U : Ty} → FloorShape T → Path T U → Path T U
  | _, _, .floor s, .key k p => .key (f k) (s.floorPath f p)
  | _, _, .outer _ s, .key k p => .key k (s.floorPath f p)
  | _, _, _, p => p

/-- The shape a path reaches. -/
def FloorShape.follow : {T U : Ty} → FloorShape T → Path T U → FloorShape U
  | _, _, .floor s, .key _ p => s.follow p
  | _, _, .outer _ s, .key _ p => s.follow p
  | _, _, .keep _, _ => .keep _
  | _, _, s, .nil => s

theorem FloorShape.floorPath_nil (f : PrimTy.uint.Denote → PrimTy.uint.Denote) {T : Ty} (s : FloorShape T) :
    s.floorPath f .nil = .nil := by
  cases s <;> rfl

theorem FloorShape.follow_nil {T : Ty} (s : FloorShape T) : s.follow .nil = s := by
  cases s <;> rfl

theorem FloorShape.floorPath_keep (f : PrimTy.uint.Denote → PrimTy.uint.Denote) {T U : Ty} (p : Path T U) :
    (FloorShape.keep T).floorPath f p = p := by
  cases p <;> rfl

theorem FloorShape.follow_keep {T U : Ty} (p : Path T U) : (FloorShape.keep T).follow p = .keep U := by
  cases p <;> rfl

theorem FloorShape.floorPath_append (f : PrimTy.uint.Denote → PrimTy.uint.Denote) :
    ∀ {T U W : Ty} (s : FloorShape T) (p : Path T U) (q : Path U W),
      s.floorPath f (p.append q) = (s.floorPath f p).append ((s.follow p).floorPath f q)
  | _, _, _, s, .nil, q => by rw [Path.append_nil, s.floorPath_nil f, s.follow_nil, Path.append_nil]
  | _, _, _, .keep _, .field h p, q | _, _, _, .keep _, .at _ p, q | _, _, _, .keep _, .atF _ p, q
  | _, _, _, .keep _, .key _ p, q => by
    rw [FloorShape.floorPath_keep, FloorShape.floorPath_keep, FloorShape.follow_keep, FloorShape.floorPath_keep]
  | _, _, _, .floor s, .key k p, q => by
    rw [Path.append_key]
    show Path.key (f k) (s.floorPath f (p.append q)) = (Path.key (f k) (s.floorPath f p)).append _
    rw [Path.append_key, FloorShape.floorPath_append f s p q]
    rfl
  | _, _, _, .outer _ s, .key k p, q => by
    rw [Path.append_key]
    show Path.key k (s.floorPath f (p.append q)) = (Path.key k (s.floorPath f p)).append _
    rw [Path.append_key, FloorShape.floorPath_append f s p q]
    rfl

theorem FloorShape.follow_append :
    ∀ {T U W : Ty} (s : FloorShape T) (p : Path T U) (q : Path U W),
      s.follow (p.append q) = (s.follow p).follow q
  | _, _, _, s, .nil, q => by rw [Path.append_nil, s.follow_nil]
  | _, _, _, .keep _, .field h p, q | _, _, _, .keep _, .at _ p, q | _, _, _, .keep _, .atF _ p, q
  | _, _, _, .keep _, .key _ p, q => by
    rw [FloorShape.follow_keep, FloorShape.follow_keep, FloorShape.follow_keep]
  | _, _, _, .floor s, .key k p, q => by
    rw [Path.append_key]
    exact FloorShape.follow_append s p q
  | _, _, _, .outer _ s, .key k p, q => by
    rw [Path.append_key]
    exact FloorShape.follow_append s p q

/-- A reference at its floors. -/
def _root_.Solidity.SRef.floorRef (f : PrimTy.uint.Denote → PrimTy.uint.Denote) {U : Ty} (r : SRef C U) :
    SRef C U :=
  ⟨r.root, r.hroot, (FloorShape.of r.ty).floorPath f r.path⟩

/-- **A root rebuilt.** -/
def MRoot.surgery (R : MRoot C) (f : PrimTy.uint.Denote → PrimTy.uint.Denote) (top : Nat)
    (st : Storage C) : Storage C :=
  st.set R.h ((FloorShape.of R.ty).rebuild f top (st.get R.h))

theorem word_of_get {st st' : Storage C} {P : PrimTy} (r : SRef C (.prim P))
    (h : st'.get r.hroot = st.get r.hroot) : st'.obs.word (.ref r) = st.obs.word (.ref r) := by
  rw [Storage.obs_word_ref, Storage.obs_word_ref, h]

/-- Another root reads as before. -/
theorem MRoot.surgery_other (R : MRoot C) (f : PrimTy.uint.Denote → PrimTy.uint.Denote) (top : Nat)
    (st : Storage C) {P : PrimTy} (r : SRef C (.prim P)) (hr : r.root ≠ R.name) :
    (R.surgery f top st).obs.word (.ref r) = st.obs.word (.ref r) :=
  word_of_get r (SFields.get_set_ne st R.h r.hroot (Ne.symm hr) _)

theorem lookupBy_map_some {V : Type} (key : Nat → PrimTy.uint.Denote) (w : PrimTy.uint.Denote → V)
    (k : PrimTy.uint.Denote) : ∀ l : List Nat, (∃ j ∈ l, key j = k) →
      lookupBy k (l.map fun j => (key j, w (key j))) = some (w k)
  | [], ⟨_, h, _⟩ => nomatch h
  | j :: l, h => by
    rw [List.map_cons, lookupBy]
    by_cases e : k = key j
    · rw [if_pos e, e]
    · rw [if_neg e]
      obtain ⟨j', hj', hk⟩ := h
      rcases List.mem_cons.1 hj' with rfl | hj'
      · exact absurd hk.symm e
      · exact lookupBy_map_some key w k l ⟨j', hj', hk⟩

theorem lookupBy_map_none {V : Type} (key : Nat → PrimTy.uint.Denote) (w : PrimTy.uint.Denote → V)
    (k : PrimTy.uint.Denote) : ∀ l : List Nat, (∀ j ∈ l, key j ≠ k) →
      lookupBy k (l.map fun j => (key j, w (key j))) = none
  | [], _ => rfl
  | j :: l, h => by
    rw [List.map_cons, lookupBy, if_neg (fun e => h j List.mem_cons_self e.symm)]
    exact lookupBy_map_none key w k l fun j' hj' => h j' (List.mem_cons_of_mem _ hj')

/-- A lookup in the entries with their values mapped. -/
theorem lookupBy_mapSnd {κ V W : Type} [DecidableEq κ] (F : V → W) (k : κ) :
    ∀ l : List (κ × V), lookupBy k (l.map fun e => (e.1, F e.2)) = (lookupBy k l).map F
  | [] => rfl
  | (k', v) :: l => by
    rw [List.map_cons, lookupBy, lookupBy]
    by_cases e : k = k'
    · rw [if_pos e, if_pos e]; rfl
    · rw [if_neg e, if_neg e]; exact lookupBy_mapSnd F k l

theorem uintVal_bounds (k : PrimTy.uint.Denote) : 0 ≤ k.1 ∧ k.1 < ((2 ^ 256 : Nat) : Int) := by
  have := k.2
  simp only [PrimTy.inRange, decide_eq_true_eq] at this
  exact this

theorem uintOfNat_toNat (k : PrimTy.uint.Denote) : uintOfNat k.1.toNat = k := by
  have hk := uintVal_bounds k
  apply Subtype.ext
  rw [uintOfNat_val (by omega)]
  omega

theorem lookupBy_range (top : Nat) {V : Type} (w : PrimTy.uint.Denote → V) (k : PrimTy.uint.Denote) :
    lookupBy k ((List.range top).map fun j => (uintOfNat j, w (uintOfNat j))) =
      if k.1.toNat < top then some (w k) else none := by
  split
  · exact lookupBy_map_some uintOfNat w k _ ⟨k.1.toNat, List.mem_range.2 (by assumption), uintOfNat_toNat k⟩
  · rename_i hn
    refine lookupBy_map_none uintOfNat w k _ fun j hj e => hn ?_
    have hj := List.mem_range.1 hj
    by_cases hb : j < 2 ^ 256
    · have := uintOfNat_val hb
      rw [e] at this
      omega
    · have : (uintOfNat j).1 = 0 := by simp only [uintOfNat, dif_neg hb]; rfl
      rw [e] at this
      omega

theorem uintMax_val : uintMax.1 = ((2 ^ 256 - 1 : Nat) : Int) := uintOfNat_val (by omega)

/-- **A rebuilt value reads at a path what the old one read at its
floors**, where `f` is constant past `top`. -/
theorem FloorShape.rebuild_word (f : PrimTy.uint.Denote → PrimTy.uint.Denote) (top : Nat)
    (hf : ∀ k : PrimTy.uint.Denote, top ≤ k.1.toNat → f k = f uintMax) :
    ∀ {T : Ty} (s : FloorShape T) (v : SVal T) {P : PrimTy} (q : Path T (.prim P)),
      SVal.wordOf ((s.rebuild f top v).findM q) = SVal.wordOf (v.findM (s.floorPath f q))
  | _, .keep _, v, _, q => by rw [FloorShape.floorPath_keep]; rfl
  | _, .floor s, .map m d, _, q => by
    cases q with
    | key k q' =>
      simp only [FloorShape.rebuild, FloorShape.floorPath, SVal.findM, SMap.toList_ofList]
      rw [lookupBy_range top (fun k => s.rebuild f top (entryAt m d (f k))) k]
      by_cases hk : k.1.toNat < top
      · rw [if_pos hk]
        dsimp only
        rw [FloorShape.rebuild_word f top hf s _ q']
        unfold entryAt
        cases lookupBy (f k) m.toList <;> rfl
      · rw [if_neg hk]
        dsimp only
        rw [← hf k (by omega), FloorShape.rebuild_word f top hf s _ q']
        unfold entryAt
        cases lookupBy (f k) m.toList <;> rfl
  | _, .outer _ s, .map m d, _, q => by
    cases q with
    | key o q' =>
      simp only [FloorShape.rebuild, FloorShape.floorPath, SVal.findM, SMap.toList_ofList]
      rw [lookupBy_mapSnd (s.rebuild f top) o m.toList]
      cases lookupBy o m.toList with
      | none => exact FloorShape.rebuild_word f top hf s d q'
      | some x => exact FloorShape.rebuild_word f top hf s x q'

/-- **The rebuilt root reads at its floors.** -/
theorem MRoot.surgery_at (R : MRoot C) (f : PrimTy.uint.Denote → PrimTy.uint.Denote) (top : Nat)
    (st : Storage C) (hf : ∀ k : PrimTy.uint.Denote, top ≤ k.1.toNat → f k = f uintMax) {P : PrimTy}
    (r : SRef C (.prim P)) (hr : r.root = R.name) :
    (R.surgery f top st).obs.word (.ref r) = st.obs.word (.ref (r.floorRef f)) := by
  obtain ⟨root, hroot, path⟩ := r
  simp only at hr
  subst hr
  obtain ⟨n, T, hT⟩ := R
  have e : T = _ := (Option.some.inj (hT.symm.trans hroot))
  subst e
  rw [Storage.obs_word_ref, Storage.obs_word_ref]
  show SVal.wordOf (((st.set hT _).get hroot).findM path) =
    SVal.wordOf ((st.get hroot).findM ((FloorShape.of _).floorPath f path))
  rw [SFields.get_set_same]
  exact FloorShape.rebuild_word f top hf _ _ path

/-- Every root of `Rs` rebuilt, the first last. -/
def surgeryAll (f : PrimTy.uint.Denote → PrimTy.uint.Denote) (top : Nat) : List (MRoot C) → Storage C → Storage C
  | [], st => st
  | R :: Rs, st => R.surgery f top (surgeryAll f top Rs st)

theorem surgeryAll_other (f : PrimTy.uint.Denote → PrimTy.uint.Denote) (top : Nat) (st : Storage C)
    {P : PrimTy} (r : SRef C (.prim P)) : ∀ Rs : List (MRoot C), r.root ∉ Rs.map (·.name) →
      (surgeryAll f top Rs st).obs.word (.ref r) = st.obs.word (.ref r)
  | [], _ => rfl
  | R :: Rs, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [surgeryAll, MRoot.surgery_other R f top _ r h.1, surgeryAll_other f top st r Rs h.2]

theorem surgeryAll_at (f : PrimTy.uint.Denote → PrimTy.uint.Denote) (top : Nat) (st : Storage C)
    (hf : ∀ k : PrimTy.uint.Denote, top ≤ k.1.toNat → f k = f uintMax) {P : PrimTy}
    (r : SRef C (.prim P)) :
    ∀ Rs : List (MRoot C), (Rs.map (·.name)).Nodup → r.root ∈ Rs.map (·.name) →
      (surgeryAll f top Rs st).obs.word (.ref r) = st.obs.word (.ref (r.floorRef f))
  | [], _, h => nomatch h
  | R' :: Rs, hn, hR => by
    rw [List.map_cons, List.nodup_cons] at hn
    rw [surgeryAll]
    by_cases he : r.root = R'.name
    · rw [MRoot.surgery_at R' f top _ hf r he]
      exact surgeryAll_other f top st (r.floorRef f) Rs (he ▸ hn.1)
    · rw [MRoot.surgery_other R' f top _ r he]
      rw [List.map_cons, List.mem_cons] at hR
      exact surgeryAll_at f top st hf r Rs hn.2 (hR.resolve_left he)

/-! ## The floor in the index set -/

/-- The largest value of `S` at most `x`, `0` where none is. -/
def floorIn (S : List Int) (x : Int) : Int := S.foldl (fun a s => if s ≤ x ∧ a < s then s else a) 0

theorem floorIn_spec (S : List Int) (x : Int) : ∀ (a : Int),
    a ≤ S.foldl (fun a s => if s ≤ x ∧ a < s then s else a) a ∧
      (a ≤ x → S.foldl (fun a s => if s ≤ x ∧ a < s then s else a) a ≤ x) ∧
      (S.foldl (fun a s => if s ≤ x ∧ a < s then s else a) a = a ∨
        S.foldl (fun a s => if s ≤ x ∧ a < s then s else a) a ∈ S) ∧
      (∀ s ∈ S, s ≤ x → s ≤ S.foldl (fun a s => if s ≤ x ∧ a < s then s else a) a) := by
  induction S with
  | nil => intro a; exact ⟨Int.le_refl _, id, .inl rfl, fun _ h => nomatch h⟩
  | cons s S ih =>
    intro a
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3, h4⟩ := ih (if s ≤ x ∧ a < s then s else a)
    by_cases hc : s ≤ x ∧ a < s
    · rw [if_pos hc] at h1 h2 h3 h4 ⊢
      refine ⟨by omega, fun _ => h2 hc.1, h3.elim (fun h => .inr (by rw [h]; exact List.mem_cons_self))
        (fun h => .inr (List.mem_cons_of_mem _ h)), fun s' hs' hsx => ?_⟩
      rcases List.mem_cons.1 hs' with rfl | hs'
      · exact h1
      · exact h4 s' hs' hsx
    · rw [if_neg hc] at h1 h2 h3 h4 ⊢
      refine ⟨h1, h2, h3.elim .inl (fun h => .inr (List.mem_cons_of_mem _ h)), fun s' hs' hsx => ?_⟩
      rcases List.mem_cons.1 hs' with rfl | hs'
      · have : s' ≤ a := by omega
        omega
      · exact h4 s' hs' hsx

theorem floorIn_le (S : List Int) {x : Int} (hx : 0 ≤ x) : floorIn S x ≤ x := (floorIn_spec S x 0).2.1 hx
theorem floorIn_nonneg (S : List Int) (x : Int) : 0 ≤ floorIn S x := (floorIn_spec S x 0).1
theorem floorIn_mem (S : List Int) (x : Int) : floorIn S x = 0 ∨ floorIn S x ∈ S := (floorIn_spec S x 0).2.2.1
theorem floorIn_ge (S : List Int) (x : Int) {s : Int} (hs : s ∈ S) (h : s ≤ x) : s ≤ floorIn S x :=
  (floorIn_spec S x 0).2.2.2 s hs h

theorem floorIn_fix (S : List Int) {s : Int} (hs : s ∈ S) (h0 : 0 ≤ s) : floorIn S s = s :=
  Int.le_antisymm (floorIn_le S h0) (floorIn_ge S s hs (Int.le_refl _))

theorem floorIn_mono (S : List Int) {x y : Int} (hx : 0 ≤ x) (h : x ≤ y) : floorIn S x ≤ floorIn S y := by
  rcases floorIn_mem S x with h0 | hm
  · rw [h0]; exact floorIn_nonneg S y
  · exact floorIn_ge S y hm (Int.le_trans (floorIn_le S hx) h)

theorem foldl_max_spec : ∀ (S : List Int) (a : Int), a ≤ S.foldl max a ∧ (∀ s ∈ S, s ≤ S.foldl max a) ∧
    (S.foldl max a = a ∨ S.foldl max a ∈ S)
  | [], a => ⟨Int.le_refl _, (fun _ h => nomatch h), .inl rfl⟩
  | s :: S, a => by
    obtain ⟨h1, h2, h3⟩ := foldl_max_spec S (max a s)
    simp only [List.foldl_cons]
    refine ⟨by omega, fun s' hs' => ?_, ?_⟩
    · rcases List.mem_cons.1 hs' with rfl | hs'
      · omega
      · exact h2 s' hs'
    · rcases h3 with h3 | h3
      · rw [h3]
        by_cases hm : a ≤ s
        · exact .inr (by rw [Int.max_eq_right hm]; exact List.mem_cons_self)
        · exact .inl (Int.max_eq_left (by omega))
      · exact .inr (List.mem_cons_of_mem _ h3)

/-- Past the largest value of `S`, the floor is constant. -/
theorem floorIn_top (S : List Int) {x : Int} (h : ∀ s ∈ S, s ≤ x) :
    floorIn S x = S.foldl max 0 := by
  obtain ⟨h0, hmax, hmem⟩ := foldl_max_spec S 0
  apply Int.le_antisymm
  · rcases floorIn_mem S x with he | hm
    · rw [he]; exact h0
    · exact hmax _ hm
  · rcases hmem with he | hm
    · rw [he]; exact floorIn_nonneg S x
    · exact floorIn_ge S x hm (h _ hm)

/-- The floor at `uint`. -/
def floorU (S : List Int) (k : PrimTy.uint.Denote) : PrimTy.uint.Denote :=
  ⟨floorIn S k.1, by
    have hk := uintVal_bounds k
    have h1 := floorIn_le S hk.1
    have h2 := floorIn_nonneg S k.1
    simp only [PrimTy.inRange, decide_eq_true_eq]
    omega⟩

/-- The keys past which the floor is constant. -/
def floorTop (S : List Int) : Nat := (S.foldl max 0).toNat

theorem floorU_top (S : List Int) (hS : ∀ s ∈ S, s < ((2 ^ 256 : Nat) : Int)) (k : PrimTy.uint.Denote)
    (hk : floorTop S ≤ k.1.toNat) : floorU S k = floorU S uintMax := by
  obtain ⟨h0, hmax, -⟩ := foldl_max_spec S 0
  have hk' := uintVal_bounds k
  apply Subtype.ext
  show floorIn S k.1 = floorIn S uintMax.1
  rw [floorIn_top S (x := k.1) (fun s hs => by have := hmax s hs; unfold floorTop at hk; omega),
    floorIn_top S (x := uintMax.1) (fun s hs => by have := hS s hs; rw [uintMax_val]; omega)]

/-! ## The floor, its last interval read at the top

A refutation lists the rebuilt mapping's entries one key at a time, so
the floor construction's last interval below the index set's largest
value (`apfSecond`, `apfTop`) would cost that value in entries.  Where the
largest value bounds no strict guard from above (`ApfSet.strict`), the
keys of that interval read the largest value instead (`lastIn`): a guard
true there is true at it, and the rebuilt mapping lists the keys up to the
second largest value only (`lastBound`), the default past them. -/

/-- The index set's values, and those of the strict guards' ground
operands (`k < t`: `t` bounds the keys strictly from above). -/
structure ApfSet where
  vals : List Int
  strict : List Int

instance : Membership Int ApfSet := ⟨fun S s => s ∈ S.vals⟩

theorem ApfSet.mem_def {S : ApfSet} {s : Int} : s ∈ S ↔ s ∈ S.vals := Iff.rfl

/-- The largest value, `0` where none is. -/
def apfTop (S : List Int) : Int := S.foldl max 0

/-- The second largest: the largest value below `apfTop`, `0` where none is. -/
def apfSecond (S : List Int) : Int := (S.filter (· < apfTop S)).foldl max 0

/-- The keys of the last interval below the largest value read it. -/
def ApfSet.region (S : ApfSet) (x : Int) : Prop :=
  apfSecond S.vals < x ∧ x < apfTop S.vals ∧ apfTop S.vals ∉ S.strict ∧ apfTop S.vals < ((2 ^ 256 : Nat) : Int)

instance (S : ApfSet) (x : Int) : Decidable (S.region x) := by unfold ApfSet.region; infer_instance

/-- **The key a key reads in the rebuilt mapping**: its floor, the largest
value in its last interval below it. -/
def lastIn (S : ApfSet) (x : Int) : Int := if S.region x then apfTop S.vals else floorIn S.vals x

section LastIn

variable (S : ApfSet)

theorem apfTop_ge {s : Int} (hs : s ∈ S.vals) : s ≤ apfTop S.vals := (foldl_max_spec S.vals 0).2.1 s hs

theorem apfTop_nonneg : 0 ≤ apfTop S.vals := (foldl_max_spec S.vals 0).1

theorem apfTop_mem (h : 0 < apfTop S.vals) : apfTop S.vals ∈ S.vals :=
  ((foldl_max_spec S.vals 0).2.2).resolve_left (by unfold apfTop at h; omega)

theorem apfSecond_ge {s : Int} (hs : s ∈ S.vals) (h : s < apfTop S.vals) : s ≤ apfSecond S.vals :=
  (foldl_max_spec _ 0).2.1 s (List.mem_filter.2 ⟨hs, by simpa only [decide_eq_true_eq] using h⟩)

theorem apfSecond_nonneg : 0 ≤ apfSecond S.vals := (foldl_max_spec _ 0).1

/-- Past the second largest value, a value is the largest. -/
theorem eq_top_of_second {s : Int} (hs : s ∈ S.vals) (h : apfSecond S.vals < s) : s = apfTop S.vals := by
  have := apfTop_ge S hs
  by_cases hl : s < apfTop S.vals
  · have := apfSecond_ge S hs hl; omega
  · omega

theorem floorIn_le_top (x : Int) : floorIn S.vals x ≤ apfTop S.vals := by
  rcases floorIn_mem S.vals x with h | h
  · rw [h]; exact apfTop_nonneg S
  · exact apfTop_ge S h

theorem lastIn_fix {s : Int} (hs : s ∈ S) (h0 : 0 ≤ s) : lastIn S s = s := by
  unfold lastIn
  split
  · rename_i hr
    have := eq_top_of_second S hs hr.1
    omega
  · exact floorIn_fix S.vals hs h0

theorem lastIn_ge (x : Int) {s : Int} (hs : s ∈ S) (h : s ≤ x) : s ≤ lastIn S x := by
  unfold lastIn
  split
  · exact apfTop_ge S hs
  · exact floorIn_ge S.vals x hs h

theorem lastIn_le {x s : Int} (hx : 0 ≤ x) (hs : s ∈ S) (h : x ≤ s) : lastIn S x ≤ s := by
  unfold lastIn
  split
  · rename_i hr
    have := eq_top_of_second S hs (by have := hr.1; omega)
    omega
  · have := floorIn_le S.vals hx; omega

theorem lastIn_lt {x t : Int} (hx : 0 ≤ x) (ht : t ∈ S) (hts : t ∈ S.strict) (h : x < t) : lastIn S x < t := by
  unfold lastIn
  split
  · rename_i hr
    have he := eq_top_of_second S ht (by have := hr.1; omega)
    exact absurd (he ▸ hts) hr.2.2.1
  · have := floorIn_le S.vals hx; omega

theorem floorIn_le_lastIn (x : Int) : floorIn S.vals x ≤ lastIn S x := by
  unfold lastIn
  split
  · exact floorIn_le_top S x
  · exact Int.le_refl _

theorem lastIn_mono {x y : Int} (hx : 0 ≤ x) (h : x ≤ y) : lastIn S x ≤ lastIn S y := by
  by_cases hr : S.region x
  · have hpos : 0 < apfTop S.vals := by have := apfSecond_nonneg S; have := hr.1; have := hr.2.1; omega
    have hmem := apfTop_mem S hpos
    have e : lastIn S x = apfTop S.vals := by unfold lastIn; rw [if_pos hr]
    rw [e]
    by_cases hy : y < apfTop S.vals
    · have hry : S.region y := ⟨by have := hr.1; omega, hy, hr.2.2⟩
      unfold lastIn; rw [if_pos hry]; exact Int.le_refl _
    · exact lastIn_ge S y hmem (by omega)
  · have e : lastIn S x = floorIn S.vals x := by unfold lastIn; rw [if_neg hr]
    rw [e]
    exact Int.le_trans (floorIn_mono S.vals hx h) (floorIn_le_lastIn S y)

theorem lastIn_mem (x : Int) : lastIn S x = 0 ∨ lastIn S x ∈ S.vals := by
  unfold lastIn
  split
  · rename_i hr
    exact .inr (apfTop_mem S (by have := apfSecond_nonneg S; have := hr.1; have := hr.2.1; omega))
  · exact floorIn_mem S.vals x

theorem lastIn_nonneg (x : Int) : 0 ≤ lastIn S x := by
  rcases lastIn_mem S x with h | h
  · omega
  · unfold lastIn at h ⊢
    split
    · exact apfTop_nonneg S
    · exact floorIn_nonneg S.vals x

theorem lastIn_bound {x : Int} (hx : 0 ≤ x) (hx' : x < ((2 ^ 256 : Nat) : Int)) :
    lastIn S x < ((2 ^ 256 : Nat) : Int) := by
  unfold lastIn
  split
  · rename_i hr; exact hr.2.2.2
  · have := floorIn_le S.vals hx; omega

end LastIn

/-- `lastIn` at `uint`. -/
def lastU (S : ApfSet) (k : PrimTy.uint.Denote) : PrimTy.uint.Denote :=
  ⟨lastIn S k.1, by
    have hk := uintVal_bounds k
    have h1 := lastIn_bound S hk.1 hk.2
    have h2 := lastIn_nonneg S k.1
    simp only [PrimTy.inRange, decide_eq_true_eq]
    omega⟩

/-- **The keys a refutation lists**: up to the second largest value where
the last interval reads the largest, up to the largest otherwise. -/
def lastBound (S : ApfSet) : Nat :=
  if apfTop S.vals ∉ S.strict ∧ apfTop S.vals < ((2 ^ 256 : Nat) : Int) then (apfSecond S.vals).toNat + 1
  else (apfTop S.vals).toNat

/-- Past `lastBound` every key reads the largest value. -/
theorem lastU_top (S : ApfSet) (hS : ∀ s ∈ S.vals, s < ((2 ^ 256 : Nat) : Int)) (k : PrimTy.uint.Denote)
    (hk : lastBound S ≤ k.1.toNat) : lastU S k = lastU S uintMax := by
  have hb := uintVal_bounds k
  have hT := apfTop_nonneg S
  have hT' : apfTop S.vals < ((2 ^ 256 : Nat) : Int) := by
    rcases (foldl_max_spec S.vals 0).2.2 with h | h
    · unfold apfTop; omega
    · exact hS _ h
  have htopv : ∀ x : Int, apfTop S.vals ≤ x → lastIn S x = apfTop S.vals := by
    intro x hx
    unfold lastIn
    rw [if_neg (fun hr => by have := hr.2.1; omega)]
    exact floorIn_top S.vals (fun s hs => Int.le_trans (apfTop_ge S hs) hx)
  have hmax : lastIn S uintMax.1 = apfTop S.vals := htopv _ (by rw [uintMax_val]; omega)
  apply Subtype.ext
  show lastIn S k.1 = lastIn S uintMax.1
  rw [hmax]
  by_cases hge : apfTop S.vals ≤ k.1
  · exact htopv _ hge
  · unfold lastBound at hk
    split at hk
    · rename_i hc
      have hr : S.region k.1 := ⟨by have := apfSecond_nonneg S; omega, by omega, hc.1, hc.2⟩
      unfold lastIn
      rw [if_pos hr]
    · omega

/-! ## The fragment's terms -/

/-- **A term of the fragment** (`false`): roots of `Rs` read only along a
path of their own (`true`: `rroot`, then keys, `rkeyU` at a `uint` key and
`rkey` at another, and members, `rfield`), the word there (`rword`); every
other path at a root outside `Rs`; no other storage access. -/
inductive ApfTm (Rs : List Name) : Bool → {s : Srt} → LTm C s → Type where
  | var {p : PrimTy} (k : Nat) : ApfTm Rs false (LTm.var (p := p) k)
  | lit {p : PrimTy} (v : p.Denote) : ApfTm Rs false (.app0 (.lit v))
  | env (k : EnvKey) : ApfTm Rs false (.app0 (.env k))
  | root (r : Name) {T : Ty} (h : C.rootType r = some T) (hr : r ∉ Rs) : ApfTm Rs false (.app0 (.root r h))
  | rroot (r : Name) {T : Ty} (h : C.rootType r = some T) (hr : r ∈ Rs) : ApfTm Rs true (.app0 (.root r h))
  | field {s f : Name} {T : Ty} (h : C.fieldType s f = some T) {q : LTm C (.path (.ref (.struct s)))}
      (hq : ApfTm Rs false q) : ApfTm Rs false (.app1 (.field h) q)
  | rfield {s f : Name} {T : Ty} (h : C.fieldType s f = some T) {q : LTm C (.path (.ref (.struct s)))}
      (hq : ApfTm Rs true q) : ApfTm Rs true (.app1 (.field h) q)
  | index {K : PrimTy} {T : Ty} {q : LTm C (.path (.ref (.mapping K T)))} {i : LTm C (.val K)}
      (hq : ApfTm Rs false q) (hi : ApfTm Rs false i) : ApfTm Rs false (.index .map q i)
  | rkeyU {T : Ty} {q : LTm C (.path (.ref (.mapping .uint T)))} {i : LTm C (.val .uint)}
      (hq : ApfTm Rs true q) (hi : ApfTm Rs false i) : ApfTm Rs true (.index .map q i)
  | rkey {K : PrimTy} {T : Ty} {q : LTm C (.path (.ref (.mapping K T)))} {i : LTm C (.val K)}
      (hq : ApfTm Rs true q) (hi : ApfTm Rs false i) : ApfTm Rs true (.index .map q i)
  | word {p : PrimTy} {q : LTm C (.path (.prim p))} (hq : ApfTm Rs false q) : ApfTm Rs false (.obsW q)
  | rword {p : PrimTy} {q : LTm C (.path (.prim p))} (hq : ApfTm Rs true q) : ApfTm Rs false (.obsW q)
  | unop (op : UnOp) {p : PrimTy} (h : op.accepts p = true) {t : LTm C (.val p)} (ht : ApfTm Rs false t) :
      ApfTm Rs false (.app1 (.unop op h) t)
  | binop (op : BinOp) {p : PrimTy} (h : op.accepts p = true) {a b : LTm C (.val p)}
      (ha : ApfTm Rs false a) (hb : ApfTm Rs false b) : ApfTm Rs false (.app2 (.binop op h) a b)
  | seq {s' s : Srt} {d : LTm C s'} {a : LTm C s} (hd : ApfTm Rs false d) (ha : ApfTm Rs false a) :
      ApfTm Rs false (.seq d a)
  | orElse {s : Srt} {a b : LTm C s} (ha : ApfTm Rs false a) (hb : ApfTm Rs false b) :
      ApfTm Rs false (.orElse a b)
  | kite {p : PrimTy} {s : Srt} {a b : LTm C (.val p)} {t e : LTm C s}
      (ha : ApfTm Rs false a) (hb : ApfTm Rs false b) (ht : ApfTm Rs false t) (he : ApfTm Rs false e) :
      ApfTm Rs false (.kite a b t e)
  | err {s : Srt} : ApfTm Rs false (LTm.err (C := C) (s := s))

namespace ApfTm

variable {Rs : List Name}

/-- Recognize the fragment: a term (`false`), or a path at a root of `Rs`
(`true`). -/
def ofTerm? (Rs : List Name) : (b : Bool) → {s : Srt} → (t : LTm C s) → Option (ApfTm Rs b t)
  | false, _, .var k => some (.var k)
  | false, _, .app0 (.lit v) => some (.lit v)
  | false, _, .app0 (.env k) => some (.env k)
  | false, _, .app0 (.root r h) => if hr : r ∈ Rs then none else some (.root r h hr)
  | true, _, .app0 (.root r h) => if hr : r ∈ Rs then some (.rroot r h hr) else none
  | false, _, .app1 (.field h) q => (ofTerm? Rs false q).map (.field h)
  | true, _, .app1 (.field h) q => (ofTerm? Rs true q).map (.rfield h)
  | false, _, .app1 (.unop op h) t => (ofTerm? Rs false t).map (.unop op h)
  | false, _, .app2 (.binop op h) a b => do return .binop op h (← ofTerm? Rs false a) (← ofTerm? Rs false b)
  | false, _, .obsW q =>
    match ofTerm? Rs true q with
    | some hq => some (.rword hq)
    | none => (ofTerm? Rs false q).map .word
  | false, _, .index .map q i => do return .index (← ofTerm? Rs false q) (← ofTerm? Rs false i)
  | true, _, .index (k := .uint) .map q i => do return .rkeyU (← ofTerm? Rs true q) (← ofTerm? Rs false i)
  | true, _, .index .map q i => do return .rkey (← ofTerm? Rs true q) (← ofTerm? Rs false i)
  | false, _, .seq d a => do return .seq (← ofTerm? Rs false d) (← ofTerm? Rs false a)
  | false, _, .orElse a b => do return .orElse (← ofTerm? Rs false a) (← ofTerm? Rs false b)
  | false, _, .kite a b t e => do
    return .kite (← ofTerm? Rs false a) (← ofTerm? Rs false b) (← ofTerm? Rs false t) (← ofTerm? Rs false e)
  | false, _, .err => some .err
  | _, _, _ => none

/-- The read query of a term of the fragment. -/
def toRead : {b : Bool} → {s : Srt} → {t : LTm C s} → ApfTm Rs b t → ReadExpr t
  | _, _, _, .var k => .var k
  | _, _, _, .lit v => .lit v
  | _, _, _, .env k => .env k
  | _, _, _, .root r h _ => .root r h
  | _, _, _, .rroot r h _ => .root r h
  | _, _, _, .field h hq => .field h hq.toRead
  | _, _, _, .rfield h hq => .field h hq.toRead
  | _, _, _, .index hq hi => .index hq.toRead hi.toRead
  | _, _, _, .rkeyU hq hi => .index hq.toRead hi.toRead
  | _, _, _, .rkey hq hi => .index hq.toRead hi.toRead
  | _, _, _, .word hq => .word hq.toRead
  | _, _, _, .rword hq => .word hq.toRead
  | _, _, _, .unop op h ht => .unop op h ht.toRead
  | _, _, _, .binop op h ha hb => .binop op h ha.toRead hb.toRead
  | _, _, _, .seq hd ha => .seq hd.toRead ha.toRead
  | _, _, _, .orElse ha hb => .orElse ha.toRead hb.toRead
  | _, _, _, .kite ha hb ht he => .kite ha.toRead hb.toRead ht.toRead he.toRead
  | _, _, _, .err => .err

/-- A path of a root of `Rs` still along its mappings: keys only. -/
def pre : {b : Bool} → {s : Srt} → {t : LTm C s} → ApfTm Rs b t → Bool
  | _, _, _, .rroot .. => true
  | _, _, _, .rkeyU hq _ | _, _, _, .rkey hq _ => hq.pre
  | _, _, _, _ => false

/-- A path value at a root of `Rs` exactly where `b`. -/
def RootsAt (Rs : List Name) (b : Bool) {H : HTy} : (s : Srt) → Option (s.Den C H) → Prop
  | .path _, some r => decide (r.root ∈ Rs) = b
  | _, _ => True

theorem RootsAt.none (Rs : List Name) (b : Bool) {H : HTy} : ∀ s : Srt, RootsAt (C := C) Rs b (H := H) s none
  | .path _ | .val _ | .st | .sv _ | .ident _ | .addr _ | .mem | .mv _ | .sts _ | .spath _ _ | .kint => trivial

/-- **The fragment's paths are at roots of `Rs` exactly where `b`.** -/
theorem rootsAt (g : State C []) (ν : AEnv) {b : Bool} {s : Srt} {t : LTm C s} (ht : ApfTm Rs b t) :
    RootsAt Rs b s (t.eval g ν) := by
  induction ht with
  | var | lit | env | word | rword | unop | binop => trivial
  | root r h hr => exact decide_eq_false hr
  | rroot r h hr => exact decide_eq_true hr
  | @field _ _ _ h q hq ih | @rfield _ _ _ h q hq ih =>
    rw [LTm.eval_app1, Close.Op1.eval_field]
    cases hq' : (q.eval g ν : Option (SRef C _)) with
    | none => exact RootsAt.none Rs _ _
    | some r => rw [hq'] at ih; exact ih
  | @index _ _ q i hq hi ihq ihi | @rkeyU _ q i hq hi ihq ihi | @rkey _ _ q i hq hi ihq ihi =>
    rw [LTm.eval_index]
    cases hq' : (q.eval g ν : Option (SRef C _)) with
    | none => exact RootsAt.none Rs _ _
    | some r =>
      rw [hq'] at ihq
      cases (i.eval g ν : Option _) with
      | none => exact RootsAt.none Rs _ _
      | some _ => exact ihq
  | seq hd ha ihd iha =>
    rw [LTm.eval_seq]
    cases LTm.eval g ν _ with
    | none => exact RootsAt.none Rs _ _
    | some _ => exact iha
  | orElse ha hb iha ihb =>
    rw [LTm.eval_orElse]
    cases h : LTm.eval g ν _ with
    | none => rw [h] at iha; exact ihb
    | some _ => rw [h] at iha; exact iha
  | kite ha hb ht he iha ihb iht ihe =>
    rw [LTm.eval_kite]
    cases (LTm.eval g ν _ : Option _) with
    | none => exact RootsAt.none Rs _ _
    | some x =>
      cases (LTm.eval g ν _ : Option _) with
      | none => exact RootsAt.none Rs _ _
      | some y =>
        dsimp only [Option.bind_some]
        split
        · exact iht
        · exact ihe
  | err => exact RootsAt.none Rs _ _

/-- The positions of `ks`, at `uint`. -/
def ksP (ks : List Nat) : List Parameter := ks.map (⟨.uint, ·⟩)

/-- **Where a term reads alike in the rebuilt storage**: the variables of
`ks` only as `uint` keys along a root of `Rs`'s mappings; every other such
key ground (`Gd`), mentioning no binder of `Bs`; no key past them a `uint`
one along the mappings. -/
def Rel (ks : List Nat) (Bs : List Parameter) (Gd : LTm C (.val .uint) → Prop) :
    {b : Bool} → {s : Srt} → {t : LTm C s} → ApfTm Rs b t → Prop
  | _, _, _, @ApfTm.var _ _ p k => (⟨p, k⟩ : Parameter) ∉ ksP ks
  | _, _, _, .lit _ | _, _, _, .env _ | _, _, _, .root .. | _, _, _, .rroot .. | _, _, _, .err => True
  | _, _, _, .field _ hq | _, _, _, .rfield _ hq => hq.Rel ks Bs Gd
  | _, _, _, .index hq hi => hq.Rel ks Bs Gd ∧ hi.Rel ks Bs Gd
  | _, _, _, .rkeyU (i := i) hq hi =>
    hq.Rel ks Bs Gd ∧ ((hq.pre = true ∧
      ((∃ k ∈ ks, i = .var k) ∨ ((∀ q ∈ i.parameters, q ∉ Bs) ∧ Gd i ∧ hi.Rel ks Bs Gd))) ∨
      (hq.pre = false ∧ hi.Rel ks Bs Gd))
  | _, _, _, .rkey (K := K) hq hi => hq.Rel ks Bs Gd ∧ hi.Rel ks Bs Gd ∧ (hq.pre = true → K ≠ .uint)
  | _, _, _, .word hq | _, _, _, .rword hq => hq.Rel ks Bs Gd
  | _, _, _, .unop _ _ ht => ht.Rel ks Bs Gd
  | _, _, _, .binop _ _ ha hb => ha.Rel ks Bs Gd ∧ hb.Rel ks Bs Gd
  | _, _, _, .seq hd ha => hd.Rel ks Bs Gd ∧ ha.Rel ks Bs Gd
  | _, _, _, .orElse ha hb => ha.Rel ks Bs Gd ∧ hb.Rel ks Bs Gd
  | _, _, _, .kite ha hb ht he => ha.Rel ks Bs Gd ∧ hb.Rel ks Bs Gd ∧ ht.Rel ks Bs Gd ∧ he.Rel ks Bs Gd

end ApfTm

/-! ## Reads in the rebuilt storage -/

/-- What the rebuilding keeps: other roots' words, and the words of a root
of `Rs` at the floors of their keys (`SRef.floorRef`). -/
structure Surg (g : State C []) (st' : Storage C) (Rs : List Name)
    (f : PrimTy.uint.Denote → PrimTy.uint.Denote) : Prop where
  other : ∀ {P : PrimTy} (r : SRef C (.prim P)), r.root ∉ Rs →
    st'.obs.word (.ref r) = g.storage.obs.word (.ref r)
  keyAt : ∀ {P : PrimTy} (r : SRef C (.prim P)), r.root ∈ Rs →
    st'.obs.word (.ref r) = g.storage.obs.word (.ref (r.floorRef f))

theorem Parameter.read_var {p : PrimTy} (k : Nat) (μ : AEnv) :
    (⟨p, k⟩ : Parameter).read μ = μ.get p k := rfl

/-- **How a term reads in the rebuilt storage** at `μ'` against the old
one at `μ`: a value alike; a path of a root of `Rs` at its floors, the
shape it reaches its type's along the mappings (`pre`) and `keep` past
them. -/
def TRel (f : PrimTy.uint.Denote → PrimTy.uint.Denote) (pre : Bool) {H : HTy} :
    (b : Bool) → (s : Srt) → Option (s.Den C H) → Option (s.Den C H) → Prop
  | true, .path U, x', x => x = x'.map (SRef.floorRef f) ∧
      ∀ r' ∈ x', (FloorShape.of r'.ty).follow r'.path = (if pre then FloorShape.of U else .keep U)
  | _, _, x', x => x' = x

theorem TRel.of_false {f : PrimTy.uint.Denote → PrimTy.uint.Denote} {pre : Bool} {H : HTy} {s : Srt}
    {x' x : Option (s.Den C H)} (h : TRel f pre false s x' x) : x' = x := h

theorem TRel.of_eq {f : PrimTy.uint.Denote → PrimTy.uint.Denote} {pre : Bool} {H : HTy} {s : Srt}
    {x' x : Option (s.Den C H)} (h : x' = x) : TRel f pre false s x' x := h

/-- A key appended to a reference, at the floors. -/
theorem SRef.floorRef_index (f : PrimTy.uint.Denote → PrimTy.uint.Denote) {K : PrimTy} {V : Ty}
    (r : SRef C (.ref (.mapping K V))) (k : K.Denote) :
    (r.index .map k).floorRef f =
      ⟨r.root, r.hroot, ((FloorShape.of r.ty).floorPath f r.path).append
        (((FloorShape.of r.ty).follow r.path).floorPath f (.key k .nil))⟩ := by
  show (⟨r.root, r.hroot, (FloorShape.of r.ty).floorPath f (r.path.append (Path.index .map k))⟩ : SRef C V) = _
  rw [Path.index_map, FloorShape.floorPath_append]

theorem SRef.index_eq {K : PrimTy} {V : Ty} (r : SRef C (.ref (.mapping K V))) (k : K.Denote) :
    r.index .map k = ⟨r.root, r.hroot, r.path.append (.key k .nil)⟩ := by
  show r.append _ = _
  rw [Path.index_map]
  rfl

theorem FloorShape.floorPath_floor_key (f : PrimTy.uint.Denote → PrimTy.uint.Denote) {V U : Ty} (s : FloorShape V)
    (k : PrimTy.uint.Denote) (p : Path V U) : (FloorShape.floor s).floorPath f (.key k p) = .key (f k) (s.floorPath f p) :=
  rfl

theorem FloorShape.floorPath_outer_key (f : PrimTy.uint.Denote → PrimTy.uint.Denote) {K : PrimTy} {V U : Ty}
    (s : FloorShape V) (k : K.Denote) (p : Path V U) :
    (FloorShape.outer K s).floorPath f (.key k p) = .key k (s.floorPath f p) := rfl

theorem SRef.follow_index {K : PrimTy} {V : Ty} (r : SRef C (.ref (.mapping K V))) (k : K.Denote) :
    (FloorShape.of (r.index .map k).ty).follow (r.index .map k).path =
      ((FloorShape.of r.ty).follow r.path).follow (.key k .nil) := by
  show (FloorShape.of r.ty).follow (r.path.append (Path.index .map k)) = _
  rw [Path.index_map, FloorShape.follow_append]

theorem SRef.floorRef_field (f : PrimTy.uint.Denote → PrimTy.uint.Denote) {s fn : Name} {T : Ty}
    (r : SRef C (.ref (.struct s))) (h : C.fieldType s fn = some T)
    (hk : (FloorShape.of r.ty).follow r.path = .keep _) :
    (r.field h).floorRef f = (r.floorRef f).field h := by
  show (⟨r.root, r.hroot, (FloorShape.of r.ty).floorPath f (r.path.append (.field h .nil))⟩ : SRef C T) =
    ⟨r.root, r.hroot, ((FloorShape.of r.ty).floorPath f r.path).append (.field h .nil)⟩
  rw [FloorShape.floorPath_append, hk, FloorShape.floorPath_keep]

theorem SRef.follow_field {s fn : Name} {T : Ty} (r : SRef C (.ref (.struct s))) (h : C.fieldType s fn = some T)
    (hk : (FloorShape.of r.ty).follow r.path = .keep _) :
    (FloorShape.of (r.field h).ty).follow (r.field h).path = .keep T := by
  show (FloorShape.of r.ty).follow (r.path.append (.field h .nil)) = _
  rw [FloorShape.follow_append, hk, FloorShape.follow_keep]

/-- **The relation**: in the rebuilt storage, at `μ'`, a term reads what it
reads at `μ` in the old one, where `μ` holds the floors of `μ'` at `ks`;
a path of a root of `Rs`, at its floors. -/
theorem ApfTm.eval_trel {Rs : List Name} (g : State C []) (st' : Storage C)
    {f : PrimTy.uint.Denote → PrimTy.uint.Denote} (hS : Surg g st' Rs f) {ks : List Nat}
    {Bs : List Parameter} {Gd : LTm C (.val .uint) → Prop} {ν μ' μ : AEnv}
    (hGd : ∀ x, Gd x → ∀ v, (x.eval g ν : Option PrimTy.uint.Denote) = some v → f v = v)
    (hμ : ∀ q, q ∉ ksP ks → q.read μ' = q.read μ)
    (hk : ∀ k ∈ ks, μ.get .uint k = f (μ'.get .uint k))
    (hν : ∀ q, q ∉ Bs → q.read μ = q.read ν) {b : Bool} {s : Srt} {t : LTm C s} (ht : ApfTm Rs b t)
    (hr : ht.Rel ks Bs Gd) : TRel f ht.pre b s (t.eval { g with storage := st' } μ') (t.eval g μ) := by
  induction ht with
  | @var p k => exact congrArg some (hμ ⟨p, k⟩ hr)
  | lit | env | root | err => rfl
  | @rroot r T h hr' =>
    refine ⟨?_, fun r' hr' => ?_⟩
    · show some (SRef.ofRoot r h) = some ((SRef.ofRoot r h).floorRef f)
      show some (⟨r, h, .nil⟩ : SRef C T) = some ⟨r, h, (FloorShape.of T).floorPath f .nil⟩
      rw [FloorShape.floorPath_nil]
    · obtain rfl : (SRef.ofRoot r h) = r' := Option.some.inj hr'
      exact FloorShape.follow_nil _
  | field h hq ih =>
    apply TRel.of_eq
    rw [LTm.eval_app1, LTm.eval_app1, (ih hr).of_false]
    rfl
  | @rfield _ _ _ h q hq ih =>
    obtain ⟨hx, hsh⟩ := ih hr
    show TRel f false true _ _ _
    rw [LTm.eval_app1, LTm.eval_app1, Close.Op1.eval_field, Close.Op1.eval_field, hx]
    cases hq' : (q.eval { g with storage := st' } μ' : Option (SRef C _)) with
    | none => exact ⟨rfl, fun _ h => nomatch h⟩
    | some r' =>
      have hk' : (FloorShape.of r'.ty).follow r'.path = .keep _ := by
        have := hsh r' (by rw [hq']; rfl)
        rw [this]
        split <;> rfl
      refine ⟨?_, fun r'' hr'' => ?_⟩
      · show some ((r'.floorRef f).field h) = some ((r'.field h).floorRef f)
        rw [SRef.floorRef_field f r' h hk']
      · obtain rfl : r'.field h = r'' := Option.some.inj hr''
        exact SRef.follow_field r' h hk'
  | index hq hi ihq ihi =>
    apply TRel.of_eq
    rw [LTm.eval_index, LTm.eval_index, (ihq hr.1).of_false, (ihi hr.2).of_false]
  | @rkeyU T q i hq hi ihq ihi =>
    obtain ⟨hx, hsh⟩ := ihq hr.1
    show TRel f hq.pre true _ _ _
    rw [LTm.eval_index, LTm.eval_index, hx]
    cases hq' : (q.eval { g with storage := st' } μ' : Option (SRef C _)) with
    | none => exact ⟨rfl, fun _ h => nomatch h⟩
    | some r' =>
      have hshr := hsh r' (by rw [hq']; rfl)
      dsimp only [Option.map_some, Option.bind_some]
      rcases hr.2 with ⟨hp, hkey⟩ | ⟨hp, hir⟩
      · -- a floored key: at the floor
        rw [hp] at hshr
        have hfol : (FloorShape.of r'.ty).follow r'.path = .floor (FloorShape.of T) := hshr
        have hkeys : (i.eval g μ : Option PrimTy.uint.Denote) =
            (i.eval { g with storage := st' } μ' : Option PrimTy.uint.Denote).map f := by
          rcases hkey with ⟨k, hk', rfl⟩ | ⟨hb, hg, hx'⟩
          · show some (μ.get .uint k) = some (f (μ'.get .uint k))
            rw [hk k hk']
          · rw [← (ihi hx').of_false]
            cases he : (i.eval { g with storage := st' } μ' : Option PrimTy.uint.Denote) with
            | none => rfl
            | some v =>
              have hv : (i.eval g ν : Option PrimTy.uint.Denote) = some v := by
                rw [← he, (ihi hx').of_false]
                exact (i.eval_agree_parameters g fun q hq => hν q (hb q hq)).symm
              rw [Option.map_some, hGd i hg v hv]
        rw [hkeys]
        cases (i.eval { g with storage := st' } μ' : Option PrimTy.uint.Denote) with
        | none => exact ⟨rfl, fun _ h => nomatch h⟩
        | some k' =>
          refine ⟨?_, fun r'' hr'' => ?_⟩
          · show some ((r'.floorRef f).index .map (f k')) = some ((r'.index .map k').floorRef f)
            rw [SRef.floorRef_index, hfol, SRef.index_eq, FloorShape.floorPath_floor_key, FloorShape.floorPath_nil]
            rfl
          · obtain rfl : r'.index .map k' = r'' := Option.some.inj hr''
            rw [SRef.follow_index, hfol, hp]
            exact FloorShape.follow_nil _
      · -- after a member: copied
        rw [hp] at hshr
        have hfol : (FloorShape.of r'.ty).follow r'.path = .keep _ := hshr
        rw [← (ihi hir).of_false]
        cases (i.eval { g with storage := st' } μ' : Option PrimTy.uint.Denote) with
        | none => exact ⟨rfl, fun _ h => nomatch h⟩
        | some k' =>
          refine ⟨?_, fun r'' hr'' => ?_⟩
          · show some ((r'.floorRef f).index .map k') = some ((r'.index .map k').floorRef f)
            rw [SRef.floorRef_index, hfol, FloorShape.floorPath_keep, SRef.index_eq]
            rfl
          · obtain rfl : r'.index .map k' = r'' := Option.some.inj hr''
            rw [SRef.follow_index, hfol, FloorShape.follow_keep, hp]
            rfl
  | @rkey K T q i hq hi ihq ihi =>
    obtain ⟨hx, hsh⟩ := ihq hr.1
    show TRel f hq.pre true _ _ _
    rw [LTm.eval_index, LTm.eval_index, hx, ← (ihi hr.2.1).of_false]
    cases hq' : (q.eval { g with storage := st' } μ' : Option (SRef C _)) with
    | none => exact ⟨rfl, fun _ h => nomatch h⟩
    | some r' =>
      have hshr := hsh r' (by rw [hq']; rfl)
      dsimp only [Option.map_some, Option.bind_some]
      cases (i.eval { g with storage := st' } μ' : Option K.Denote) with
      | none => exact ⟨rfl, fun _ h => nomatch h⟩
      | some k' =>
        cases hp : hq.pre with
        | true =>
          rw [hp] at hshr
          have hfol : (FloorShape.of r'.ty).follow r'.path = .outer K (FloorShape.of T) := by
            rw [hshr, if_pos rfl, FloorShape.of_mapping_ne (hr.2.2 hp)]
          refine ⟨?_, fun r'' hr'' => ?_⟩
          · show some ((r'.floorRef f).index .map k') = some ((r'.index .map k').floorRef f)
            rw [SRef.floorRef_index, hfol, SRef.index_eq, FloorShape.floorPath_outer_key, FloorShape.floorPath_nil]
            rfl
          · obtain rfl : r'.index .map k' = r'' := Option.some.inj hr''
            rw [SRef.follow_index, hfol]
            exact FloorShape.follow_nil _
        | false =>
          rw [hp] at hshr
          have hfol : (FloorShape.of r'.ty).follow r'.path = .keep _ := hshr
          refine ⟨?_, fun r'' hr'' => ?_⟩
          · show some ((r'.floorRef f).index .map k') = some ((r'.index .map k').floorRef f)
            rw [SRef.floorRef_index, hfol, FloorShape.floorPath_keep, SRef.index_eq]
            rfl
          · obtain rfl : r'.index .map k' = r'' := Option.some.inj hr''
            rw [SRef.follow_index, hfol, FloorShape.follow_keep]
            rfl
  | @word p q hq ih =>
    apply TRel.of_eq
    rw [LTm.eval_obsW, LTm.eval_obsW, (ih hr).of_false]
    have hroot := ApfTm.rootsAt g μ hq
    cases hq' : (q.eval g μ : Option (SRef C (.prim p))) with
    | none => rfl
    | some r =>
      rw [hq'] at hroot
      exact congrArg some (hS.other r (of_decide_eq_false hroot))
  | @rword p q hq ih =>
    obtain ⟨hx, -⟩ := ih hr
    apply TRel.of_eq
    rw [LTm.eval_obsW, LTm.eval_obsW, hx]
    have hroot := ApfTm.rootsAt { g with storage := st' } μ' hq
    cases hq' : (q.eval { g with storage := st' } μ' : Option (SRef C (.prim p))) with
    | none => rfl
    | some r =>
      rw [hq'] at hroot
      exact congrArg some (hS.keyAt r (of_decide_eq_true hroot))
  | unop op h ht ih =>
    apply TRel.of_eq
    rw [LTm.eval_app1, LTm.eval_app1, (ih hr).of_false]
    rfl
  | binop op h ha hb iha ihb =>
    apply TRel.of_eq
    rw [LTm.eval_app2, LTm.eval_app2, (iha hr.1).of_false, (ihb hr.2).of_false]
    rfl
  | seq hd ha ihd iha =>
    apply TRel.of_eq
    rw [LTm.eval_seq, LTm.eval_seq, (ihd hr.1).of_false, (iha hr.2).of_false]
  | orElse ha hb iha ihb =>
    apply TRel.of_eq
    rw [LTm.eval_orElse, LTm.eval_orElse, (iha hr.1).of_false, (ihb hr.2).of_false]
  | kite ha hb ht he iha ihb iht ihe =>
    apply TRel.of_eq
    rw [LTm.eval_kite, LTm.eval_kite, (iha hr.1).of_false, (ihb hr.2.1).of_false, (iht hr.2.2.1).of_false,
      (ihe hr.2.2.2).of_false]

/-- **A term reads alike** in the rebuilt storage at `μ'` and the old one at
`μ`. -/
theorem ApfTm.eval_rel {Rs : List Name} (g : State C []) (st' : Storage C)
    {f : PrimTy.uint.Denote → PrimTy.uint.Denote} (hS : Surg g st' Rs f) {ks : List Nat}
    {Bs : List Parameter} {Gd : LTm C (.val .uint) → Prop} {ν μ' μ : AEnv}
    (hGd : ∀ x, Gd x → ∀ v, (x.eval g ν : Option PrimTy.uint.Denote) = some v → f v = v)
    (hμ : ∀ q, q ∉ ksP ks → q.read μ' = q.read μ)
    (hk : ∀ k ∈ ks, μ.get .uint k = f (μ'.get .uint k))
    (hν : ∀ q, q ∉ Bs → q.read μ = q.read ν) {s : Srt} {t : LTm C s} (ht : ApfTm Rs false t)
    (hr : ht.Rel ks Bs Gd) : t.eval { g with storage := st' } μ' = t.eval g μ :=
  (ApfTm.eval_trel g st' hS hGd hμ hk hν ht hr).of_false

/-! ## Guards: true at a key, true at its floor -/

/-- How an operand's value relates to its value at the floor: a block
variable's is its floor (`lastIn`); a ground operand's is the same, in the
index set with its successor, and among the strict guards' operands. -/
def FRel (S : ApfSet) (v : Bool) (x' x : Int) : Prop :=
  if v then x = lastIn S x'
  else x = x' ∧ x ∈ S ∧ x ∈ S.strict ∧ (x + 1 < ((2 ^ 256 : Nat) : Int) → x + 1 ∈ S)

theorem le_mono (S : ApfSet) {vx vy : Bool} {x' y' x y : Int} (h0 : 0 ≤ x') (h0' : 0 ≤ y')
    (hx : FRel S vx x' x) (hy : FRel S vy y' y) (h : x' ≤ y') : x ≤ y := by
  unfold FRel at hx hy
  cases vx <;> cases vy <;> simp only [Bool.false_eq_true, if_false, if_true] at hx hy
  · omega
  · obtain ⟨rfl, hm, -⟩ := hx; rw [hy]; exact lastIn_ge S y' hm h
  · obtain ⟨rfl, hm, -⟩ := hy; rw [hx]; exact lastIn_le S h0 hm h
  · rw [hx, hy]; exact lastIn_mono S h0 h

theorem lt_mono (S : ApfSet) {vx vy : Bool} {x' y' x y : Int} (h0 : 0 ≤ x')
    (hb : y' < ((2 ^ 256 : Nat) : Int)) (hx : FRel S vx x' x) (hy : FRel S vy y' y)
    (hv : (vx && vy) = false) (h : x' < y') : x < y := by
  unfold FRel at hx hy
  cases vx <;> cases vy <;> simp only [Bool.false_eq_true, if_false, if_true, Bool.and_self] at hx hy hv
  · omega
  · obtain ⟨rfl, -, -, hs⟩ := hx
    rw [hy]
    have := lastIn_ge S y' (hs (by omega)) (by omega)
    omega
  · obtain ⟨rfl, hm, ht, -⟩ := hy; rw [hx]; exact lastIn_lt S h0 hm ht h
  · cases hv

theorem eq_mono (S : ApfSet) {vx vy : Bool} {x' y' x y : Int} (h0 : 0 ≤ x')
    (hx : FRel S vx x' x) (hy : FRel S vy y' y) (h : x' = y') : x = y := by
  subst h
  unfold FRel at hx hy
  cases vx <;> cases vy <;> simp only [Bool.false_eq_true, if_false, if_true] at hx hy
  · omega
  · obtain ⟨rfl, hm, -⟩ := hx; rw [hy, lastIn_fix S hm h0]
  · obtain ⟨rfl, hm, -⟩ := hy; rw [hx, lastIn_fix S hm h0]
  · rw [hx, hy]

/-- A comparison at `uint`. -/
def cmpOf : BinOp → Int → Int → Bool
  | .lt, x, y => decide (x < y)
  | .gt, x, y => decide (y < x)
  | .le, x, y => decide (x ≤ y)
  | .ge, x, y => decide (y ≤ x)
  | .eqB, x, y => decide (x = y)
  | _, _, _ => false

/-- `<`, `>`, `<=`, `>=`, `==`: the guard comparisons. -/
def _root_.Solidity.BinOp.isGuardOp : BinOp → Bool
  | .lt | .gt | .le | .ge | .eqB => true
  | _ => false

/-- `<`, `>`. -/
def _root_.Solidity.BinOp.isStrict : BinOp → Bool
  | .lt | .gt => true
  | _ => false

/-- **A comparison true of the values is true of their floors.** -/
theorem cmp_mono (S : ApfSet) (op : BinOp) {vx vy : Bool} {x' y' x y : Int} (h0 : 0 ≤ x') (h0' : 0 ≤ y')
    (hb : x' < ((2 ^ 256 : Nat) : Int)) (hb' : y' < ((2 ^ 256 : Nat) : Int))
    (hx : FRel S vx x' x) (hy : FRel S vy y' y) (hs : op.isStrict = true → (vx && vy) = false)
    (h : cmpOf op x' y' = true) : cmpOf op x y = true := by
  cases op <;> simp only [cmpOf, decide_eq_true_eq, Bool.false_eq_true] at h ⊢
  · exact lt_mono S h0 hb' hx hy (hs rfl) h
  · exact lt_mono S h0' hb hy hx (by rw [Bool.and_comm]; exact hs rfl) h
  · exact le_mono S h0 h0' hx hy h
  · exact le_mono S h0' h0 hy hx h
  · exact eq_mono S h0 hx hy h

/-- The values in the index set. -/
def InS (S : List Int) (g : State C []) (ν : AEnv) (x : LTm C (.val .uint)) : Prop :=
  ∀ v, (x.eval g ν : Option PrimTy.uint.Denote) = some v → v.1 ∈ S

/-- Their successors in the index set, where they are words. -/
def InSucc (S : List Int) (g : State C []) (ν : AEnv) (x : LTm C (.val .uint)) : Prop :=
  ∀ v, (x.eval g ν : Option PrimTy.uint.Denote) = some v → v.1 + 1 < ((2 ^ 256 : Nat) : Int) → v.1 + 1 ∈ S

/-- A variable of `ks`. -/
def LTm.isBVar (ks : List Nat) : {s : Srt} → LTm C s → Bool
  | _, .var k => decide (k ∈ ks)
  | _, _ => false

theorem LTm.isBVar_spec {ks : List Nat} {x : LTm C (.val .uint)} (h : x.isBVar ks = true) :
    ∃ k ∈ ks, x = .var k := by
  cases x with
  | var k => exact ⟨k, by simpa only [LTm.isBVar, decide_eq_true_eq] using h, rfl⟩
  | _ => simp only [LTm.isBVar, Bool.false_eq_true] at h

/-- **An operand of a guard comparison**: a block variable, or a ground
term of the index set (`Gd`) whose successor is in it too (`Lo`); it may
halt (`k < x - 1`). -/
inductive IdxP {Rs : List Name} (Gd Lo : LTm C (.val .uint) → Prop) (ks : List Nat)
    (Bs : List Parameter) : Bool → {a : LTm C (.val .uint)} → ApfTm Rs false a → Prop where
  | var (k : Nat) (hk : k ∈ ks) (hv : ApfTm Rs false (LTm.var (p := .uint) k)) : IdxP Gd Lo ks Bs true hv
  | gnd {a : LTm C (.val .uint)} (ha : ApfTm Rs false a) (hr : ha.Rel ks Bs Gd)
      (hb : ∀ q ∈ a.parameters, q ∉ Bs) (hs : Gd a) (hl : Lo a) :
      IdxP Gd Lo ks Bs false ha

/-- **A guard**: `&&` and `||` of comparisons of operands (`IdxP`), never a
strict one of two block variables.  `tot` where it returns wherever its
atoms do (its operands block variables or total); `ds` where it returns
at the floors wherever it returned at the keys, as the left operand of
every `||` must: a comparison does, a `&&` where its left operand does and
its right one is total (a `&&` that skipped a halting right operand at the
keys may evaluate it at the floors), a `||` where its right one is total. -/
inductive GuardP {Rs : List Name} (Gd Lo : LTm C (.val .uint) → Prop) (ks : List Nat)
    (Bs : List Parameter) : Bool → Bool → {p : PrimTy} → {t : LTm C (.val p)} → ApfTm Rs false t → Prop where
  | and (h : BinOp.and.accepts .bool = true) {ta da tb db : Bool} {a b : LTm C (.val .bool)}
      {ha : ApfTm Rs false a} {hb : ApfTm Rs false b} :
      GuardP Gd Lo ks Bs ta da ha → GuardP Gd Lo ks Bs tb db hb →
      GuardP Gd Lo ks Bs (ta && tb) (da && tb) (.binop .and h ha hb)
  | or (h : BinOp.or.accepts .bool = true) {ta tb db : Bool} {a b : LTm C (.val .bool)}
      {ha : ApfTm Rs false a} {hb : ApfTm Rs false b} :
      GuardP Gd Lo ks Bs ta true ha → GuardP Gd Lo ks Bs tb db hb →
      GuardP Gd Lo ks Bs (ta && tb) tb (.binop .or h ha hb)
  | cmp (op : BinOp) (h : op.accepts .uint = true) (hop : op.isGuardOp = true) {va vb : Bool}
      {a b : LTm C (.val .uint)} {ha : ApfTm Rs false a} {hb : ApfTm Rs false b} {tot : Bool} :
      IdxP Gd Lo ks Bs va ha → IdxP Gd Lo ks Bs vb hb → (op.isStrict = true → (va && vb) = false) →
      (tot = true → (a.isBVar ks || a.totalB) = true ∧ (b.isBVar ks || b.totalB) = true) →
      GuardP Gd Lo ks Bs tot true (.binop op h ha hb)

/-- `true`, at `bool`. -/
def IsTrue : (p : PrimTy) → p.Denote → Prop
  | .bool, b => b = true
  | _, _ => False

/-- The setting of a rebuilt storage: `μ'` reads the keys, `μ` their
floors; both are `ν` off the binders; the terms `Gd` and their successors
`Lo` are in the index set at `ν`. -/
structure Setting (g : State C []) (st' : Storage C) (Rs : List Name) (S : ApfSet)
    (Gd Lo : LTm C (.val .uint) → Prop) (ks : List Nat) (Bs : List Parameter) (ν μ' μ : AEnv) : Prop where
  surg : Surg g st' Rs (lastU S)
  gdS : ∀ x, Gd x → InS S.vals g ν x
  loS : ∀ x, Lo x → InSucc S.vals g ν x
  loT : ∀ x, Lo x → InS S.strict g ν x
  hμ : ∀ q, q ∉ ApfTm.ksP ks → q.read μ' = q.read μ
  hk : ∀ k ∈ ks, μ.get .uint k = lastU S (μ'.get .uint k)
  hν : ∀ q, q ∉ Bs → q.read μ = q.read ν

section Setting

variable {g : State C []} {st' : Storage C} {Rs : List Name} {S : ApfSet}
  {Gd Lo : LTm C (.val .uint) → Prop} {ks : List Nat} {Bs : List Parameter} {ν μ' μ : AEnv}

theorem Setting.gd (hs : Setting g st' Rs S Gd Lo ks Bs ν μ' μ) :
    ∀ x, Gd x → ∀ v, (x.eval g ν : Option PrimTy.uint.Denote) = some v → lastU S v = v :=
  fun _ hx v hv => Subtype.ext (lastIn_fix S (hs.gdS _ hx v hv) (uintVal_bounds v).1)

theorem Setting.eval (hs : Setting g st' Rs S Gd Lo ks Bs ν μ' μ) {s : Srt}
    {t : LTm C s} (ht : ApfTm Rs false t) (hr : ht.Rel ks Bs Gd) :
    t.eval { g with storage := st' } μ' = t.eval g μ :=
  ApfTm.eval_rel g st' hs.surg hs.gd hs.hμ hs.hk hs.hν ht hr

theorem IdxP.values (hs : Setting g st' Rs S Gd Lo ks Bs ν μ' μ) {v : Bool}
    {a : LTm C (.val .uint)} {ha : ApfTm Rs false a} (hi : IdxP Gd Lo ks Bs v ha) {x' : PrimTy.uint.Denote}
    (hx' : (a.eval { g with storage := st' } μ' : Option _) = some x') :
    ∃ x : PrimTy.uint.Denote, (a.eval g μ : Option _) = some x ∧ FRel S v x'.1 x.1 := by
  cases hi with
  | var k hk _ =>
    obtain rfl : μ'.get .uint k = x' := Option.some.inj hx'
    refine ⟨μ.get .uint k, rfl, ?_⟩
    show (μ.get .uint k).1 = lastIn S (μ'.get .uint k).1
    rw [hs.hk k hk]
    rfl
  | gnd ha hr hb hsS hl =>
    have hx : (a.eval g μ : Option PrimTy.uint.Denote) = some x' := (hs.eval ha hr).symm.trans hx'
    have hxν : (a.eval g ν : Option PrimTy.uint.Denote) = some x' := by
      rw [← hx]; exact (a.eval_agree_parameters g fun q hq => hs.hν q (hb q hq)).symm
    exact ⟨x', hx, rfl, hs.gdS _ hsS x' hxν, hs.loT _ hl x' hxν, hs.loS _ hl x' hxν⟩

end Setting

theorem binopT_andB (h : BinOp.and.accepts .bool = true) (x y : Bool) :
    binopT .and h x (some y) = some (x && y) := by cases x <;> cases y <;> rfl

theorem binopT_orB (h : BinOp.or.accepts .bool = true) (x y : Bool) :
    binopT .or h x (some y) = some (x || y) := by cases x <;> cases y <;> rfl

theorem binopT_and_true (h : BinOp.and.accepts .bool = true) (x : Bool) (y : Option Bool)
    (e : binopT .and h x y = some true) : x = true ∧ y = some true := by
  cases x <;> rcases y with _ | _ | _ <;> first | exact ⟨rfl, rfl⟩ | cases e

theorem binopT_or_true (h : BinOp.or.accepts .bool = true) (x : Bool) (y : Option Bool)
    (e : binopT .or h x y = some true) : x = true ∨ (x = false ∧ y = some true) := by
  cases x <;> rcases y with _ | _ | _ <;> first | exact .inl rfl | exact .inr ⟨rfl, rfl⟩ | cases e

theorem binopT_cmp_some (op : BinOp) (h : op.accepts .uint = true) (hop : op.isGuardOp = true)
    (x y : PrimTy.uint.Denote) :
    ∃ c, binopT op h x (some y) = some c ∧ (IsTrue (op.ret .uint) c ↔ cmpOf op x.1 y.1 = true) := by
  cases op <;> simp only [BinOp.isGuardOp, Bool.false_eq_true] at hop <;> exact ⟨_, rfl, Iff.rfl⟩

theorem binopT_cmp_none (op : BinOp) (h : op.accepts .uint = true) (hop : op.isGuardOp = true)
    (x : PrimTy.uint.Denote) : binopT op h x none = none := by
  cases op <;> simp only [BinOp.isGuardOp, Bool.false_eq_true] at hop <;> rfl

theorem eval_of_tot (g : State C []) (ν : AEnv) {ks : List Nat} {a : LTm C (.val .uint)}
    (h : (a.isBVar ks || a.totalB) = true) : ∃ x, (a.eval g ν : Option PrimTy.uint.Denote) = some x := by
  rcases Bool.or_eq_true _ _ ▸ h with h | h
  · obtain ⟨k, _, rfl⟩ := LTm.isBVar_spec h
    exact ⟨_, rfl⟩
  · exact Option.isSome_iff_exists.1 (LTm.totalB_eval g ν a h)

/-- **A total guard returns.** -/
theorem GuardP.defined {Rs : List Name} {Gd Lo : LTm C (.val .uint) → Prop} {ks : List Nat}
    {Bs : List Parameter} (g : State C []) (μ : AEnv) {tot ds : Bool} {p : PrimTy}
    {t : LTm C (.val p)} {ht : ApfTm Rs false t} (hg : GuardP Gd Lo ks Bs tot ds ht) :
    tot = true → ∃ x : p.Denote, (t.eval g μ : Option _) = some x := by
  induction hg with
  | and h _ _ iha ihb =>
    intro htot
    rw [Bool.and_eq_true] at htot
    obtain ⟨a, ha⟩ := iha htot.1
    obtain ⟨b, hb⟩ := ihb htot.2
    exact ⟨a && b, by rw [LTm.eval_app2, Close.Op2.eval_binop, ha, Option.bind_some, hb]; exact binopT_andB h a b⟩
  | or h _ _ iha ihb =>
    intro htot
    rw [Bool.and_eq_true] at htot
    obtain ⟨a, ha⟩ := iha htot.1
    obtain ⟨b, hb⟩ := ihb htot.2
    exact ⟨a || b, by rw [LTm.eval_app2, Close.Op2.eval_binop, ha, Option.bind_some, hb]; exact binopT_orB h a b⟩
  | cmp op h hop _ _ _ htt =>
    intro htot
    obtain ⟨x, hx⟩ := eval_of_tot g μ (htt htot).1
    obtain ⟨y, hy⟩ := eval_of_tot g μ (htt htot).2
    obtain ⟨c, e, -⟩ := binopT_cmp_some op h hop x y
    exact ⟨c, by rw [LTm.eval_app2, Close.Op2.eval_binop, hx, Option.bind_some, hy]; exact e⟩

/-- **A guard at the keys and at their floors**: true at the keys, true at
the floors; where `ds`, returning at the keys, returning at the floors. -/
theorem GuardP.floors {g : State C []} {st' : Storage C} {Rs : List Name} {S : ApfSet}
    {Gd Lo : LTm C (.val .uint) → Prop} {ks : List Nat} {Bs : List Parameter} {ν μ' μ : AEnv}
    (hs : Setting g st' Rs S Gd Lo ks Bs ν μ' μ) {tot ds : Bool} {p : PrimTy}
    {t : LTm C (.val p)} {ht : ApfTm Rs false t} (hg : GuardP Gd Lo ks Bs tot ds ht) :
    (∀ x' : p.Denote, (t.eval { g with storage := st' } μ' : Option _) = some x' → IsTrue p x' →
      ∃ x : p.Denote, (t.eval g μ : Option _) = some x ∧ IsTrue p x) ∧
    (ds = true → ∀ x' : p.Denote, (t.eval { g with storage := st' } μ' : Option _) = some x' →
      ∃ x : p.Denote, (t.eval g μ : Option _) = some x) := by
  induction hg with
  | @and h ta da tb db a b ha hb _ hgb iha ihb =>
    refine ⟨fun c' hc' htc => ?_, fun hds c' hc' => ?_⟩
    · have htc' : c' = true := htc
      subst htc'
      rw [LTm.eval_app2, Close.Op2.eval_binop] at hc'
      cases hxa : (a.eval { g with storage := st' } μ' : Option Bool) with
      | none => rw [hxa] at hc'; cases hc'
      | some a' =>
        rw [hxa, Option.bind_some] at hc'
        obtain ⟨rfl, hyb⟩ := binopT_and_true h a' _ hc'
        obtain ⟨a0, ha0, ht0⟩ := iha.1 true hxa rfl
        obtain ⟨b0, hb0, ht1⟩ := ihb.1 true hyb rfl
        have e0 : a0 = true := ht0
        have e1 : b0 = true := ht1
        subst e0 e1
        exact ⟨true, by rw [LTm.eval_app2, Close.Op2.eval_binop, ha0, Option.bind_some, hb0]; rfl, rfl⟩
    · rw [Bool.and_eq_true] at hds
      rw [LTm.eval_app2, Close.Op2.eval_binop] at hc'
      cases hxa : (a.eval { g with storage := st' } μ' : Option Bool) with
      | none => rw [hxa] at hc'; cases hc'
      | some a' =>
        obtain ⟨a0, ha0⟩ := iha.2 hds.1 a' hxa
        obtain ⟨b0, hb0⟩ := GuardP.defined g μ hgb hds.2
        exact ⟨a0 && b0, by rw [LTm.eval_app2, Close.Op2.eval_binop, ha0, Option.bind_some, hb0]; exact binopT_andB h a0 b0⟩
  | @or h ta tb db a b ha hb _ hgb iha ihb =>
    refine ⟨fun c' hc' htc => ?_, fun hds c' hc' => ?_⟩
    · have htc' : c' = true := htc
      subst htc'
      rw [LTm.eval_app2, Close.Op2.eval_binop] at hc'
      cases hxa : (a.eval { g with storage := st' } μ' : Option Bool) with
      | none => rw [hxa] at hc'; cases hc'
      | some a' =>
        rw [hxa, Option.bind_some] at hc'
        rcases binopT_or_true h a' _ hc' with rfl | ⟨rfl, hyb⟩
        · obtain ⟨a0, ha0, ht0⟩ := iha.1 true hxa rfl
          have e0 : a0 = true := ht0
          subst e0
          exact ⟨true, by rw [LTm.eval_app2, Close.Op2.eval_binop, ha0, Option.bind_some]; rfl, rfl⟩
        · obtain ⟨b0, hb0, ht1⟩ := ihb.1 true hyb rfl
          have e1 : b0 = true := ht1
          subst e1
          obtain ⟨a0, ha0⟩ := iha.2 rfl false hxa
          refine ⟨a0 || true, ?_, Bool.or_true a0⟩
          rw [LTm.eval_app2, Close.Op2.eval_binop, ha0, Option.bind_some, hb0]
          exact binopT_orB h a0 true
    · rw [LTm.eval_app2, Close.Op2.eval_binop] at hc'
      cases hxa : (a.eval { g with storage := st' } μ' : Option Bool) with
      | none => rw [hxa] at hc'; cases hc'
      | some a' =>
        obtain ⟨a0, ha0⟩ := iha.2 rfl a' hxa
        obtain ⟨b0, hb0⟩ := GuardP.defined g μ hgb hds
        exact ⟨a0 || b0, by rw [LTm.eval_app2, Close.Op2.eval_binop, ha0, Option.bind_some, hb0]; exact binopT_orB h a0 b0⟩
  | @cmp op h hop va vb a b ha hb tot ia ib hst _ =>
    have key : ∀ c', (LTm.eval { g with storage := st' } μ' (.app2 (.binop op h) a b) : Option _) = some c' →
        ∃ c2, (LTm.eval g μ (.app2 (.binop op h) a b) : Option _) = some c2 ∧
          (IsTrue (op.ret .uint) c' → IsTrue (op.ret .uint) c2) := by
      intro c' hc'
      rw [LTm.eval_app2, Close.Op2.eval_binop] at hc'
      cases hxa : (a.eval { g with storage := st' } μ' : Option PrimTy.uint.Denote) with
      | none => rw [hxa] at hc'; cases hc'
      | some x' =>
        rw [hxa, Option.bind_some] at hc'
        cases hyb : (b.eval { g with storage := st' } μ' : Option PrimTy.uint.Denote) with
        | none => rw [hyb, binopT_cmp_none op h hop] at hc'; cases hc'
        | some y' =>
          rw [hyb] at hc'
          obtain ⟨c1, e1, i1⟩ := binopT_cmp_some op h hop x' y'
          rw [e1] at hc'
          cases hc'
          obtain ⟨x, hx, hfx⟩ := ia.values hs hxa
          obtain ⟨y, hy, hfy⟩ := ib.values hs hyb
          obtain ⟨c2, e2, i2⟩ := binopT_cmp_some op h hop x y
          have bx := uintVal_bounds x'
          have bY := uintVal_bounds y'
          refine ⟨c2, ?_, fun htc => i2.2 (cmp_mono S op bx.1 bY.1 bx.2 bY.2 hfx hfy hst (i1.1 htc))⟩
          rw [LTm.eval_app2, Close.Op2.eval_binop, hx, Option.bind_some, hy]
          exact e2
    exact ⟨fun c' hc' htc => (key c' hc').imp fun _ h => ⟨h.1, h.2 htc⟩,
      fun _ c' hc' => (key c' hc').imp fun _ h => h.1⟩

/-- **A guard true at the keys is true at their floors.** -/
theorem GuardP.mono {g : State C []} {st' : Storage C} {Rs : List Name} {S : ApfSet}
    {Gd Lo : LTm C (.val .uint) → Prop} {ks : List Nat} {Bs : List Parameter} {ν μ' μ : AEnv}
    (hs : Setting g st' Rs S Gd Lo ks Bs ν μ' μ) {tot ds : Bool} {p : PrimTy}
    {t : LTm C (.val p)} {ht : ApfTm Rs false t} (hg : GuardP Gd Lo ks Bs tot ds ht) :
    ∀ x' : p.Denote, (t.eval { g with storage := st' } μ' : Option _) = some x' → IsTrue p x' →
      ∃ x : p.Denote, (t.eval g μ : Option _) = some x ∧ IsTrue p x :=
  (GuardP.floors hs hg).1

/-! ## Instances -/

/-- `t[u/k]`: the `uint` position `k` replaced by `u`. -/
def LTm.subst1 (k : Nat) (u : LTm C (.val .uint)) : {s : Srt} → LTm C s → LTm C s
  | _, @LTm.var _ .uint j => if j = k then u else .var j
  | _, .var j => .var j
  | _, .app0 o => .app0 o
  | _, .app1 o a => .app1 o (LTm.subst1 k u a)
  | _, .app2 o a b => .app2 o (LTm.subst1 k u a) (LTm.subst1 k u b)
  | _, .app3 o a b c => .app3 o (LTm.subst1 k u a) (LTm.subst1 k u b) (LTm.subst1 k u c)
  | _, .index it q i => .index it (LTm.subst1 k u q) (LTm.subst1 k u i)
  | _, .obsW q => .obsW (LTm.subst1 k u q)
  | _, .obsL q => .obsL (LTm.subst1 k u q)
  | _, .obsH q => .obsH (LTm.subst1 k u q)
  | _, .seq d a => .seq (LTm.subst1 k u d) (LTm.subst1 k u a)
  | _, .orElse a b => .orElse (LTm.subst1 k u a) (LTm.subst1 k u b)
  | _, .kite a b t e => .kite (LTm.subst1 k u a) (LTm.subst1 k u b) (LTm.subst1 k u t) (LTm.subst1 k u e)
  | _, .err => .err

theorem AEnv.get_set_uint_other (ν : AEnv) (k j : Nat) (v : PrimTy.uint.Denote) {p : PrimTy}
    (hp : p ≠ .uint) : (ν.set .uint k v).get p j = ν.get p j := by
  cases p
  · rfl
  · exact absurd rfl hp
  · rfl

/-- **Substitution is evaluation at the value.** -/
theorem LTm.eval_subst1 (g : State C []) (ν : AEnv) (k : Nat) (u : LTm C (.val .uint))
    {v : PrimTy.uint.Denote} (hu : (u.eval g ν : Option PrimTy.uint.Denote) = some v) {s : Srt}
    (t : LTm C s) : (LTm.subst1 k u t).eval g ν = t.eval g (ν.set .uint k v) := by
  induction t with
  | @var p j =>
    cases p with
    | uint =>
      show ((if j = k then u else LTm.var j).eval g ν : Option _) = some ((ν.set .uint k v).get .uint j)
      by_cases hj : j = k
      · subst hj; rw [if_pos rfl, hu, AEnv.get_set_self]
      · rw [if_neg hj, AEnv.get_set_ne ν .uint .uint v hj]; rfl
    | bool => exact congrArg some (AEnv.get_set_uint_other ν k j v (by decide)).symm
    | int => exact congrArg some (AEnv.get_set_uint_other ν k j v (by decide)).symm
  | app0 o => rfl
  | app1 o a ih => show (LTm.app1 o _).eval g ν = _; rw [LTm.eval_app1, LTm.eval_app1, ih]
  | app2 o a b iha ihb => show (LTm.app2 o _ _).eval g ν = _; rw [LTm.eval_app2, LTm.eval_app2, iha, ihb]
  | app3 o a b c iha ihb ihc =>
    show (LTm.app3 o _ _ _).eval g ν = _; rw [LTm.eval_app3, LTm.eval_app3, iha, ihb, ihc]
  | index it q i ihq ihi => show (LTm.index it _ _).eval g ν = _; rw [LTm.eval_index, LTm.eval_index, ihq, ihi]
  | obsW q ih => show (LTm.obsW _).eval g ν = _; rw [LTm.eval_obsW, LTm.eval_obsW, ih]
  | obsL q ih => show (LTm.obsL _).eval g ν = _; rw [LTm.eval_obsL, LTm.eval_obsL, ih]
  | obsH q ih => show (LTm.obsH _).eval g ν = _; rw [LTm.eval_obsH, LTm.eval_obsH, ih]
  | seq d a ihd iha => show (LTm.seq _ _).eval g ν = _; rw [LTm.eval_seq, LTm.eval_seq, ihd, iha]
  | orElse a b iha ihb => show (LTm.orElse _ _).eval g ν = _; rw [LTm.eval_orElse, LTm.eval_orElse, iha, ihb]
  | kite a b t e iha ihb iht ihe =>
    show (LTm.kite _ _ _ _).eval g ν = _; rw [LTm.eval_kite, LTm.eval_kite, iha, ihb, iht, ihe]
  | err => rfl

/-- Quantifier-free. -/
def LFml.qfB : LFml C → Bool
  | .tt | .eq _ _ => true
  | .not φ => φ.qfB
  | .and φ ψ | .imp φ ψ => φ.qfB && ψ.qfB
  | .all .. => false

/-- `φ[u/k]`, on a quantifier-free formula. -/
def LFml.subst1 (k : Nat) (u : LTm C (.val .uint)) : LFml C → LFml C
  | .tt => .tt
  | .eq a b => .eq (LTm.subst1 k u a) (LTm.subst1 k u b)
  | .not φ => .not (φ.subst1 k u)
  | .and φ ψ => .and (φ.subst1 k u) (ψ.subst1 k u)
  | .imp φ ψ => .imp (φ.subst1 k u) (ψ.subst1 k u)
  | .all j p φ => .all j p φ

theorem LFml.qfB_subst1 (k : Nat) (u : LTm C (.val .uint)) : ∀ φ : LFml C, φ.qfB = true → (φ.subst1 k u).qfB = true
  | .tt, _ | .eq _ _, _ => rfl
  | .not φ, h => LFml.qfB_subst1 k u φ h
  | .and φ ψ, h | .imp φ ψ, h => by
    simp only [LFml.qfB, Bool.and_eq_true] at h
    simp only [LFml.subst1, LFml.qfB, LFml.qfB_subst1 k u φ h.1, LFml.qfB_subst1 k u ψ h.2, Bool.and_self]

theorem LFml.holds_subst1 (g : State C []) (ν : AEnv) (k : Nat) (u : LTm C (.val .uint))
    {v : PrimTy.uint.Denote} (hu : (u.eval g ν : Option PrimTy.uint.Denote) = some v) :
    ∀ φ : LFml C, φ.qfB = true → ((φ.subst1 k u).holds g ν ↔ φ.holds g (ν.set .uint k v))
  | .tt, _ => Iff.rfl
  | .eq a b, _ => by simp only [LFml.subst1, LFml.holds, LTm.eval_subst1 g ν k u hu]
  | .not φ, h => not_congr (LFml.holds_subst1 g ν k u hu φ h)
  | .and φ ψ, h => by
    simp only [LFml.qfB, Bool.and_eq_true] at h
    exact and_congr (LFml.holds_subst1 g ν k u hu φ h.1) (LFml.holds_subst1 g ν k u hu ψ h.2)
  | .imp φ ψ, h => by
    simp only [LFml.qfB, Bool.and_eq_true] at h
    exact imp_congr (LFml.holds_subst1 g ν k u hu φ h.1) (LFml.holds_subst1 g ν k u hu ψ h.2)

/-- A chain of `uint` binders over a quantifier-free body. -/
def LFml.chainQF : LFml C → Bool
  | .all _ .uint φ => φ.chainQF
  | φ => φ.qfB

/-- The chain's variables. -/
def LFml.chainVars : LFml C → List Nat
  | .all k .uint φ => k :: φ.chainVars
  | _ => []

/-- The chain's body. -/
def LFml.chainBody : LFml C → LFml C
  | .all _ .uint φ => φ.chainBody
  | φ => φ

/-- **The block's instances at `us`**: one per tuple, each guarded by its
terms returning. -/
def LFml.inst (us : List (LTm C (.val .uint))) : LFml C → LFml C
  | .all k .uint φ => LFml.conj (us.map fun u => .imp (.eq u u) ((φ.inst us).subst1 k u))
  | φ => φ

theorem LFml.qfB_conj : ∀ ds : List (LFml C), (∀ d ∈ ds, d.qfB = true) → (LFml.conj ds).qfB = true
  | [], _ => rfl
  | [d], h => h d List.mem_cons_self
  | d :: e :: ds, h => by
    show (d.qfB && (LFml.conj (e :: ds)).qfB) = true
    rw [h d List.mem_cons_self, LFml.qfB_conj (e :: ds) fun d' hd' => h d' (List.mem_cons_of_mem _ hd')]
    rfl

theorem LFml.qfB_inst (us : List (LTm C (.val .uint))) : ∀ φ : LFml C, φ.chainQF = true → (φ.inst us).qfB = true
  | .all k .uint φ, h => LFml.qfB_conj _ fun d hd => by
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 hd
      show (true && ((φ.inst us).subst1 k u).qfB) = true
      rw [LFml.qfB_subst1 k u _ (LFml.qfB_inst us φ h)]
      rfl
  | .all _ .bool _, h | .all _ .int _, h => h
  | .tt, h | .eq _ _, h | .not _, h | .and _ _, h | .imp _ _, h => h

/-- **The block implies its instances.** -/
theorem LFml.inst_sound (g : State C []) (us : List (LTm C (.val .uint))) :
    ∀ (φ : LFml C) (ν : AEnv), φ.chainQF = true → φ.holds g ν → (φ.inst us).holds g ν
  | .all k .uint φ, ν, hc, h => by
    show (LFml.conj _).holds g ν
    rw [LFml.holds_conj]
    intro d hd
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hd
    intro hu
    obtain ⟨v, hv, -⟩ := (LFml.holds_eq_iff g ν u u).1 hu
    rw [LFml.holds_subst1 g ν k u hv _ (LFml.qfB_inst us φ hc)]
    exact LFml.inst_sound g us φ _ hc (h v)
  | .all _ .bool _, _, _, h | .all _ .int _, _, _, h => h
  | .tt, _, _, h | .eq _ _, _, _, h | .not _, _, _, h | .and _ _, _, _, h | .imp _ _, _, _, h => h

/-! ## Blocks, instantiated at their polarity -/

/-- The root a path of keys and members starts at. -/
def LTm.pathRoot? : {s : Srt} → LTm C s → Option Name
  | _, .app0 (.root r _) => some r
  | _, .index .map q _ => q.pathRoot?
  | _, .app1 (.field _) q => q.pathRoot?
  | _, _ => none

/-- The term reads a root of `Rs` at a variable of `ks`, as a `uint` key of
a path. -/
def LTm.readsAtVar (Rs : List Name) (ks : List Nat) : {s : Srt} → LTm C s → Bool
  | _, .index (k := .uint) .map q (.var j) =>
    (q.pathRoot?.any (· ∈ Rs) && decide (j ∈ ks)) || q.readsAtVar Rs ks
  | _, .app1 _ a | _, .obsW a | _, .obsL a | _, .obsH a => a.readsAtVar Rs ks
  | _, .app2 _ a b | _, .index _ a b | _, .seq a b | _, .orElse a b => a.readsAtVar Rs ks || b.readsAtVar Rs ks
  | _, .app3 _ a b c => a.readsAtVar Rs ks || b.readsAtVar Rs ks || c.readsAtVar Rs ks
  | _, .kite a b t e => a.readsAtVar Rs ks || b.readsAtVar Rs ks || t.readsAtVar Rs ks || e.readsAtVar Rs ks
  | _, _ => false

/-- The roots the term reads at a variable of `ks`. -/
def LTm.rootsAtVar (ks : List Nat) : {s : Srt} → LTm C s → List Name
  | _, .index (k := .uint) .map q (.var j) =>
    (if j ∈ ks then q.pathRoot?.toList else []) ++ q.rootsAtVar ks
  | _, .app1 _ a | _, .obsW a | _, .obsL a | _, .obsH a => a.rootsAtVar ks
  | _, .app2 _ a b | _, .index _ a b | _, .seq a b | _, .orElse a b => a.rootsAtVar ks ++ b.rootsAtVar ks
  | _, .app3 _ a b c => a.rootsAtVar ks ++ b.rootsAtVar ks ++ c.rootsAtVar ks
  | _, .kite a b t e => a.rootsAtVar ks ++ b.rootsAtVar ks ++ t.rootsAtVar ks ++ e.rootsAtVar ks
  | _, _ => []

def LFml.readsAtVar (Rs : List Name) (ks : List Nat) : LFml C → Bool
  | .tt => false
  | .eq a b => a.readsAtVar Rs ks || b.readsAtVar Rs ks
  | .not φ | .all _ _ φ => φ.readsAtVar Rs ks
  | .and φ ψ | .imp φ ψ => φ.readsAtVar Rs ks || ψ.readsAtVar Rs ks

def LFml.rootsAtVar (ks : List Nat) : LFml C → List Name
  | .tt => []
  | .eq a b => a.rootsAtVar ks ++ b.rootsAtVar ks
  | .not φ | .all _ _ φ => φ.rootsAtVar ks
  | .and φ ψ | .imp φ ψ => φ.rootsAtVar ks ++ ψ.rootsAtVar ks

/-- **A block of the fragment's shape**: `uint` binders over a
quantifier-free body reading a root of `Rs` at one of them. -/
def LFml.isBlock (Rs : List Name) (φ : LFml C) : Bool :=
  φ.chainQF && !φ.chainVars.isEmpty && φ.chainBody.readsAtVar Rs φ.chainVars

/-- The roots the negative chains outside binders read at their
variables. -/
def LFml.blockRoots : Bool → LFml C → List Name
  | pol, .not φ => φ.blockRoots (!pol)
  | pol, .and φ ψ => φ.blockRoots pol ++ ψ.blockRoots pol
  | pol, .imp φ ψ => φ.blockRoots (!pol) ++ ψ.blockRoots pol
  | pol, .all k p φ =>
    if !pol && (LFml.all k p φ).chainQF then (LFml.all k p φ).chainBody.rootsAtVar (LFml.all k p φ).chainVars
    else []
  | _, _ => []

/-- **The body, each negative block replaced by its instances at `us`.** -/
def LFml.apfInst (Rs : List Name) (us : List (LTm C (.val .uint))) : Bool → LFml C → LFml C
  | pol, .not φ => .not (φ.apfInst Rs us (!pol))
  | pol, .and φ ψ => .and (φ.apfInst Rs us pol) (ψ.apfInst Rs us pol)
  | pol, .imp φ ψ => .imp (φ.apfInst Rs us (!pol)) (ψ.apfInst Rs us pol)
  | pol, .all k p φ =>
    if !pol && (LFml.all k p φ).isBlock Rs then (LFml.all k p φ).inst us else .all k p φ
  | _, φ => φ

/-- **Instantiation is sound**: at a positive polarity the instantiated
formula implies the formula, at a negative one the converse. -/
theorem LFml.apfInst_sound (g : State C []) (Rs : List Name) (us : List (LTm C (.val .uint))) :
    ∀ (φ : LFml C) (pol : Bool) (ν : AEnv),
      (pol = true → (φ.apfInst Rs us pol).holds g ν → φ.holds g ν) ∧
      (pol = false → φ.holds g ν → (φ.apfInst Rs us pol).holds g ν)
  | .not φ, pol, ν => by
    have ih := LFml.apfInst_sound g Rs us φ (!pol) ν
    cases pol
    · exact ⟨nofun, fun _ h h' => h (ih.1 rfl h')⟩
    · exact ⟨fun _ h h' => h (ih.2 rfl h'), nofun⟩
  | .and φ ψ, pol, ν => by
    have ih1 := LFml.apfInst_sound g Rs us φ pol ν
    have ih2 := LFml.apfInst_sound g Rs us ψ pol ν
    exact ⟨fun hp h => ⟨ih1.1 hp h.1, ih2.1 hp h.2⟩, fun hp h => ⟨ih1.2 hp h.1, ih2.2 hp h.2⟩⟩
  | .imp φ ψ, pol, ν => by
    have ih1 := LFml.apfInst_sound g Rs us φ (!pol) ν
    have ih2 := LFml.apfInst_sound g Rs us ψ pol ν
    cases pol
    · exact ⟨nofun, fun _ h h' => ih2.2 rfl (h (ih1.1 rfl h'))⟩
    · exact ⟨fun _ h h' => ih2.1 rfl (h (ih1.2 rfl h')), nofun⟩
  | .all k p φ, pol, ν => by
    refine ⟨fun hp h => ?_, fun hp h => ?_⟩
    · subst hp
      simpa only [LFml.apfInst, Bool.not_true, Bool.false_and, if_false] using h
    · subst hp
      show LFml.holds g ν (if (!false && (LFml.all k p φ).isBlock Rs) = true then
        (LFml.all k p φ).inst us else .all k p φ)
      split
      · rename_i hb
        simp only [LFml.isBlock, Bool.not_false, Bool.true_and, Bool.and_eq_true] at hb
        exact LFml.inst_sound g us _ ν hb.1.1 h
      · exact h
  | .tt, _, _ => ⟨fun _ h => h, fun _ h => h⟩
  | .eq _ _, _, _ => ⟨fun _ h => h, fun _ h => h⟩

/-! ## The refutation: a failing instance, a failing block -/

/-- The formulas of the fragment. -/
inductive ApfFml (Rs : List Name) : LFml C → Type where
  | tt : ApfFml Rs .tt
  | eq {p : PrimTy} {a b : LTm C (.val p)} (ha : ApfTm Rs false a) (hb : ApfTm Rs false b) : ApfFml Rs (.eq a b)
  | not {φ : LFml C} (h : ApfFml Rs φ) : ApfFml Rs (.not φ)
  | and {φ ψ : LFml C} (h₁ : ApfFml Rs φ) (h₂ : ApfFml Rs ψ) : ApfFml Rs (.and φ ψ)
  | imp {φ ψ : LFml C} (h₁ : ApfFml Rs φ) (h₂ : ApfFml Rs ψ) : ApfFml Rs (.imp φ ψ)
  | all (k : Nat) (p : PrimTy) {φ : LFml C} (h : ApfFml Rs φ) : ApfFml Rs (.all k p φ)

def ApfFml.ofFormula? (Rs : List Name) : (φ : LFml C) → Option (ApfFml Rs φ)
  | .tt => some .tt
  | .eq a b => do return .eq (← ApfTm.ofTerm? Rs false a) (← ApfTm.ofTerm? Rs false b)
  | .not φ => (ofFormula? Rs φ).map .not
  | .and φ ψ => do return .and (← ofFormula? Rs φ) (← ofFormula? Rs ψ)
  | .imp φ ψ => do return .imp (← ofFormula? Rs φ) (← ofFormula? Rs ψ)
  | .all k p φ => (ofFormula? Rs φ).map (.all k p)

section Refute

variable {Rs : List Name} {Gd Lo : LTm C (.val .uint) → Prop} {Bs : List Parameter}

/-- **A formula reading alike in the rebuilt storage**: each term ground
(`ApfTm.Rel` at no block variable), each binder among `Bs`. -/
def ApfFml.Frame (Bs : List Parameter) (Gd : LTm C (.val .uint) → Prop) : {φ : LFml C} → ApfFml Rs φ → Prop
  | _, .tt => True
  | _, .eq ha hb => ha.Rel [] Bs Gd ∧ hb.Rel [] Bs Gd
  | _, .not h => h.Frame Bs Gd
  | _, .and h₁ h₂ | _, .imp h₁ h₂ => h₁.Frame Bs Gd ∧ h₂.Frame Bs Gd
  | _, .all k p h => (⟨p, k⟩ : Parameter) ∈ Bs ∧ h.Frame Bs Gd

variable {g : State C []} {st' : Storage C} {S : ApfSet} {ks : List Nat} {ν μ' μ : AEnv}

/-- The setting under a binder of `Bs` that is no block variable. -/
theorem Setting.set (hs : Setting g st' Rs S Gd Lo ks Bs ν μ' μ) (p : PrimTy) (k : Nat) (v : p.Denote)
    (hB : (⟨p, k⟩ : Parameter) ∈ Bs) (hk : (⟨p, k⟩ : Parameter) ∉ ApfTm.ksP ks) :
    Setting g st' Rs S Gd Lo ks Bs ν (μ'.set p k v) (μ.set p k v) where
  surg := hs.surg
  gdS := hs.gdS
  loS := hs.loS
  loT := hs.loT
  hμ q hq := by
    by_cases he : q = ⟨p, k⟩
    · subst he; exact (Parameter.read_set ⟨p, k⟩ μ' v).trans (Parameter.read_set ⟨p, k⟩ μ v).symm
    · exact (Parameter.read_set_ne q ⟨p, k⟩ he μ' v).trans ((hs.hμ q hq).trans
        (Parameter.read_set_ne q ⟨p, k⟩ he μ v).symm)
  hk j hj := by
    have hne : (⟨p, k⟩ : Parameter) ≠ ⟨.uint, j⟩ := fun e => hk (e ▸ List.mem_map.2 ⟨j, hj, rfl⟩)
    have h1 : (μ.set p k v).get .uint j = μ.get .uint j :=
      Parameter.read_set_ne ⟨.uint, j⟩ ⟨p, k⟩ (Ne.symm hne) μ v
    have h2 : (μ'.set p k v).get .uint j = μ'.get .uint j :=
      Parameter.read_set_ne ⟨.uint, j⟩ ⟨p, k⟩ (Ne.symm hne) μ' v
    rw [h1, h2]
    exact hs.hk j hj
  hν q hq := by
    have hne : q ≠ ⟨p, k⟩ := fun e => hq (e ▸ hB)
    exact (Parameter.read_set_ne q ⟨p, k⟩ hne μ v).trans (hs.hν q hq)

/-- **Outside the blocks the formula reads alike.** -/
theorem ApfFml.frame_holds : ∀ {φ : LFml C} (h : ApfFml Rs φ) {μ : AEnv},
    Setting g st' Rs S Gd Lo [] Bs ν μ μ → h.Frame Bs Gd →
      (φ.holds { g with storage := st' } μ ↔ φ.holds g μ)
  | _, .tt, _, _, _ => Iff.rfl
  | _, .eq ha hb, _, hs, hf => by
    rw [LFml.holds_eq_iff, LFml.holds_eq_iff, hs.eval ha hf.1, hs.eval hb hf.2]
  | _, .not h, _, hs, hf => not_congr (ApfFml.frame_holds h hs hf)
  | _, .and h₁ h₂, _, hs, hf => and_congr (ApfFml.frame_holds h₁ hs hf.1) (ApfFml.frame_holds h₂ hs hf.2)
  | _, .imp h₁ h₂, _, hs, hf => imp_congr (ApfFml.frame_holds h₁ hs hf.1) (ApfFml.frame_holds h₂ hs hf.2)
  | _, .all k p h, _, hs, hf => forall_congr' fun v =>
      ApfFml.frame_holds h (hs.set p k v hf.1 (fun h => nomatch h)) hf.2

/-- **A guard atom**: a guard against `true`, or an equation of operands. -/
inductive GAtom (Gd Lo : LTm C (.val .uint) → Prop) (ks : List Nat) (Bs : List Parameter) :
    {p : PrimTy} → {a b : LTm C (.val p)} → ApfTm Rs false a → ApfTm Rs false b → Prop where
  | tt {tot ds : Bool} {G : LTm C (.val .bool)} {hG : ApfTm Rs false G}
      {hT : ApfTm Rs false (LTm.app0 (.lit (p := .bool) true))} :
      GuardP Gd Lo ks Bs tot ds hG → GAtom Gd Lo ks Bs hG hT
  | idx {a b : LTm C (.val .uint)} {ha : ApfTm Rs false a} {hb : ApfTm Rs false b} {va vb : Bool} :
      IdxP Gd Lo ks Bs va ha → IdxP Gd Lo ks Bs vb hb → GAtom Gd Lo ks Bs ha hb

/-- **A block body of the fragment**, at a polarity: guard atoms only in
negative positions, every other atom read alike. -/
def ApfFml.BodyOk (Gd Lo : LTm C (.val .uint) → Prop) (ks : List Nat) (Bs : List Parameter) :
    Bool → {φ : LFml C} → ApfFml Rs φ → Prop
  | _, _, .tt => True
  | pol, _, .eq ha hb => (ha.Rel ks Bs Gd ∧ hb.Rel ks Bs Gd) ∨ (pol = false ∧ GAtom Gd Lo ks Bs ha hb)
  | pol, _, .not h => h.BodyOk Gd Lo ks Bs (!pol)
  | pol, _, .and h₁ h₂ => h₁.BodyOk Gd Lo ks Bs pol ∧ h₂.BodyOk Gd Lo ks Bs pol
  | pol, _, .imp h₁ h₂ => h₁.BodyOk Gd Lo ks Bs (!pol) ∧ h₂.BodyOk Gd Lo ks Bs pol
  | _, _, .all .. => False

theorem GAtom.holds (hs : Setting g st' Rs S Gd Lo ks Bs ν μ' μ) {p : PrimTy} {a b : LTm C (.val p)}
    {ha : ApfTm Rs false a} {hb : ApfTm Rs false b} (hg : GAtom Gd Lo ks Bs ha hb) :
    (LFml.eq a b).holds { g with storage := st' } μ' → (LFml.eq a b).holds g μ := by
  cases hg with
  | @tt tot ds G hG hT hg =>
    intro h
    cases hx' : (G.eval { g with storage := st' } μ' : Option Bool) with
    | none => simp only [LFml.holds, hx'] at h
    | some x' =>
      simp only [LFml.holds, hx'] at h
      obtain ⟨x, hx, ht⟩ := hg.mono hs x' hx' h
      simp only [LFml.holds, hx]
      exact ht
  | idx ia ib =>
    intro h
    obtain ⟨x', hx', hy'⟩ := (LFml.holds_eq_iff _ _ _ _).1 h
    obtain ⟨x, hx, hfx⟩ := ia.values hs hx'
    obtain ⟨y, hy, hfy⟩ := ib.values hs hy'
    refine (LFml.holds_eq_iff _ _ _ _).2 ⟨x, hx, ?_⟩
    rw [hy, Subtype.ext (eq_mono S (uintVal_bounds x').1 hfx hfy rfl)]

/-- **A block body true at the floors is true at the keys.** -/
theorem ApfFml.body_holds (hs : Setting g st' Rs S Gd Lo ks Bs ν μ' μ) :
    ∀ (pol : Bool) {φ : LFml C} (h : ApfFml Rs φ), h.BodyOk Gd Lo ks Bs pol →
      (pol = true → φ.holds g μ → φ.holds { g with storage := st' } μ') ∧
      (pol = false → φ.holds { g with storage := st' } μ' → φ.holds g μ)
  | _, _, .tt, _ => ⟨fun _ h => h, fun _ h => h⟩
  | pol, _, @ApfFml.eq _ _ _ a b ha hb, hok => by
    rcases hok with ⟨hr₁, hr₂⟩ | ⟨rfl, hg⟩
    · have e : (LFml.eq a b).holds { g with storage := st' } μ' ↔ (LFml.eq a b).holds g μ := by
        rw [LFml.holds_eq_iff, LFml.holds_eq_iff, hs.eval ha hr₁, hs.eval hb hr₂]
      exact ⟨fun _ h => e.2 h, fun _ h => e.1 h⟩
    · exact ⟨nofun, fun _ => hg.holds hs⟩
  | pol, _, .not h, hok => by
    have ih := ApfFml.body_holds hs (!pol) h hok
    cases pol
    · exact ⟨nofun, fun _ hn h' => hn (ih.1 rfl h')⟩
    · exact ⟨fun _ hn h' => hn (ih.2 rfl h'), nofun⟩
  | pol, _, .and h₁ h₂, hok => by
    have ih₁ := ApfFml.body_holds hs pol h₁ hok.1
    have ih₂ := ApfFml.body_holds hs pol h₂ hok.2
    exact ⟨fun hp h => ⟨ih₁.1 hp h.1, ih₂.1 hp h.2⟩, fun hp h => ⟨ih₁.2 hp h.1, ih₂.2 hp h.2⟩⟩
  | pol, _, .imp h₁ h₂, hok => by
    have ih₁ := ApfFml.body_holds hs (!pol) h₁ hok.1
    have ih₂ := ApfFml.body_holds hs pol h₂ hok.2
    cases pol
    · exact ⟨nofun, fun _ h h' => ih₂.2 rfl (h (ih₁.1 rfl h'))⟩
    · exact ⟨fun _ h h' => ih₂.1 rfl (h (ih₁.2 rfl h')), nofun⟩
  | _, _, .all .., hok => hok.elim

/-- The setting with one more block variable, set at the key and at its floor. -/
theorem Setting.push (hs : Setting g st' Rs S Gd Lo ks Bs ν μ' μ) (k : Nat) (i : PrimTy.uint.Denote)
    (hB : (⟨.uint, k⟩ : Parameter) ∈ Bs) :
    Setting g st' Rs S Gd Lo (ks ++ [k]) Bs ν (μ'.set .uint k i) (μ.set .uint k (lastU S i)) where
  surg := hs.surg
  gdS := hs.gdS
  loS := hs.loS
  loT := hs.loT
  hμ q hq := by
    have hne : q ≠ ⟨.uint, k⟩ := fun e => hq (by
      rw [e]; exact List.mem_map.2 ⟨k, List.mem_append_right _ List.mem_cons_self, rfl⟩)
    exact (Parameter.read_set_ne q _ hne μ' i).trans ((hs.hμ q fun h => hq (by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
      exact List.mem_map.2 ⟨j, List.mem_append_left _ hj, rfl⟩)).trans
        (Parameter.read_set_ne q _ hne μ (lastU S i)).symm)
  hk j hj := by
    by_cases he : j = k
    · subst he; rw [AEnv.get_set_self, AEnv.get_set_self]
    · rw [AEnv.get_set_ne μ .uint .uint _ he, AEnv.get_set_ne μ' .uint .uint _ he]
      exact hs.hk j ((List.mem_append.1 hj).resolve_right fun h => he (List.mem_singleton.1 h))
  hν q hq := by
    have hne : q ≠ ⟨.uint, k⟩ := fun e => hq (e ▸ hB)
    exact (Parameter.read_set_ne q _ hne μ (lastU S i)).trans (hs.hν q hq)

/-- **The block holds where its instances hold** (Bradley, Manna, Sipma):
at the keys `μ'` read in the rebuilt storage, by the instance at their
floors, which the index set `us` names. -/
theorem LFml.block_refute (us : List (LTm C (.val .uint)))
    (hus : ∀ u ∈ us, ∀ q ∈ u.parameters, q ∉ Bs)
    (hcover : ∀ s ∈ S, ∃ u ∈ us, ∃ v : PrimTy.uint.Denote, (u.eval g ν : Option _) = some v ∧ v.1 = s)
    (h0 : (0 : Int) ∈ S) :
    ∀ (φ : LFml C) (done : List Nat) (μ' μ : AEnv), φ.chainQF = true →
      Setting g st' Rs S Gd Lo done Bs ν μ' μ →
      (∀ k ∈ φ.chainVars, (⟨.uint, k⟩ : Parameter) ∈ Bs) →
      ∀ hb : ApfFml Rs φ.chainBody, hb.BodyOk Gd Lo (done ++ φ.chainVars) Bs true →
      (φ.inst us).holds g μ → φ.holds { g with storage := st' } μ'
  | .all k .uint φ, done, μ', μ, hc, hs, hB, hb, hok, hi => by
    intro i
    have hkB : (⟨.uint, k⟩ : Parameter) ∈ Bs := hB k List.mem_cons_self
    have hfS : (lastU S i).1 ∈ S := by
      rcases lastIn_mem S i.1 with h | h
      · show lastIn S i.1 ∈ S
        rw [h]; exact h0
      · exact h
    obtain ⟨u, hu, v, hv, hvs⟩ := hcover _ hfS
    have hv' : v = lastU S i := Subtype.ext hvs
    subst hv'
    have huμ : (u.eval g μ : Option PrimTy.uint.Denote) = some (lastU S i) := by
      rw [← hv]; exact u.eval_agree_parameters g fun q hq => hs.hν q (hus u hu q hq)
    have hconj := (LFml.holds_conj g μ _).1 hi _ (List.mem_map.2 ⟨u, hu, rfl⟩)
    have hsub := hconj ((LFml.holds_eq_iff g μ u u).2 ⟨_, huμ, huμ⟩)
    rw [LFml.holds_subst1 g μ k u huμ _ (LFml.qfB_inst us φ hc)] at hsub
    exact LFml.block_refute us hus hcover h0 φ (done ++ [k]) _ _ hc (hs.push k i hkB)
      (fun j hj => hB j (List.mem_cons_of_mem _ hj)) hb
      (by rw [List.append_assoc, List.singleton_append]; exact hok) hsub
  | .all _ .bool _, _, _, _, hc, _, _, _, _, _ | .all _ .int _, _, _, _, hc, _, _, _, _, _ => by
    simp only [LFml.chainQF, LFml.qfB, Bool.false_eq_true] at hc
  | .tt, done, μ', μ, _, hs, _, hb, hok, hi | .eq _ _, done, μ', μ, _, hs, _, hb, hok, hi
  | .not _, done, μ', μ, _, hs, _, hb, hok, hi | .and _ _, done, μ', μ, _, hs, _, hb, hok, hi
  | .imp _ _, done, μ', μ, _, hs, _, hb, hok, hi =>
    (ApfFml.body_holds hs true hb (by simpa only [LFml.chainVars, List.append_nil] using hok)).1 rfl hi

/-- **The conditions the refutation needs**, outside the blocks: terms
read alike; at a negative block, its variables among `Bs` and its body
of the fragment; at any other quantifier, a formula read alike. -/
def ApfFml.TopOk (Gd Lo : LTm C (.val .uint) → Prop) (Bs : List Parameter) :
    Bool → {φ : LFml C} → ApfFml Rs φ → Prop
  | _, _, .tt => True
  | _, _, .eq ha hb => ha.Rel [] Bs Gd ∧ hb.Rel [] Bs Gd
  | pol, _, .not h => h.TopOk Gd Lo Bs (!pol)
  | pol, _, .and h₁ h₂ => h₁.TopOk Gd Lo Bs pol ∧ h₂.TopOk Gd Lo Bs pol
  | pol, _, .imp h₁ h₂ => h₁.TopOk Gd Lo Bs (!pol) ∧ h₂.TopOk Gd Lo Bs pol
  | pol, _, @ApfFml.all _ _ k p φ h =>
    if (!pol && (LFml.all k p φ).isBlock Rs) = true then
      (∀ j ∈ (LFml.all k p φ).chainVars, (⟨.uint, j⟩ : Parameter) ∈ Bs) ∧
        ∃ hb : ApfFml Rs (LFml.all k p φ).chainBody, hb.BodyOk Gd Lo (LFml.all k p φ).chainVars Bs true
    else (⟨p, k⟩ : Parameter) ∈ Bs ∧ h.Frame Bs Gd

/-- **Instantiation is exact**: where the instantiated formula fails at
`ν`, the formula fails at `ν` in the rebuilt storage. -/
theorem ApfFml.apfInst_refute (us : List (LTm C (.val .uint)))
    (hus : ∀ u ∈ us, ∀ q ∈ u.parameters, q ∉ Bs)
    (hcover : ∀ s ∈ S, ∃ u ∈ us, ∃ v : PrimTy.uint.Denote, (u.eval g ν : Option _) = some v ∧ v.1 = s)
    (h0 : (0 : Int) ∈ S) (hs : Setting g st' Rs S Gd Lo [] Bs ν ν ν) :
    ∀ (pol : Bool) {φ : LFml C} (h : ApfFml Rs φ), h.TopOk Gd Lo Bs pol →
      (pol = true → φ.holds { g with storage := st' } ν → (φ.apfInst Rs us pol).holds g ν) ∧
      (pol = false → (φ.apfInst Rs us pol).holds g ν → φ.holds { g with storage := st' } ν)
  | _, _, .tt, _ => ⟨fun _ h => h, fun _ h => h⟩
  | _, _, @ApfFml.eq _ _ _ a b ha hb, hok => by
    have e : (LFml.eq a b).holds { g with storage := st' } ν ↔ (LFml.eq a b).holds g ν := by
      rw [LFml.holds_eq_iff, LFml.holds_eq_iff, hs.eval ha hok.1, hs.eval hb hok.2]
    exact ⟨fun _ h => e.1 h, fun _ h => e.2 h⟩
  | pol, _, .not h, hok => by
    have ih := ApfFml.apfInst_refute us hus hcover h0 hs (!pol) h hok
    cases pol
    · exact ⟨nofun, fun _ hn h' => hn (ih.1 rfl h')⟩
    · exact ⟨fun _ hn h' => hn (ih.2 rfl h'), nofun⟩
  | pol, _, .and h₁ h₂, hok => by
    have ih₁ := ApfFml.apfInst_refute us hus hcover h0 hs pol h₁ hok.1
    have ih₂ := ApfFml.apfInst_refute us hus hcover h0 hs pol h₂ hok.2
    exact ⟨fun hp h => ⟨ih₁.1 hp h.1, ih₂.1 hp h.2⟩, fun hp h => ⟨ih₁.2 hp h.1, ih₂.2 hp h.2⟩⟩
  | pol, _, .imp h₁ h₂, hok => by
    have ih₁ := ApfFml.apfInst_refute us hus hcover h0 hs (!pol) h₁ hok.1
    have ih₂ := ApfFml.apfInst_refute us hus hcover h0 hs pol h₂ hok.2
    cases pol
    · exact ⟨nofun, fun _ h h' => ih₂.2 rfl (h (ih₁.1 rfl h'))⟩
    · exact ⟨fun _ h h' => ih₂.1 rfl (h (ih₁.2 rfl h')), nofun⟩
  | pol, _, @ApfFml.all _ _ k p φ h, hok => by
    unfold ApfFml.TopOk at hok
    by_cases hb : (!pol && (LFml.all k p φ).isBlock Rs) = true
    · rw [if_pos hb] at hok
      have hpol : pol = false := by cases pol <;> simp_all only [Bool.not_true, Bool.false_and,
        Bool.false_eq_true]
      subst hpol
      obtain ⟨hB, hbd, hok⟩ := hok
      have hc : (LFml.all k p φ).chainQF = true := by
        simp only [LFml.isBlock, Bool.not_false, Bool.true_and, Bool.and_eq_true] at hb
        exact hb.1.1
      refine ⟨nofun, fun _ hi => ?_⟩
      have hi' : ((LFml.all k p φ).inst us).holds g ν := by
        simpa only [LFml.apfInst, hb, if_true] using hi
      exact LFml.block_refute us hus hcover h0 _ [] ν ν hc hs hB hbd
        (by simpa only [List.nil_append] using hok) hi'
    · rw [if_neg hb] at hok
      have e := ApfFml.frame_holds (.all k p h) hs hok
      have hx : (LFml.all k p φ).apfInst Rs us pol = .all k p φ := by
        simp only [LFml.apfInst, hb]
        rfl
      rw [hx]
      exact ⟨fun _ h => e.1 h, fun _ h => e.2 h⟩

end Refute

/-! ## The checks, computed -/

/-- An index term with its read query. -/
abbrev IdxKey (C : Contract) := (u : LTm C (.val .uint)) × ReadExpr u

namespace ApfTm

variable {Rs : List Name}

/-- `ApfTm.Rel`, computed: its ground keys are `gkeys`. -/
def relB (ks : List Nat) (Bs : List Parameter) : {b : Bool} → {s : Srt} → {t : LTm C s} → ApfTm Rs b t → Bool
  | _, _, _, @ApfTm.var _ _ p k => decide ((⟨p, k⟩ : Parameter) ∉ ksP ks)
  | _, _, _, .lit _ | _, _, _, .env _ | _, _, _, .root .. | _, _, _, .rroot .. | _, _, _, .err => true
  | _, _, _, .field _ hq | _, _, _, .rfield _ hq => hq.relB ks Bs
  | _, _, _, .index hq hi => hq.relB ks Bs && hi.relB ks Bs
  | _, _, _, .rkeyU (i := i) hq hi =>
    hq.relB ks Bs && (if hq.pre then i.isBVar ks || (i.parameters.all (fun q => decide (q ∉ Bs)) && hi.relB ks Bs)
      else hi.relB ks Bs)
  | _, _, _, .rkey (K := K) hq hi => hq.relB ks Bs && hi.relB ks Bs && (!hq.pre || K != .uint)
  | _, _, _, .word hq | _, _, _, .rword hq => hq.relB ks Bs
  | _, _, _, .unop _ _ ht => ht.relB ks Bs
  | _, _, _, .binop _ _ ha hb => ha.relB ks Bs && hb.relB ks Bs
  | _, _, _, .seq hd ha => hd.relB ks Bs && ha.relB ks Bs
  | _, _, _, .orElse ha hb => ha.relB ks Bs && hb.relB ks Bs
  | _, _, _, .kite ha hb ht he => ha.relB ks Bs && hb.relB ks Bs && ht.relB ks Bs && he.relB ks Bs

/-- The ground `uint` keys along the mappings of the roots of `Rs` (`pre`). -/
def gkeys (ks : List Nat) : {b : Bool} → {s : Srt} → {t : LTm C s} → ApfTm Rs b t → List (IdxKey C)
  | _, _, _, .var _ | _, _, _, .lit _ | _, _, _, .env _ | _, _, _, .root .. | _, _, _, .rroot ..
  | _, _, _, .err => []
  | _, _, _, .field _ hq | _, _, _, .rfield _ hq | _, _, _, .word hq | _, _, _, .rword hq
  | _, _, _, .unop _ _ hq => hq.gkeys ks
  | _, _, _, .index hq hi | _, _, _, .rkey hq hi => hq.gkeys ks ++ hi.gkeys ks
  | _, _, _, .rkeyU (i := i) hq hi =>
    hq.gkeys ks ++ (if hq.pre && !i.isBVar ks then ⟨i, hi.toRead⟩ :: hi.gkeys ks else hi.gkeys ks)
  | _, _, _, .binop _ _ ha hb | _, _, _, .seq ha hb | _, _, _, .orElse ha hb => ha.gkeys ks ++ hb.gkeys ks
  | _, _, _, .kite ha hb ht he => ha.gkeys ks ++ hb.gkeys ks ++ ht.gkeys ks ++ he.gkeys ks

theorem relB_sound {ks : List Nat} {Bs : List Parameter} {Gd : LTm C (.val .uint) → Prop} :
    ∀ {b : Bool} {s : Srt} {t : LTm C s} (ht : ApfTm Rs b t), ht.relB ks Bs = true →
      (∀ e ∈ ht.gkeys ks, Gd e.1) → ht.Rel ks Bs Gd
  | _, _, _, .var _, h, _ => by simpa only [relB, decide_eq_true_eq] using h
  | _, _, _, .lit _, _, _ | _, _, _, .env _, _, _ | _, _, _, .root .., _, _ | _, _, _, .rroot .., _, _
  | _, _, _, .err, _, _ => trivial
  | _, _, _, .field _ hq, h, hg | _, _, _, .rfield _ hq, h, hg | _, _, _, .word hq, h, hg
  | _, _, _, .rword hq, h, hg | _, _, _, .unop _ _ hq, h, hg =>
    relB_sound hq h hg
  | _, _, _, .index hq hi, h, hg | _, _, _, .binop _ _ hq hi, h, hg
  | _, _, _, .seq hq hi, h, hg | _, _, _, .orElse hq hi, h, hg => by
    simp only [relB, Bool.and_eq_true] at h
    exact ⟨relB_sound hq h.1 fun e he => hg e (List.mem_append_left _ he),
      relB_sound hi h.2 fun e he => hg e (List.mem_append_right _ he)⟩
  | _, _, _, .rkey (K := K) hq hi, h, hg => by
    simp only [relB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
    exact ⟨relB_sound hq h.1.1 fun e he => hg e (List.mem_append_left _ he),
      relB_sound hi h.1.2 fun e he => hg e (List.mem_append_right _ he),
      fun hp => h.2.resolve_left (by rw [hp]; exact Bool.noConfusion)⟩
  | _, _, _, .kite ha hb ht he, h, hg => by
    simp only [relB, Bool.and_eq_true] at h
    simp only [gkeys, List.append_assoc] at hg
    exact ⟨relB_sound ha h.1.1.1 fun e h' => hg e (List.mem_append_left _ h'),
      relB_sound hb h.1.1.2 fun e h' => hg e (List.mem_append_right _ (List.mem_append_left _ h')),
      relB_sound ht h.1.2 fun e h' => hg e (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _ h'))),
      relB_sound he h.2 fun e h' => hg e (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ h')))⟩
  | _, _, _, .rkeyU (i := x) hq hx, h, hg => by
    unfold gkeys at hg
    simp only [relB, Bool.and_eq_true] at h
    refine ⟨relB_sound hq h.1 fun e he => hg e (List.mem_append_left _ he), ?_⟩
    have hg' := fun e he => hg e (List.mem_append_right _ he)
    have h2 := h.2
    cases hp : hq.pre with
    | false =>
      simp only [hp, Bool.false_and, Bool.false_eq_true, if_false] at h2 hg'
      exact .inr ⟨rfl, relB_sound hx h2 hg'⟩
    | true =>
      refine .inl ⟨rfl, ?_⟩
      by_cases hv : x.isBVar ks = true
      · exact .inl (LTm.isBVar_spec hv)
      · simp only [hp, hv, Bool.not_false, Bool.and_self, if_true] at hg'
        simp only [hp, hv, if_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true,
          decide_eq_true_eq] at h2
        exact .inr ⟨h2.1, hg' _ List.mem_cons_self,
          relB_sound hx h2.2 fun e he => hg' e (List.mem_cons_of_mem _ he)⟩

/-- An operand of a guard comparison, computed. -/
def idxB (ks : List Nat) (Bs : List Parameter) {s : Srt} {a : LTm C s} (ha : ApfTm Rs false a) : Bool :=
  a.isBVar ks || (ha.relB ks Bs && a.parameters.all (fun q => decide (q ∉ Bs)))

/-- An operand's terms in the index set: itself and its keys. -/
def idxGd (ks : List Nat) : (s : Srt) → {a : LTm C s} → ApfTm Rs false a → List (IdxKey C)
  | .val .uint, a, ha => if a.isBVar ks then [] else ⟨a, ha.toRead⟩ :: ha.gkeys ks
  | _, _, _ => []

/-- An operand whose successor is in the index set. -/
def idxLo (ks : List Nat) : (s : Srt) → {a : LTm C s} → ApfTm Rs false a → List (IdxKey C)
  | .val .uint, a, ha => if a.isBVar ks then [] else [⟨a, ha.toRead⟩]
  | _, _, _ => []

theorem idxB_sound {ks : List Nat} {Bs : List Parameter} {Gd Lo : LTm C (.val .uint) → Prop}
    {a : LTm C (.val .uint)} (ha : ApfTm Rs false a) (h : ha.idxB ks Bs = true)
    (hg : ∀ e ∈ idxGd ks _ ha, Gd e.1) (hl : ∀ e ∈ idxLo ks _ ha, Lo e.1) :
    IdxP Gd Lo ks Bs (a.isBVar ks) ha := by
  by_cases hv : a.isBVar ks = true
  · obtain ⟨k, hk, rfl⟩ := LTm.isBVar_spec hv
    rw [hv]
    exact .var k hk ha
  · have hv' : a.isBVar ks = false := by simpa only [Bool.not_eq_true] using hv
    rw [hv']
    simp only [idxB, hv', Bool.false_or, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    simp only [idxGd, idxLo, hv', Bool.false_eq_true, if_false] at hg hl
    exact .gnd ha (relB_sound ha h.1 fun e he => hg e (List.mem_cons_of_mem _ he)) h.2
      (hg _ List.mem_cons_self) (hl _ List.mem_cons_self)

/-- Whether a guard returns wherever its atoms do (`GuardP`'s `tot`). -/
def guardTot (ks : List Nat) : {s : Srt} → {t : LTm C s} → ApfTm Rs false t → Bool
  | _, _, @ApfTm.binop _ _ op _ _ a b ha hb =>
    if op == .and || op == .or then ha.guardTot ks && hb.guardTot ks
    else (a.isBVar ks || a.totalB) && (b.isBVar ks || b.totalB)
  | _, _, _ => true

/-- Whether a guard returns at the floors where it returned at the keys
(`GuardP`'s `ds`). -/
def guardDs (ks : List Nat) : {s : Srt} → {t : LTm C s} → ApfTm Rs false t → Bool
  | _, _, @ApfTm.binop _ _ op _ _ _ _ ha hb =>
    if op == .and then ha.guardDs ks && hb.guardTot ks
    else if op == .or then hb.guardTot ks
    else true
  | _, _, _ => true

/-- A guard, computed. -/
def guardB (ks : List Nat) (Bs : List Parameter) : {s : Srt} → {t : LTm C s} → ApfTm Rs false t → Bool
  | _, _, @ApfTm.binop _ _ op p _ a b ha hb =>
    ((op == .and || op == .or) && p == .bool && ha.guardB ks Bs && hb.guardB ks Bs &&
        (op != .or || ha.guardDs ks)) ||
      (op.isGuardOp && p == .uint && ha.idxB ks Bs && hb.idxB ks Bs &&
        (!op.isStrict || !(a.isBVar ks && b.isBVar ks)))
  | _, _, .var _ | _, _, .lit _ | _, _, .env _ | _, _, .root .. | _, _, .field .. | _, _, .index ..
  | _, _, .word _ | _, _, .rword .. | _, _, .unop .. | _, _, .seq .. | _, _, .orElse ..
  | _, _, .kite .. | _, _, .err => false

/-- A guard's terms in the index set. -/
def guardGd (ks : List Nat) : {s : Srt} → {t : LTm C s} → ApfTm Rs false t → List (IdxKey C)
  | _, _, @ApfTm.binop _ _ op p _ _ _ ha hb =>
    (if op == .and || op == .or then ha.guardGd ks ++ hb.guardGd ks else []) ++
      (idxGd ks (.val p) ha ++ idxGd ks (.val p) hb)
  | _, _, .var _ | _, _, .lit _ | _, _, .env _ | _, _, .root .. | _, _, .field .. | _, _, .index ..
  | _, _, .word _ | _, _, .rword .. | _, _, .unop .. | _, _, .seq .. | _, _, .orElse ..
  | _, _, .kite .. | _, _, .err => []

/-- A guard's terms whose successors are in the index set. -/
def guardLo (ks : List Nat) : {s : Srt} → {t : LTm C s} → ApfTm Rs false t → List (IdxKey C)
  | _, _, @ApfTm.binop _ _ op p _ _ _ ha hb =>
    (if op == .and || op == .or then ha.guardLo ks ++ hb.guardLo ks else []) ++
      (idxLo ks (.val p) ha ++ idxLo ks (.val p) hb)
  | _, _, .var _ | _, _, .lit _ | _, _, .env _ | _, _, .root .. | _, _, .field .. | _, _, .index ..
  | _, _, .word _ | _, _, .rword .. | _, _, .unop .. | _, _, .seq .. | _, _, .orElse ..
  | _, _, .kite .. | _, _, .err => []

theorem guardB_sound {ks : List Nat} {Bs : List Parameter} {Gd Lo : LTm C (.val .uint) → Prop} :
    ∀ {p : PrimTy} {t : LTm C (.val p)} (ht : ApfTm Rs false t), ht.guardB ks Bs = true →
      (∀ e ∈ ht.guardGd ks, Gd e.1) → (∀ e ∈ ht.guardLo ks, Lo e.1) →
        GuardP Gd Lo ks Bs (ht.guardTot ks) (ht.guardDs ks) ht
  | _, _, @ApfTm.binop _ _ op p h a b ha hb, hg, hd, hl => by
    have iha : ha.guardB ks Bs = true → (∀ e ∈ ha.guardGd ks, Gd e.1) → (∀ e ∈ ha.guardLo ks, Lo e.1) →
        GuardP Gd Lo ks Bs (ha.guardTot ks) (ha.guardDs ks) ha := guardB_sound ha
    have ihb : hb.guardB ks Bs = true → (∀ e ∈ hb.guardGd ks, Gd e.1) → (∀ e ∈ hb.guardLo ks, Lo e.1) →
        GuardP Gd Lo ks Bs (hb.guardTot ks) (hb.guardDs ks) hb := guardB_sound hb
    simp only [guardGd, guardLo] at hd hl
    simp only [guardB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hg
    rcases hg with ⟨⟨⟨⟨hop, rfl⟩, h1⟩, h2⟩, h3⟩ | ⟨⟨⟨⟨hop, rfl⟩, h1⟩, h2⟩, h4⟩
    · rcases hop with rfl | rfl
      · simp only [show (BinOp.and == BinOp.and || BinOp.and == BinOp.or) = true from rfl, if_true,
          List.mem_append] at hd hl
        exact .and h (iha h1 (fun e he => hd e (.inl (.inl he))) (fun e he => hl e (.inl (.inl he))))
          (ihb h2 (fun e he => hd e (.inl (.inr he))) (fun e he => hl e (.inl (.inr he))))
      · simp only [show (BinOp.or == BinOp.and || BinOp.or == BinOp.or) = true from rfl, if_true,
          List.mem_append] at hd hl
        have htot : ha.guardDs ks = true := by
          simpa only [bne_self_eq_false, Bool.false_or, Bool.false_eq_true, false_or] using h3
        have ha' := iha h1 (fun e he => hd e (.inl (.inl he))) (fun e he => hl e (.inl (.inl he)))
        rw [htot] at ha'
        exact .or h ha' (ihb h2 (fun e he => hd e (.inl (.inr he))) (fun e he => hl e (.inl (.inr he))))
    · have hc : (op == .and || op == .or) = false := by
        cases op <;> simp only [BinOp.isGuardOp, Bool.false_eq_true] at hop <;> rfl
      simp only [hc, Bool.false_eq_true, if_false, List.nil_append, List.mem_append] at hd hl
      have hT : (ApfTm.binop op h ha hb).guardTot ks =
          ((a.isBVar ks || a.totalB) && (b.isBVar ks || b.totalB)) := by
        cases op <;> simp only [BinOp.isGuardOp, Bool.false_eq_true] at hop <;> rfl
      have hD : (ApfTm.binop op h ha hb).guardDs ks = true := by
        cases op <;> simp only [BinOp.isGuardOp, Bool.false_eq_true] at hop <;> rfl
      rw [hT, hD]
      refine .cmp op h hop (idxB_sound ha h1 (fun e he => hd e (.inl he)) (fun e he => hl e (.inl he)))
        (idxB_sound hb h2 (fun e he => hd e (.inr he)) (fun e he => hl e (.inr he))) (fun hs => ?_)
        (fun ht => by simpa only [Bool.and_eq_true] using ht)
      rw [hs] at h4
      simpa only [Bool.not_true, Bool.false_eq_true, false_or, Bool.not_eq_true'] using h4
  | _, _, .var _, hg, _, _ | _, _, .lit _, hg, _, _ | _, _, .env _, hg, _, _ | _, _, .word _, hg, _, _
  | _, _, .rword .., hg, _, _ | _, _, .unop .., hg, _, _ | _, _, .seq .., hg, _, _
  | _, _, .orElse .., hg, _, _ | _, _, .kite .., hg, _, _ | _, _, .err, hg, _, _ => by
    simp only [guardB, Bool.false_eq_true] at hg

end ApfTm

/-- The literal `true`. -/
def LTm.isTrueAt : {s : Srt} → LTm C s → Bool
  | _, .app0 (.lit (p := .bool) v) => v
  | _, _ => false

namespace ApfFml

variable {Rs : List Name}

/-- A guard atom, computed. -/
def eqGuardB (ks : List Nat) (Bs : List Parameter) {p : PrimTy} {a b : LTm C (.val p)}
    (ha : ApfTm Rs false a) (hb : ApfTm Rs false b) : Bool :=
  (b.isTrueAt && ha.guardB ks Bs) || (p == .uint && ha.idxB ks Bs && hb.idxB ks Bs)

theorem eqGuardB_sound {ks : List Nat} {Bs : List Parameter} {Gd Lo : LTm C (.val .uint) → Prop}
    {p : PrimTy} {a b : LTm C (.val p)} (ha : ApfTm Rs false a) (hb : ApfTm Rs false b) (h : eqGuardB ks Bs ha hb = true)
    (hd : ∀ e ∈ ha.guardGd ks ++ ApfTm.idxGd ks _ ha ++ ApfTm.idxGd ks _ hb, Gd e.1)
    (hl : ∀ e ∈ ha.guardLo ks ++ ApfTm.idxLo ks _ ha ++ ApfTm.idxLo ks _ hb, Lo e.1) :
    GAtom Gd Lo ks Bs ha hb := by
  simp only [eqGuardB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨ht, hg⟩ | ⟨⟨⟨rfl, h1⟩, h2⟩⟩
  · have hG := ApfTm.guardB_sound ha hg (fun e he => hd e (List.mem_append_left _ (List.mem_append_left _ he)))
      (fun e he => hl e (List.mem_append_left _ (List.mem_append_left _ he)))
    cases b with
    | app0 o =>
      cases o with
      | lit v =>
        cases p with
        | bool =>
          have hv : v = true := ht
          subst hv
          exact .tt hG
        | _ => simp only [LTm.isTrueAt, Bool.false_eq_true] at ht
      | _ => simp only [LTm.isTrueAt, Bool.false_eq_true] at ht
    | _ => simp only [LTm.isTrueAt, Bool.false_eq_true] at ht
  · exact .idx (ApfTm.idxB_sound ha h1 (fun e he => hd e (List.mem_append_left _ (List.mem_append_right _ he)))
        (fun e he => hl e (List.mem_append_left _ (List.mem_append_right _ he))))
      (ApfTm.idxB_sound hb h2 (fun e he => hd e (List.mem_append_right _ he))
        (fun e he => hl e (List.mem_append_right _ he)))

/-- `ApfFml.BodyOk`, computed. -/
def bodyB (ks : List Nat) (Bs : List Parameter) : Bool → {φ : LFml C} → ApfFml Rs φ → Bool
  | _, _, .tt => true
  | pol, _, .eq ha hb => (ha.relB ks Bs && hb.relB ks Bs) || (!pol && eqGuardB ks Bs ha hb)
  | pol, _, .not h => h.bodyB ks Bs (!pol)
  | pol, _, .and h₁ h₂ => h₁.bodyB ks Bs pol && h₂.bodyB ks Bs pol
  | pol, _, .imp h₁ h₂ => h₁.bodyB ks Bs (!pol) && h₂.bodyB ks Bs pol
  | _, _, .all .. => false

/-- A body's terms in the index set. -/
def bodyGd (ks : List Nat) (Bs : List Parameter) : {φ : LFml C} → ApfFml Rs φ → List (IdxKey C)
  | _, .tt | _, .all .. => []
  | _, .eq ha hb =>
    if (ha.relB ks Bs && hb.relB ks Bs) = true then ha.gkeys ks ++ hb.gkeys ks
    else ha.guardGd ks ++ ApfTm.idxGd ks _ ha ++ ApfTm.idxGd ks _ hb
  | _, .not h => h.bodyGd ks Bs
  | _, .and h₁ h₂ | _, .imp h₁ h₂ => h₁.bodyGd ks Bs ++ h₂.bodyGd ks Bs

/-- A body's terms whose successors are in the index set. -/
def bodyLo (ks : List Nat) (Bs : List Parameter) : {φ : LFml C} → ApfFml Rs φ → List (IdxKey C)
  | _, .tt | _, .all .. => []
  | _, .eq ha hb =>
    if (ha.relB ks Bs && hb.relB ks Bs) = true then []
    else ha.guardLo ks ++ ApfTm.idxLo ks _ ha ++ ApfTm.idxLo ks _ hb
  | _, .not h => h.bodyLo ks Bs
  | _, .and h₁ h₂ | _, .imp h₁ h₂ => h₁.bodyLo ks Bs ++ h₂.bodyLo ks Bs

theorem bodyB_sound {ks : List Nat} {Bs : List Parameter} {Gd Lo : LTm C (.val .uint) → Prop} :
    ∀ (pol : Bool) {φ : LFml C} (h : ApfFml Rs φ), h.bodyB ks Bs pol = true →
      (∀ e ∈ h.bodyGd ks Bs, Gd e.1) → (∀ e ∈ h.bodyLo ks Bs, Lo e.1) → h.BodyOk Gd Lo ks Bs pol
  | _, _, .tt, _, _, _ => trivial
  | pol, _, .eq ha hb, hb', hd, hl => by
    unfold bodyGd at hd
    unfold bodyLo at hl
    by_cases hr : (ha.relB ks Bs && hb.relB ks Bs) = true
    · rw [if_pos hr] at hd
      simp only [Bool.and_eq_true] at hr
      exact .inl ⟨ApfTm.relB_sound ha hr.1 fun e he => hd e (List.mem_append_left _ he),
        ApfTm.relB_sound hb hr.2 fun e he => hd e (List.mem_append_right _ he)⟩
    · rw [if_neg hr] at hd hl
      simp only [bodyB, hr, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at hb'
      exact .inr ⟨hb'.1, eqGuardB_sound ha hb hb'.2 hd hl⟩
  | pol, _, .not h, hb', hd, hl => bodyB_sound (!pol) h hb' hd hl
  | pol, _, .and h₁ h₂, hb', hd, hl => by
    simp only [bodyB, Bool.and_eq_true] at hb'
    exact ⟨bodyB_sound pol h₁ hb'.1 (fun e he => hd e (List.mem_append_left _ he))
        (fun e he => hl e (List.mem_append_left _ he)),
      bodyB_sound pol h₂ hb'.2 (fun e he => hd e (List.mem_append_right _ he))
        (fun e he => hl e (List.mem_append_right _ he))⟩
  | pol, _, .imp h₁ h₂, hb', hd, hl => by
    simp only [bodyB, Bool.and_eq_true] at hb'
    exact ⟨bodyB_sound (!pol) h₁ hb'.1 (fun e he => hd e (List.mem_append_left _ he))
        (fun e he => hl e (List.mem_append_left _ he)),
      bodyB_sound pol h₂ hb'.2 (fun e he => hd e (List.mem_append_right _ he))
        (fun e he => hl e (List.mem_append_right _ he))⟩
  | _, _, .all .., hb', _, _ => by simp only [bodyB, Bool.false_eq_true] at hb'

/-- `ApfFml.Frame`, computed. -/
def frameB (Bs : List Parameter) : {φ : LFml C} → ApfFml Rs φ → Bool
  | _, .tt => true
  | _, .eq ha hb => ha.relB [] Bs && hb.relB [] Bs
  | _, .not h => h.frameB Bs
  | _, .and h₁ h₂ | _, .imp h₁ h₂ => h₁.frameB Bs && h₂.frameB Bs
  | _, .all k p h => decide ((⟨p, k⟩ : Parameter) ∈ Bs) && h.frameB Bs

/-- Its ground keys. -/
def frameGd : {φ : LFml C} → ApfFml Rs φ → List (IdxKey C)
  | _, .tt => []
  | _, .eq ha hb => ha.gkeys [] ++ hb.gkeys []
  | _, .not h | _, .all _ _ h => h.frameGd
  | _, .and h₁ h₂ | _, .imp h₁ h₂ => h₁.frameGd ++ h₂.frameGd

theorem frameB_sound {Bs : List Parameter} {Gd : LTm C (.val .uint) → Prop} :
    ∀ {φ : LFml C} (h : ApfFml Rs φ), h.frameB Bs = true → (∀ e ∈ h.frameGd, Gd e.1) → h.Frame Bs Gd
  | _, .tt, _, _ => trivial
  | _, .eq ha hb, hf, hd => by
    simp only [frameB, Bool.and_eq_true] at hf
    exact ⟨ApfTm.relB_sound ha hf.1 fun e he => hd e (List.mem_append_left _ he),
      ApfTm.relB_sound hb hf.2 fun e he => hd e (List.mem_append_right _ he)⟩
  | _, .not h, hf, hd => frameB_sound h hf hd
  | _, .and h₁ h₂, hf, hd | _, .imp h₁ h₂, hf, hd => by
    simp only [frameB, Bool.and_eq_true] at hf
    exact ⟨frameB_sound h₁ hf.1 fun e he => hd e (List.mem_append_left _ he),
      frameB_sound h₂ hf.2 fun e he => hd e (List.mem_append_right _ he)⟩
  | _, .all k p h, hf, hd => by
    simp only [frameB, Bool.and_eq_true, decide_eq_true_eq] at hf
    exact ⟨hf.1, frameB_sound h hf.2 hd⟩

/-- The evidence of a block's body, if any. -/
def blockBody? (Rs : List Name) (φ : LFml C) : Option (ApfFml Rs φ.chainBody) := ofFormula? Rs φ.chainBody

/-- `ApfFml.TopOk`, computed. -/
def topB (Bs : List Parameter) : Bool → {φ : LFml C} → ApfFml Rs φ → Bool
  | _, _, .tt => true
  | _, _, .eq ha hb => ha.relB [] Bs && hb.relB [] Bs
  | pol, _, .not h => h.topB Bs (!pol)
  | pol, _, .and h₁ h₂ => h₁.topB Bs pol && h₂.topB Bs pol
  | pol, _, .imp h₁ h₂ => h₁.topB Bs (!pol) && h₂.topB Bs pol
  | pol, _, @ApfFml.all _ _ k p φ h =>
    if (!pol && (LFml.all k p φ).isBlock Rs) = true then
      (LFml.all k p φ).chainVars.all (fun j => decide ((⟨.uint, j⟩ : Parameter) ∈ Bs)) &&
        (match blockBody? Rs (LFml.all k p φ) with
          | some hb => hb.bodyB (LFml.all k p φ).chainVars Bs true
          | none => false)
    else decide ((⟨p, k⟩ : Parameter) ∈ Bs) && h.frameB Bs

/-- The terms the conditions put in the index set. -/
def topGd (Bs : List Parameter) : Bool → {φ : LFml C} → ApfFml Rs φ → List (IdxKey C)
  | _, _, .tt => []
  | _, _, .eq ha hb => ha.gkeys [] ++ hb.gkeys []
  | pol, _, .not h => h.topGd Bs (!pol)
  | pol, _, .and h₁ h₂ => h₁.topGd Bs pol ++ h₂.topGd Bs pol
  | pol, _, .imp h₁ h₂ => h₁.topGd Bs (!pol) ++ h₂.topGd Bs pol
  | pol, _, @ApfFml.all _ _ k p φ h =>
    if (!pol && (LFml.all k p φ).isBlock Rs) = true then
      (match blockBody? Rs (LFml.all k p φ) with
        | some hb => hb.bodyGd (LFml.all k p φ).chainVars Bs
        | none => [])
    else h.frameGd

/-- The terms whose successors the conditions put in the index set. -/
def topLo (Bs : List Parameter) : Bool → {φ : LFml C} → ApfFml Rs φ → List (IdxKey C)
  | _, _, .tt | _, _, .eq _ _ => []
  | pol, _, .not h => h.topLo Bs (!pol)
  | pol, _, .and h₁ h₂ => h₁.topLo Bs pol ++ h₂.topLo Bs pol
  | pol, _, .imp h₁ h₂ => h₁.topLo Bs (!pol) ++ h₂.topLo Bs pol
  | pol, _, @ApfFml.all _ _ k p φ _ =>
    if (!pol && (LFml.all k p φ).isBlock Rs) = true then
      (match blockBody? Rs (LFml.all k p φ) with
        | some hb => hb.bodyLo (LFml.all k p φ).chainVars Bs
        | none => [])
    else []

theorem topB_sound {Bs : List Parameter} {Gd Lo : LTm C (.val .uint) → Prop} :
    ∀ (pol : Bool) {φ : LFml C} (h : ApfFml Rs φ), h.topB Bs pol = true →
      (∀ e ∈ h.topGd Bs pol, Gd e.1) → (∀ e ∈ h.topLo Bs pol, Lo e.1) → h.TopOk Gd Lo Bs pol
  | _, _, .tt, _, _, _ => trivial
  | _, _, .eq ha hb, ht, hd, _ => by
    simp only [topB, Bool.and_eq_true] at ht
    exact ⟨ApfTm.relB_sound ha ht.1 fun e he => hd e (List.mem_append_left _ he),
      ApfTm.relB_sound hb ht.2 fun e he => hd e (List.mem_append_right _ he)⟩
  | pol, _, .not h, ht, hd, hl => topB_sound (!pol) h ht hd hl
  | pol, _, .and h₁ h₂, ht, hd, hl => by
    simp only [topB, Bool.and_eq_true] at ht
    exact ⟨topB_sound pol h₁ ht.1 (fun e he => hd e (List.mem_append_left _ he))
        (fun e he => hl e (List.mem_append_left _ he)),
      topB_sound pol h₂ ht.2 (fun e he => hd e (List.mem_append_right _ he))
        (fun e he => hl e (List.mem_append_right _ he))⟩
  | pol, _, .imp h₁ h₂, ht, hd, hl => by
    simp only [topB, Bool.and_eq_true] at ht
    exact ⟨topB_sound (!pol) h₁ ht.1 (fun e he => hd e (List.mem_append_left _ he))
        (fun e he => hl e (List.mem_append_left _ he)),
      topB_sound pol h₂ ht.2 (fun e he => hd e (List.mem_append_right _ he))
        (fun e he => hl e (List.mem_append_right _ he))⟩
  | pol, _, @ApfFml.all _ _ k p φ h, ht, hd, hl => by
    unfold ApfFml.TopOk
    unfold topB at ht
    unfold topGd at hd
    unfold topLo at hl
    split
    · rename_i hb
      rw [if_pos hb] at ht hd hl
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ht
      refine ⟨ht.1, ?_⟩
      cases hbb : blockBody? Rs (LFml.all k p φ) with
      | none => simp only [hbb, Bool.false_eq_true, and_false] at ht
      | some hb' =>
        simp only [hbb] at ht hd hl
        exact ⟨hb', bodyB_sound true hb' ht.2 hd hl⟩
    · rename_i hb
      rw [if_neg hb] at ht hd
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
      exact ⟨ht.1, frameB_sound h ht.2 hd⟩

end ApfFml

/-! ## The preparation -/

/-- `x + 1`, checked. -/
def LTm.succU (x : LTm C (.val .uint)) : LTm C (.val .uint) :=
  .app2 (.binop .add rfl) x (.app0 (.lit (uintOfNat 1)))

theorem LTm.eval_succU (g : State C []) (ν : AEnv) (x : LTm C (.val .uint)) {v : PrimTy.uint.Denote}
    (hv : (x.eval g ν : Option _) = some v) (hb : v.1 + 1 < ((2 ^ 256 : Nat) : Int)) :
    ∃ w : PrimTy.uint.Denote, (x.succU.eval g ν : Option _) = some w ∧ w.1 = v.1 + 1 := by
  have h1 : (uintOfNat 1).1 = 1 := uintOfNat_val (by omega)
  have hr : PrimTy.uint.inRange (v.1 + 1) = true := by
    have := uintVal_bounds v
    simp only [PrimTy.inRange, decide_eq_true_eq]
    omega
  refine ⟨⟨v.1 + 1, hr⟩, ?_, rfl⟩
  rw [LTm.succU, LTm.eval_app2, Close.Op2.eval_binop, hv]
  show binopT .add rfl v (some (uintOfNat 1)) = _
  simp only [binopT, BinOp.shortT, Option.bind_some, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, h1,
    PrimTy.ofInt?, dif_pos hr]

/-- The successor's key. -/
def IdxKey.succ (e : IdxKey C) : IdxKey C := ⟨e.1.succU, .binop .add rfl e.2 (.lit _)⟩

/-- `0`. -/
def IdxKey.zero : IdxKey C := ⟨.app0 (.lit (uintOfNat 0)), .lit _⟩

/-- A key's value at `g`, `ν`, by its read query. -/
def IdxKey.value (g : State C []) (ν : AEnv) (e : IdxKey C) : Option PrimTy.uint.Denote :=
  (e.2.query g ν).runStorage g.storage

theorem IdxKey.value_eq (g : State C []) (ν : AEnv) (e : IdxKey C) :
    e.value g ν = (e.1.eval g ν : Option PrimTy.uint.Denote) := by
  have := ReadExpr.query_sound g ν e.2 g.storage
  rw [ReadDen.erase_val, Option.map_id] at this
  exact this

/-- **The index set's values** at `g`, `ν`. -/
def apfValues (us : List (IdxKey C)) (g : State C []) (ν : AEnv) : List Int :=
  us.filterMap fun e => (e.value g ν).map (·.1)

theorem mem_apfValues {us : List (IdxKey C)} {g : State C []} {ν : AEnv} {s : Int} :
    s ∈ apfValues us g ν ↔ ∃ e ∈ us, ∃ v : PrimTy.uint.Denote, (e.1.eval g ν : Option _) = some v ∧ v.1 = s := by
  simp only [apfValues, List.mem_filterMap, Option.map_eq_some_iff, IdxKey.value_eq]

/-- **The index set without repeated terms**: a term written twice is one
instance, not two (`LTm.beqR`, structural). -/
def dedupKeys : List (IdxKey C) → List (IdxKey C)
  | [] => []
  | e :: l => e :: (dedupKeys l).filter fun e' => !(e'.1.beqR e.1)

theorem dedupKeys_mem : ∀ {l : List (IdxKey C)} {e : IdxKey C}, e ∈ l → ∃ e' ∈ dedupKeys l, e'.1 = e.1
  | e₀ :: l, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨e, List.mem_cons_self, rfl⟩
    · obtain ⟨e', he', hee⟩ := dedupKeys_mem h
      by_cases hb : e'.1.beqR e₀.1 = true
      · rw [LTm.beqR_eq_beqM] at hb
        have := LTm.eq_of_beqM _ _ hb
        exact ⟨e₀, List.mem_cons_self, by
          rw [← hee]; exact (eq_of_heq (Sigma.ext_iff.1 this).2).symm⟩
      · exact ⟨e', List.mem_cons_of_mem _ (List.mem_filter.2 ⟨he', by simp only [hb, Bool.not_false]⟩),
          hee⟩

/-- The root a name holds, if any. -/
def MRoot.of? (r : Name) : Option (MRoot C) :=
  match h : C.rootType r with
  | some T => some ⟨r, T, h⟩
  | none => none

/-- **Array property instantiation as a preparation** (`Prep`): the
negative blocks over the roots they read at their variables, instantiated
at the index set; the body itself where there is none, or where the body
is outside the fragment. -/
def apfPrep (B : LFml C) : Prep B :=
  let roots := (B.blockRoots true).eraseDups.filterMap (MRoot.of? (C := C))
  let Rs := roots.map (·.name)
  if hn : Rs.Nodup ∧ Rs ≠ [] then
    match ApfFml.ofFormula? Rs B with
    | none => Prep.id B
    | some h =>
      let us := dedupKeys (IdxKey.zero :: (h.topGd B.binders true ++ (h.topLo B.binders true).map IdxKey.succ))
      if hc : h.topB B.binders true = true ∧
          us.all (fun e => e.1.parameters.all fun q => decide (q ∉ B.binders)) = true then
        { body := B.apfInst Rs (us.map (·.1)) true
          sound := fun hv g ν => (LFml.apfInst_sound g Rs _ B true ν).1 rfl (hv g ν)
          refute := fun g ν hneg =>
            let lo := h.topLo B.binders true
            let S : ApfSet := ⟨apfValues us g ν, apfValues lo g ν⟩
            ⟨{ g with storage := surgeryAll (lastU S) (lastBound S) roots g.storage }, by
              have hS : ∀ s ∈ S.vals, s < ((2 ^ 256 : Nat) : Int) := fun s hs => by
                obtain ⟨_, _, v, _, rfl⟩ := mem_apfValues.1 hs
                exact (uintVal_bounds v).2
              have hsurg : Surg g (surgeryAll (lastU S) (lastBound S) roots g.storage) Rs (lastU S) :=
                ⟨fun r hr => surgeryAll_other _ _ _ r roots hr,
                  fun r hr => surgeryAll_at _ _ _ (lastU_top S hS) r roots hn.1 hr⟩
              have hall := List.all_eq_true.1 hc.2
              have hus : ∀ u ∈ us.map (·.1), ∀ q ∈ u.parameters, q ∉ B.binders := fun u hu q hq => by
                obtain ⟨e, he, rfl⟩ := List.mem_map.1 hu
                have := List.all_eq_true.1 (hall e he) q hq
                simpa only [decide_eq_true_eq] using this
              have hcover : ∀ s ∈ S, ∃ u ∈ us.map (·.1), ∃ v : PrimTy.uint.Denote,
                  (u.eval g ν : Option _) = some v ∧ v.1 = s := fun s hs => by
                obtain ⟨e, he, v, hv, rfl⟩ := mem_apfValues.1 hs
                exact ⟨e.1, List.mem_map.2 ⟨e, he, rfl⟩, v, hv, rfl⟩
              have h0 : (0 : Int) ∈ S := mem_apfValues.2 ⟨IdxKey.zero, List.mem_cons_self, uintOfNat 0, rfl,
                uintOfNat_val (by omega)⟩
              have hset : Setting g (surgeryAll (lastU S) (lastBound S) roots g.storage) Rs S
                  (fun x => x ∈ us.map (·.1)) (fun x => x ∈ lo.map (·.1)) [] B.binders ν ν ν :=
                { surg := hsurg
                  gdS := fun x hx v hv => by
                    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
                    exact mem_apfValues.2 ⟨e, he, v, hv, rfl⟩
                  loS := fun x hx v hv hb => by
                    obtain ⟨w, hw, hw1⟩ := LTm.eval_succU g ν x hv hb
                    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
                    obtain ⟨e', he', hee⟩ := dedupKeys_mem (List.mem_cons_of_mem IdxKey.zero
                      (List.mem_append_right _ (List.mem_map.2 ⟨e, he, rfl⟩)))
                    exact mem_apfValues.2 ⟨e', he', w, by rw [hee]; exact hw, hw1⟩
                  loT := fun x hx v hv => by
                    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
                    exact mem_apfValues.2 ⟨e, he, v, hv, rfl⟩
                  hμ := fun _ _ => rfl
                  hk := fun _ h => nomatch h
                  hν := fun _ _ => rfl }
              have htop := ApfFml.topB_sound (Gd := fun x => x ∈ us.map (·.1))
                (Lo := fun x => x ∈ lo.map (·.1)) true h hc.1
                (fun e he => by
                  obtain ⟨e', he', hee⟩ := dedupKeys_mem (List.mem_cons_of_mem IdxKey.zero
                    (List.mem_append_left _ he))
                  exact List.mem_map.2 ⟨e', he', hee⟩)
                (fun e he => List.mem_map.2 ⟨e, he, rfl⟩)
              exact fun hB => hneg ((ApfFml.apfInst_refute (us.map (·.1)) hus hcover h0 hset true h htop).1
                rfl hB)⟩ }
      else Prep.id B
  else Prep.id B

/-- **The prepared body is valid exactly where the body is**: this is
`Prep.valid_iff`, which every preparation has (`Prep.id` too).  What the
fragment adds is that `apfPrep` instantiates where its checks pass, the
instantiation sound (`LFml.apfInst_sound`) and exact
(`ApfFml.apfInst_refute`, Bradley, Manna, Sipma) there; outside the
fragment the body is kept. -/
theorem apfPrep_valid_iff (B : LFml C) : (apfPrep B).body.Valid ↔ B.Valid := (apfPrep B).valid_iff

/-- info: 'Solidity.Decide.apfPrep_valid_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms apfPrep_valid_iff

/-- info: 'Solidity.Decide.LFml.apfInst_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LFml.apfInst_sound

/-- info: 'Solidity.Decide.ApfFml.apfInst_refute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ApfFml.apfInst_refute

end Solidity.Decide
