import Solidity.Calculus.QuantHoist
import Solidity.Calculus.QueryReduction
import Solidity.Calculus.FloorRegion

/-!
# The array property fragment, instantiated (M7, step 5)

A universal block in a negative position whose body reads mappings at its
variables (`(∀ k. k < 10 → balances[k] == 0) → balances[5] == 0`) is
decided as Bradley, Manna and Sipma decide it: replaced by its instances
at the index set `U`, the goal's ground keys of those mappings and the
guards' ground operands with their successors, and the key type's least
value; the instance is decided by the quantified pipeline.

One pass per key type (`OrdK`: `uint`, `int`; `apfPrepK`), each
instantiating the blocks whose variables are all of its type, read as
keys of that type.

* **Sound** (`apfInst_sound`): the block implies each instance, and it
  stands where the formula is antitone in it.
* **Exact** (`apfInst_refute`): from a state where the instantiated body
  fails, a state where the body fails: each mapping read at a block
  variable is rebuilt (`MRoot.surgery`) so that its key `i` holds what key
  `⌊i⌋` held, `⌊i⌋` the largest value of the index set at most `i`
  (`floorIn`, the type's least value where there is none), or its largest
  value where `i` lies past the second largest and the largest bounds no
  strict guard (`lastIn`, `Calculus/FloorRegion.lean`).  Reads at the
  index set keep their values, so everything outside the blocks reads as
  before (`ApfTm.eval_rel`); a guard true at `i` is true at `⌊i⌋`
  (`GuardP.mono`: guards compare a variable with a ground term, or two
  variables by `≤`, `≥`, `==`, never `<`), so each block holds by its
  instance at `⌊i⌋`.  A ground operand may halt (`k < x - 1`): a guard
  true at the keys returned there, so its comparisons return at the
  floors; but a `||` whose left operand was false at the keys reads that
  operand at the floors too, where a `&&` inside it may evaluate a halting
  right operand it skipped at the keys.  So such a right operand must be
  total (`GuardP`'s `ds`, `GuardP.floors`, `GuardP.defined`).
* **The ledger** (feature 21): a `uint` block may read the starting
  ledger at its variables (`net(a)`, `ARoots.net`); the ledger is rebuilt
  as the mappings are (`netRebuild`), each address holding what its floor
  held, and the index set takes the largest address too (`IdxKey.top`), so
  the addresses past the goal's read the solver's free entry there.

The fragment (`apfPrepK`): roots of any type, read along their own paths
(`ApfTm.rroot`, `rkey`, `rfield`, `rword`).  Along a root's mappings every
key of the pass's type is floored (`FloorShape.of`: `floor` at a
`mapping(K => V)`, `outer` at a mapping keyed by another type, `keep` past
the mappings): read there at a block variable or at a ground term of the
index set mentioning no binder (`m[k]`, `m[o][k]`, `m[i][3]`, `m[3][k]`
beside `m[k][3]`, `accs[k].v`); a key of another type (`owed[a][k]`), and
every key past a member, any term of the fragment with no block variable
(`ApfTm.Rel`).  The rebuilt root holds at each floored key what the key's
floor held, the whole value under it copied (`FloorShape.rebuild`), so a
read reads at its keys' floors (`FloorShape.rebuild_word`,
`SRef.floorRef`).  Block variables compared in guards (atoms in negative
positions of the block body); every other read of such a root outside
the fragment.  Nested mappings `m[i][j]` with two bound indices on one
path are outside (a decision recorded in `docs/automation.md`, M7).

Dynamic arrays of primitives (feature 32): at a `uint` pass a block may
read a root's array at its variables (`ApfTm.rat`, the slot test `rhas`,
the length `rlen`, the Theory's conditional read `ite`).  The rebuilt
array (`FloorShape.arr`) keeps its live length and holds at slot `i` what
slot `⌊i⌋` held, there exactly where `⌊i⌋` is below the old slots
(`arr_rebuild_slot`); so the floor must be monotone and never above its
key (`ArrOK`), and a pass that rebuilds an array turns `lastIn`'s
largest-value region off (every value among the strict operands,
`lastIn_eq_floorIn`).  The index set may take further terms (`extra`,
`apfPrepWith`: an array's length read as an atom,
`Calculus/ArrayBlock.lean`), and its values are computed by `LTm.evalC`.

A rebuilt mapping is listed region by region (`regionList`), each region
a symbolic run of keys between two breakpoints of the floor, skipped where
it holds the default (what the largest key's floor held): its reads are
proved by region reasoning (`lookupBy_regionList`), never evaluated, so
the refutation of an `int`-keyed block whose two outer regions hold
different words is a term of `2^255` entries that only an evaluation
would build.  No construction is polynomial in the index set in general:
a mapping lists its entries one key at a time with a single default, and
a sorted mapping (`∀ i j. i <= j → m[i] <= m[j]`) read at three far keys
`a < b < c` with increasing words has, in every state that refutes such a
leaf, the keys between `a` and `b` listed or those past `c`.
-/

namespace Solidity.Decide

open Semantics ReadRealization

variable {C : Contract} {K : PrimTy}

/-! ## The mappings rebuilt -/

/-- **How a root the blocks read is rebuilt**: along its mappings each key
of type `K` floored (`floor`), any other key kept (`outer`); a dynamic
array of primitives at a `uint` pass floored slot by slot (`arr`); past
them (a struct, any other array, a word) the value copied whole
(`keep`). -/
inductive FloorShape (K : PrimTy) : Ty → Type where
  | keep (T : Ty) : FloorShape K T
  | floor {V : Ty} (s : FloorShape K V) : FloorShape K (.ref (.mapping K V))
  | outer (K' : PrimTy) {V : Ty} (s : FloorShape K V) : FloorShape K (.ref (.mapping K' V))
  /-- A dynamic array of primitives at a `uint` pass: each slot floored,
  the live length kept (feature 32). -/
  | arr {e : PrimTy} (hK : K = .uint) : FloorShape K (.ref (.array (.prim e)))

/-- `floor` at a key type `K'` that is `K`. -/
def FloorShape.floorEq {K' : PrimTy} {V : Ty} (h : K' = K) (s : FloorShape K V) :
    FloorShape K (.ref (.mapping K' V)) :=
  match h with
  | rfl => .floor s

/-- **The shape of a type**: every key of type `K` along its mappings
floored, and at a `uint` pass the slots of a dynamic array of primitives. -/
def FloorShape.of (K : PrimTy) : (T : Ty) → FloorShape K T
  | .ref (.mapping K' V) =>
    if h : K' = K then FloorShape.floorEq h (FloorShape.of K V) else .outer K' (FloorShape.of K V)
  | .ref (.array (.prim _)) => if h : K = .uint then .arr h else .keep _
  | T => .keep T

/-- The shape floors an array's slots here. -/
def FloorShape.isArr {T : Ty} : FloorShape K T → Bool
  | .arr _ => true
  | _ => false

/-- The shape floors an array's slots somewhere. -/
def FloorShape.hasArr {T : Ty} : FloorShape K T → Bool
  | .arr _ => true
  | .floor s | .outer _ s => s.hasArr
  | .keep _ => false

/-- A floor at the pass's key type, read at `uint`. -/
def FloorShape.fU (hK : K = .uint) (f : K.Denote → K.Denote) : PrimTy.uint.Denote → PrimTy.uint.Denote :=
  hK ▸ f

/-- **A floor an array can be rebuilt at** (feature 32): monotone, and
never above its key, so the slots below the live length stay there. -/
def ArrOK (ok : OrdK K) (f : K.Denote → K.Denote) : Prop :=
  (∀ x y : K.Denote, ok.val x ≤ ok.val y → ok.val (f x) ≤ ok.val (f y)) ∧ ∀ x : K.Denote, ok.val (f x) ≤ ok.val x

/-- The least value of `B` where `P` holds, `hi` where none does. -/
def cutIn (hi : Int) (B : List Int) (P : Int → Bool) : Int := B.foldl (fun a b => if P b = true ∧ b < a then b else a) hi

theorem cutIn_spec (B : List Int) (P : Int → Bool) : ∀ a : Int,
    B.foldl (fun a b => if P b = true ∧ b < a then b else a) a ≤ a ∧
      (∀ b ∈ B, P b = true → B.foldl (fun a b => if P b = true ∧ b < a then b else a) a ≤ b) ∧
      (B.foldl (fun a b => if P b = true ∧ b < a then b else a) a = a ∨
        (B.foldl (fun a b => if P b = true ∧ b < a then b else a) a ∈ B ∧
          P (B.foldl (fun a b => if P b = true ∧ b < a then b else a) a) = true)) := by
  induction B with
  | nil => intro a; exact ⟨Int.le_refl _, (fun _ h _ => nomatch h), .inl rfl⟩
  | cons s B ih =>
    intro a
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := ih (if P s = true ∧ s < a then s else a)
    by_cases hc : P s = true ∧ s < a
    · rw [if_pos hc] at h1 h2 h3 ⊢
      refine ⟨by omega, fun b hb hP => ?_, ?_⟩
      · rcases List.mem_cons.1 hb with rfl | hb
        · exact h1
        · exact h2 b hb hP
      · rcases h3 with h | ⟨h, hp⟩
        · exact .inr ⟨by rw [h]; exact List.mem_cons_self, by rw [h]; exact hc.1⟩
        · exact .inr ⟨List.mem_cons_of_mem _ h, hp⟩
    · rw [if_neg hc] at h1 h2 h3 ⊢
      refine ⟨h1, fun b hb hP => ?_, ?_⟩
      · rcases List.mem_cons.1 hb with rfl | hb
        · have : ¬ b < a := fun hl => hc ⟨hP, hl⟩
          omega
        · exact h2 b hb hP
      · rcases h3 with h | ⟨h, hp⟩
        · exact .inl h
        · exact .inr ⟨List.mem_cons_of_mem _ h, hp⟩

theorem FloorShape.of_self (K : PrimTy) (V : Ty) :
    FloorShape.of K (.ref (.mapping K V)) = .floor (FloorShape.of K V) := by
  simp only [FloorShape.of]
  rfl

theorem FloorShape.of_mapping_ne {K' : PrimTy} {V : Ty} (h : K' ≠ K) :
    FloorShape.of K (.ref (.mapping K' V)) = .outer K' (FloorShape.of K V) := by
  simp only [FloorShape.of, dif_neg h]

/-- A root the blocks read. -/
structure MRoot (C : Contract) where
  name : Name
  ty : Ty
  h : C.rootType name = some ty

/-- A mapping's value at a key: its entry, or its default. -/
def entryAt {K : PrimTy} {V : Ty} (m : SMap K V) (d : SVal V) (k : K.Denote) : SVal V :=
  (lookupBy k m.toList).getD d

theorem findM_key_entryAt {K : PrimTy} {V U : Ty} (m : SMap K V) (d : SVal V) (k : K.Denote) (p : Path V U) :
    (SVal.map m d).findM (.key k p) = (entryAt m d k).findM p := by
  unfold entryAt
  simp only [SVal.findM]
  cases lookupBy k m.toList <;> rfl

/-- **A region list read with its default**: the region's value, which
the default is where the region is skipped. -/
theorem entryAt_regionList (ok : OrdK K) (B : List Int) {V : Ty} (w : Int → SVal V) (d : SVal V)
    (hB : ∀ b ∈ B, ok.lo ≤ b ∧ b < ok.hi) (hlo : ok.lo ∈ B) (k : K.Denote) :
    entryAt (SMap.ofList (regionList ok B w fun v => v.beq d)) d k = w (floorIn ok.lo B (ok.val k)) := by
  unfold entryAt
  rw [SMap.toList_ofList, lookupBy_regionList ok B w _ hB hlo k]
  split
  · rename_i hs
    exact (SVal.eq_of_beq _ _ hs).symm
  · rfl

/-- **The value rebuilt**: at a floored mapping the key `k` holds what
`f k` held, listed region by region over the breakpoints `B`
(`regionList`), the default what the largest key's floor held; an outer
mapping's entries and default rebuilt; the rest copied. -/
def FloorShape.rebuild (ok : OrdK K) (f : K.Denote → K.Denote) (B : List Int) :
    {T : Ty} → FloorShape K T → SVal T → SVal T
  | _, .keep _, v => v
  | _, .floor s, .map m d =>
    let dflt := s.rebuild ok f B (entryAt m d (f ok.top))
    SVal.map (SMap.ofList (regionList ok B (fun b => s.rebuild ok f B (entryAt m d (f (ok.ofInt b))))
      fun v => v.beq dflt)) dflt
  | _, .outer _ s, .map m d =>
    SVal.map (SMap.ofList (m.toList.map fun e => (e.1, s.rebuild ok f B e.2))) (s.rebuild ok f B d)
  | _, .arr _, .array (n := n) es sh hn =>
    let L := es.toList ++ sh.toList
    let m := cutIn ok.hi B fun b => decide ((L.length : Int) ≤ ok.val (f (ok.ofInt b)))
    let slots := (List.range m.toNat).map fun (t : Nat) => L.getD (ok.val (f (ok.ofInt (t : Int)))).toNat (.prim (PrimTy.dflt _))
    .array (SVec.ofList (slots.take n)) (SList.ofList (slots.drop n)) (SVal.take_lt_bound slots hn)

/-- **A path's keys at their floors**: `f` at each floored mapping, the
rest kept. -/
def FloorShape.floorPath (f : K.Denote → K.Denote) :
    {T U : Ty} → FloorShape K T → Path T U → Path T U
  | _, _, .floor s, .key k p => .key (f k) (s.floorPath f p)
  | _, _, .outer _ s, .key k p => .key k (s.floorPath f p)
  | _, _, .arr hK, .at i p => .at (FloorShape.fU hK f i) p
  | _, _, _, p => p

/-- The shape a path reaches. -/
def FloorShape.follow : {T U : Ty} → FloorShape K T → Path T U → FloorShape K U
  | _, _, .floor s, .key _ p => s.follow p
  | _, _, .outer _ s, .key _ p => s.follow p
  | _, _, .arr _, .at _ _ => .keep _
  | _, _, .keep _, _ => .keep _
  | _, _, s, .nil => s

theorem FloorShape.floorPath_nil (f : K.Denote → K.Denote) {T : Ty} (s : FloorShape K T) :
    s.floorPath f .nil = .nil := by
  cases s <;> rfl

theorem FloorShape.follow_nil {T : Ty} (s : FloorShape K T) : s.follow .nil = s := by
  cases s <;> rfl

theorem FloorShape.floorPath_keep (f : K.Denote → K.Denote) {T U : Ty} (p : Path T U) :
    (FloorShape.keep (K := K) T).floorPath f p = p := by
  cases p <;> rfl

theorem FloorShape.follow_keep {T U : Ty} (p : Path T U) : (FloorShape.keep (K := K) T).follow p = .keep U := by
  cases p <;> rfl

theorem FloorShape.floorPath_append (f : K.Denote → K.Denote) :
    ∀ {T U W : Ty} (s : FloorShape K T) (p : Path T U) (q : Path U W),
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
  | _, _, _, .arr hK, .at i p, q => by
    cases p
    cases q
    simp only [FloorShape.floorPath, FloorShape.follow, Path.append_at, Path.append_nil,
      FloorShape.floorPath_keep]

theorem FloorShape.follow_append :
    ∀ {T U W : Ty} (s : FloorShape K T) (p : Path T U) (q : Path U W),
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
  | _, _, _, .arr hK, .at i p, q => by
    cases p
    cases q
    simp only [FloorShape.follow, Path.append_at, Path.append_nil, FloorShape.follow_keep]

/-- A shape reached floors an array only where the shape does. -/
theorem FloorShape.hasArr_follow : ∀ {T U : Ty} (s : FloorShape K T) (q : Path T U),
    (s.follow q).hasArr = true → s.hasArr = true
  | _, _, s, .nil, h => by rwa [FloorShape.follow_nil] at h
  | _, _, .keep _, q, h => by rw [FloorShape.follow_keep] at h; exact h
  | _, _, .floor s, .key _ q, h => FloorShape.hasArr_follow s q h
  | _, _, .outer _ s, .key _ q, h => FloorShape.hasArr_follow s q h
  | _, _, .arr _, .at _ _, _ => rfl

/-- A reference at its floors. -/
def _root_.Solidity.SRef.floorRef (K : PrimTy) (f : K.Denote → K.Denote) {U : Ty} (r : SRef C U) :
    SRef C U :=
  ⟨r.root, r.hroot, (FloorShape.of K r.ty).floorPath f r.path⟩

/-- **A root rebuilt.** -/
def MRoot.surgery (R : MRoot C) (ok : OrdK K) (f : K.Denote → K.Denote) (B : List Int)
    (st : Storage C) : Storage C :=
  st.set R.h ((FloorShape.of K R.ty).rebuild ok f B (st.get R.h))

theorem word_of_get {st st' : Storage C} {P : PrimTy} (r : SRef C (.prim P))
    (h : st'.get r.hroot = st.get r.hroot) : st'.obs.word (.ref r) = st.obs.word (.ref r) := by
  rw [Storage.obs_word_ref, Storage.obs_word_ref, h]

theorem has_of_get {st st' : Storage C} {U : Ty} (r : SRef C U)
    (h : st'.get r.hroot = st.get r.hroot) : st'.obs.has (.ref r) = st.obs.has (.ref r) := by
  rw [Storage.obs_has_ref, Storage.obs_has_ref, h]

theorem len_of_get {st st' : Storage C} {E : Ty} (r : SRef C (.ref (.array E)))
    (h : st'.get r.hroot = st.get r.hroot) : st'.obs.len (.ref r) = st.obs.len (.ref r) := by
  rw [Storage.obs_len_ref, Storage.obs_len_ref, h]

/-- A lookup in the entries with their values mapped. -/
theorem lookupBy_mapSnd {κ V W : Type} [DecidableEq κ] (F : V → W) (k : κ) :
    ∀ l : List (κ × V), lookupBy k (l.map fun e => (e.1, F e.2)) = (lookupBy k l).map F
  | [] => rfl
  | (k', v) :: l => by
    rw [List.map_cons, lookupBy, lookupBy]
    by_cases e : k = k'
    · rw [if_pos e, if_pos e]; rfl
    · rw [if_neg e, if_neg e]; exact lookupBy_mapSnd F k l

/-- **`f` is constant on the regions of the breakpoints `B`**, which lie in
the key type's range and start at its least value. -/
def FloorsOn (ok : OrdK K) (f : K.Denote → K.Denote) (B : List Int) : Prop :=
  (∀ b ∈ B, ok.lo ≤ b ∧ b < ok.hi) ∧ ok.lo ∈ B ∧
    ∀ k : K.Denote, f (ok.ofInt (floorIn ok.lo B (ok.val k))) = f k

/-- The slots a rebuilt array keeps: the first breakpoint whose floor is at
or past the old slots' count, `2^256` where none is. -/
abbrev arrCut (f : PrimTy.uint.Denote → PrimTy.uint.Denote) (B : List Int) (len : Nat) : Int :=
  cutIn OrdK.uint.hi B fun b => decide ((len : Int) ≤ OrdK.uint.val (f (OrdK.uint.ofInt b)))

theorem arrCut_spec (f : PrimTy.uint.Denote → PrimTy.uint.Denote) (B : List Int) (len : Nat) :
    arrCut f B len ≤ OrdK.uint.hi ∧
      (∀ b ∈ B, (len : Int) ≤ OrdK.uint.val (f (OrdK.uint.ofInt b)) → arrCut f B len ≤ b) ∧
      (arrCut f B len = OrdK.uint.hi ∨ (arrCut f B len ∈ B ∧
        (len : Int) ≤ OrdK.uint.val (f (OrdK.uint.ofInt (arrCut f B len))))) := by
  obtain ⟨h1, h2, h3⟩ := cutIn_spec B (fun b => decide ((len : Int) ≤ OrdK.uint.val (f (OrdK.uint.ofInt b))))
    OrdK.uint.hi
  refine ⟨h1, fun b hb hl => h2 b hb (decide_eq_true hl), ?_⟩
  rcases h3 with h | ⟨h, hp⟩
  · exact .inl h
  · exact .inr ⟨h, of_decide_eq_true hp⟩

theorem uint_ofInt_toNat (i : PrimTy.uint.Denote) : OrdK.uint.ofInt ((i.1.toNat : Nat) : Int) = i := by
  have h0 := (OrdK.uint.bounds i).1
  have e : ((i.1.toNat : Nat) : Int) = OrdK.uint.val i := Int.toNat_of_nonneg h0
  rw [e, OrdK.ofInt_val]

/-- **A rebuilt array's slot**: the old array's slot at the floor, there
exactly where that one is. -/
theorem arr_rebuild_slot {e : PrimTy} (f : PrimTy.uint.Denote → PrimTy.uint.Denote) (B : List Int)
    (hf : FloorsOn .uint f B) (hA : ArrOK .uint f) (L : List (SVal (.prim e))) (d : SVal (.prim e))
    (i : PrimTy.uint.Denote) :
    ((List.range (arrCut f B L.length).toNat).map
        fun (t : Nat) => L.getD (OrdK.uint.val (f (OrdK.uint.ofInt (t : Int)))).toNat d)[i.1.toNat]? =
      L[(f i).1.toNat]? := by
  obtain ⟨hm1, hm2, hm3⟩ := arrCut_spec f B L.length
  have hi := OrdK.uint.bounds i
  have hfi := OrdK.uint.bounds (f i)
  simp only [OrdK.lo, OrdK.val] at hi hfi
  rw [List.getElem?_map]
  by_cases ht : i.1.toNat < (arrCut f B L.length).toNat
  · rw [List.getElem?_range ht, Option.map_some, uint_ofInt_toNat]
    have hlt : (f i).1.toNat < L.length := by
      apply Classical.byContradiction
      intro hn
      have hle : (L.length : Int) ≤ OrdK.uint.val (f i) := by
        show (L.length : Int) ≤ (f i).1
        omega
      have hbB : floorIn 0 B i.1 ∈ B := by
        rcases floorIn_mem 0 B i.1 with h | h
        · rw [h]; exact hf.2.1
        · exact h
      have hfb : f (OrdK.uint.ofInt (floorIn 0 B i.1)) = f i := hf.2.2 i
      have h1 := hm2 _ hbB (by rw [hfb]; exact hle)
      have h2 := floorIn_le 0 B (x := i.1) hi.1
      omega
    show some (L.getD (f i).1.toNat d) = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    rfl
  · rw [List.getElem?_eq_none (by rw [List.length_range]; omega), Option.map_none]
    have hmi : arrCut f B L.length ≤ i.1 := by omega
    rcases hm3 with h | ⟨hmB, hmP⟩
    · have : i.1 < OrdK.uint.hi := hi.2
      omega
    · have h0 := (hf.1 _ hmB).1
      have hmono := hA.1 (OrdK.uint.ofInt (arrCut f B L.length)) i (by
        rw [OrdK.val_ofInt _ h0 (hf.1 _ hmB).2]; exact hmi)
      have : L.length ≤ (f i).1.toNat := by
        have := Int.le_trans hmP hmono
        simp only [OrdK.val] at this
        omega
      exact (List.getElem?_eq_none this).symm

/-- **A rebuilt array keeps its live length**: the floors never pass their
keys, so the slots below it stay. -/
theorem arr_rebuild_len (f : PrimTy.uint.Denote → PrimTy.uint.Denote) (B : List Int)
    (hf : FloorsOn .uint f B) (hA : ArrOK .uint f) {n len : Nat} (hn : n ≤ len) (hn' : n < 2 ^ 256) :
    n ≤ (arrCut f B len).toNat := by
  obtain ⟨-, -, hm3⟩ := arrCut_spec f B len
  apply Classical.byContradiction
  intro hlt
  rcases hm3 with h | ⟨hmB, hmP⟩
  · rw [h] at hlt
    simp only [OrdK.hi] at hlt
    omega
  · have h0 := (hf.1 _ hmB)
    have := hA.2 (OrdK.uint.ofInt (arrCut f B len))
    rw [OrdK.val_ofInt _ h0.1 h0.2] at this
    omega

/-- **A rebuilt value reads at a path what the old one read at its
floors**, the value there rebuilt as the shape it reaches has it, where
`f` is constant on the regions (and, where the shape floors an array's
slots, monotone and never above its key). -/
theorem FloorShape.rebuild_find (ok : OrdK K) (f : K.Denote → K.Denote) (B : List Int)
    (hf : FloorsOn ok f B) :
    ∀ {T : Ty} (s : FloorShape K T), (s.hasArr = true → ArrOK ok f) → ∀ (v : SVal T) {U : Ty} (q : Path T U),
      (s.rebuild ok f B v).findM q = (v.findM (s.floorPath f q)).map ((s.follow q).rebuild ok f B)
  | _, .keep _, _, v, _, q => by
    rw [FloorShape.floorPath_keep, FloorShape.follow_keep]
    show v.findM q = _
    cases v.findM q <;> rfl
  | _, .floor s, hA, .map m d, _, q => by
    cases q with
    | nil => rfl
    | key k q' =>
      simp only [FloorShape.rebuild, FloorShape.floorPath, FloorShape.follow]
      rw [findM_key_entryAt, findM_key_entryAt, entryAt_regionList ok B _ _ hf.1 hf.2.1 k, hf.2.2 k,
        FloorShape.rebuild_find ok f B hf s hA _ q']
  | _, .outer _ s, hA, .map m d, _, q => by
    cases q with
    | nil => rfl
    | key o q' =>
      simp only [FloorShape.rebuild, FloorShape.floorPath, FloorShape.follow, SVal.findM, SMap.toList_ofList]
      rw [lookupBy_mapSnd (s.rebuild ok f B) o m.toList]
      cases lookupBy o m.toList with
      | none => exact FloorShape.rebuild_find ok f B hf s hA d q'
      | some x => exact FloorShape.rebuild_find ok f B hf s hA x q'
  | _, .arr hK, hA, .array es sh hn, _, q => by
    have hA' := hA rfl
    cases ok with
    | int => exact nomatch hK
    | uint =>
    cases q with
    | nil => rfl
    | «at» i q' =>
      cases q'
      simp only [FloorShape.rebuild, FloorShape.floorPath, FloorShape.follow, SVal.findM,
        SVec.toList_ofList, SList.toList_ofList, List.take_append_drop]
      rw [arr_rebuild_slot f B hf hA' _ _ i, show FloorShape.fU hK f = f from rfl]
      cases (es.toList ++ sh.toList)[(f i).1.toNat]? <;> rfl

/-- **A rebuilt value reads the word its floors held.** -/
theorem FloorShape.rebuild_word (ok : OrdK K) (f : K.Denote → K.Denote) (B : List Int)
    (hf : FloorsOn ok f B) {T : Ty} (s : FloorShape K T) (hA : s.hasArr = true → ArrOK ok f)
    (v : SVal T) {P : PrimTy} (q : Path T (.prim P)) :
    SVal.wordOf ((s.rebuild ok f B v).findM q) = SVal.wordOf (v.findM (s.floorPath f q)) := by
  rw [FloorShape.rebuild_find ok f B hf s hA v q]
  generalize s.follow q = s'
  cases s' with
  | keep => cases v.findM (s.floorPath f q) <;> rfl

/-- **A rebuilt value has a location exactly where its floors had one.** -/
theorem FloorShape.rebuild_has (ok : OrdK K) (f : K.Denote → K.Denote) (B : List Int)
    (hf : FloorsOn ok f B) {T : Ty} (s : FloorShape K T) (hA : s.hasArr = true → ArrOK ok f)
    (v : SVal T) {U : Ty} (q : Path T U) :
    ((s.rebuild ok f B v).findM q).isSome = (v.findM (s.floorPath f q)).isSome := by
  rw [FloorShape.rebuild_find ok f B hf s hA v q]
  cases v.findM (s.floorPath f q) <;> rfl

/-- **A rebuilt array keeps its live length.** -/
theorem FloorShape.rebuild_lenOf (ok : OrdK K) (f : K.Denote → K.Denote) (B : List Int)
    (hf : FloorsOn ok f B) {E : Ty} (s : FloorShape K (.ref (.array E))) (hA : s.hasArr = true → ArrOK ok f)
    (v : SVal (.ref (.array E))) : SVal.lenOf (some (s.rebuild ok f B v)) = SVal.lenOf (some v) := by
  cases s with
  | keep => rfl
  | arr hK =>
    have hA' := hA rfl
    cases ok with
    | int => exact nomatch hK
    | uint =>
    cases v with
    | @array _ n es sh hn =>
      simp only [FloorShape.rebuild, SVal.lenOf, SVal.view_array]
      rw [List.length_take, List.length_map, List.length_range]
      have hl : n ≤ (es.toList ++ sh.toList).length := by
        rw [List.length_append, SVec.length_toList]; exact Nat.le_add_right _ _
      exact Nat.min_eq_left (arr_rebuild_len f B hf hA' hl hn)

/-- **A rebuilt array reads the live length its floors held.** -/
theorem FloorShape.rebuild_len (ok : OrdK K) (f : K.Denote → K.Denote) (B : List Int)
    (hf : FloorsOn ok f B) {T : Ty} (s : FloorShape K T) (hA : s.hasArr = true → ArrOK ok f)
    (v : SVal T) {E : Ty} (q : Path T (.ref (.array E))) :
    SVal.lenOf ((s.rebuild ok f B v).findM q) = SVal.lenOf (v.findM (s.floorPath f q)) := by
  rw [FloorShape.rebuild_find ok f B hf s hA v q]
  cases hx : v.findM (s.floorPath f q) with
  | none => rfl
  | some x =>
    show SVal.lenOf (some ((s.follow q).rebuild ok f B x)) = _
    exact FloorShape.rebuild_lenOf ok f B hf _ (fun h => hA (FloorShape.hasArr_follow s q h)) x

/-- **The rebuilt root reads at its floors**, the value there rebuilt as
the shape it reaches has it. -/
theorem MRoot.surgery_find (R : MRoot C) (ok : OrdK K) (f : K.Denote → K.Denote) (B : List Int)
    (st : Storage C) (hf : FloorsOn ok f B) (hA : (FloorShape.of K R.ty).hasArr = true → ArrOK ok f)
    {U : Ty} (r : SRef C U) (hr : r.root = R.name) :
    ((R.surgery ok f B st).get r.hroot).findM r.path =
      ((st.get r.hroot).findM ((FloorShape.of K r.ty).floorPath f r.path)).map
        (((FloorShape.of K r.ty).follow r.path).rebuild ok f B) := by
  obtain ⟨root, hroot, path⟩ := r
  simp only at hr
  subst hr
  obtain ⟨n, T, hT⟩ := R
  have e : T = _ := (Option.some.inj (hT.symm.trans hroot))
  subst e
  show ((st.set hT _).get hroot).findM path = _
  rw [SFields.get_set_same]
  exact FloorShape.rebuild_find ok f B hf _ hA _ path

/-- Another root is kept. -/
theorem MRoot.surgery_get_ne (R : MRoot C) (ok : OrdK K) (f : K.Denote → K.Denote) (B : List Int)
    (st : Storage C) {T : Ty} {a : Name} (h : C.rootType a = some T) (ha : a ≠ R.name) :
    (R.surgery ok f B st).get h = st.get h :=
  SFields.get_set_ne st R.h h (Ne.symm ha) _

/-- Every root of `Rs` rebuilt, the first last. -/
def surgeryAll (ok : OrdK K) (f : K.Denote → K.Denote) (B : List Int) : List (MRoot C) → Storage C → Storage C
  | [], st => st
  | R :: Rs, st => R.surgery ok f B (surgeryAll ok f B Rs st)

theorem surgeryAll_get_ne (ok : OrdK K) (f : K.Denote → K.Denote) (B : List Int) (st : Storage C)
    {T : Ty} {a : Name} (h : C.rootType a = some T) : ∀ Rs : List (MRoot C), a ∉ Rs.map (·.name) →
      (surgeryAll ok f B Rs st).get h = st.get h
  | [], _ => rfl
  | R :: Rs, hn => by
    simp only [List.map_cons, List.mem_cons, not_or] at hn
    rw [surgeryAll, MRoot.surgery_get_ne R ok f B _ h hn.1, surgeryAll_get_ne ok f B st h Rs hn.2]

theorem surgeryAll_find (ok : OrdK K) (f : K.Denote → K.Denote) (B : List Int) (st : Storage C)
    (hf : FloorsOn ok f B) {U : Ty} (r : SRef C U) :
    ∀ Rs : List (MRoot C), (Rs.map (·.name)).Nodup →
      (∀ R ∈ Rs, (FloorShape.of K R.ty).hasArr = true → ArrOK ok f) → r.root ∈ Rs.map (·.name) →
      ((surgeryAll ok f B Rs st).get r.hroot).findM r.path =
        ((st.get r.hroot).findM ((FloorShape.of K r.ty).floorPath f r.path)).map
          (((FloorShape.of K r.ty).follow r.path).rebuild ok f B)
  | [], _, _, h => nomatch h
  | R' :: Rs, hn, hA, hR => by
    rw [List.map_cons, List.nodup_cons] at hn
    rw [surgeryAll]
    by_cases he : r.root = R'.name
    · rw [MRoot.surgery_find R' ok f B _ hf (hA R' List.mem_cons_self) r he,
        surgeryAll_get_ne ok f B st r.hroot Rs (he ▸ hn.1)]
    · rw [MRoot.surgery_get_ne R' ok f B _ r.hroot he]
      rw [List.map_cons, List.mem_cons] at hR
      exact surgeryAll_find ok f B st hf r Rs hn.2 (fun R hR => hA R (List.mem_cons_of_mem _ hR))
        (hR.resolve_left he)

theorem wordOf_map_rebuild (ok : OrdK K) (f : K.Denote → K.Denote) (B : List Int) {P : PrimTy}
    (s : FloorShape K (.prim P)) (x : Option (SVal (.prim P))) :
    SVal.wordOf (x.map (s.rebuild ok f B)) = SVal.wordOf x := by
  cases s with
  | keep => cases x <;> rfl

theorem surgeryAll_word (ok : OrdK K) (f : K.Denote → K.Denote) (B : List Int) (st : Storage C)
    (hf : FloorsOn ok f B) {P : PrimTy} (r : SRef C (.prim P)) (Rs : List (MRoot C))
    (hn : (Rs.map (·.name)).Nodup) (hA : ∀ R ∈ Rs, (FloorShape.of K R.ty).hasArr = true → ArrOK ok f)
    (hR : r.root ∈ Rs.map (·.name)) :
    (surgeryAll ok f B Rs st).obs.word (.ref r) = st.obs.word (.ref (r.floorRef K f)) := by
  rw [Storage.obs_word_ref, Storage.obs_word_ref]
  show SVal.wordOf (((surgeryAll ok f B Rs st).get r.hroot).findM r.path) =
    SVal.wordOf ((st.get r.hroot).findM ((FloorShape.of K r.ty).floorPath f r.path))
  rw [surgeryAll_find ok f B st hf r Rs hn hA hR, wordOf_map_rebuild]

theorem surgeryAll_has (ok : OrdK K) (f : K.Denote → K.Denote) (B : List Int) (st : Storage C)
    (hf : FloorsOn ok f B) {U : Ty} (r : SRef C U) (Rs : List (MRoot C))
    (hn : (Rs.map (·.name)).Nodup) (hA : ∀ R ∈ Rs, (FloorShape.of K R.ty).hasArr = true → ArrOK ok f)
    (hR : r.root ∈ Rs.map (·.name)) :
    (surgeryAll ok f B Rs st).obs.has (.ref r) = st.obs.has (.ref (r.floorRef K f)) := by
  rw [Storage.obs_has_ref, Storage.obs_has_ref]
  show (((surgeryAll ok f B Rs st).get r.hroot).findM r.path).isSome =
    ((st.get r.hroot).findM ((FloorShape.of K r.ty).floorPath f r.path)).isSome
  rw [surgeryAll_find ok f B st hf r Rs hn hA hR]
  cases (st.get r.hroot).findM ((FloorShape.of K r.ty).floorPath f r.path) <;> rfl

theorem surgeryAll_len (ok : OrdK K) (f : K.Denote → K.Denote) (B : List Int) (st : Storage C)
    (hf : FloorsOn ok f B) {E : Ty} (r : SRef C (.ref (.array E))) (Rs : List (MRoot C))
    (hn : (Rs.map (·.name)).Nodup) (hA : ∀ R ∈ Rs, (FloorShape.of K R.ty).hasArr = true → ArrOK ok f)
    (hR : r.root ∈ Rs.map (·.name)) :
    (surgeryAll ok f B Rs st).obs.len (.ref r) = st.obs.len (.ref (r.floorRef K f)) := by
  rw [Storage.obs_len_ref, Storage.obs_len_ref]
  show SVal.lenOf (((surgeryAll ok f B Rs st).get r.hroot).findM r.path) =
    SVal.lenOf ((st.get r.hroot).findM ((FloorShape.of K r.ty).floorPath f r.path))
  rw [surgeryAll_find ok f B st hf r Rs hn hA hR]
  obtain ⟨R, hRm, hRn⟩ := List.mem_map.1 hR
  have hA' : (FloorShape.of K r.ty).hasArr = true → ArrOK ok f := by
    obtain ⟨n, T, hT⟩ := R
    simp only at hRn
    have e : T = r.ty := Option.some.inj (hT.symm.trans (hRn ▸ r.hroot))
    subst e
    exact hA _ hRm
  cases hx : (st.get r.hroot).findM ((FloorShape.of K r.ty).floorPath f r.path) with
  | none => rfl
  | some x =>
    show SVal.lenOf (some (((FloorShape.of K r.ty).follow r.path).rebuild ok f B x)) = _
    exact FloorShape.rebuild_lenOf ok f B hf _
      (fun h => hA' (FloorShape.hasArr_follow _ r.path h)) x

/-! ## The ledger rebuilt -/

/-- **The ledger rebuilt**: each address holding what its floor held,
region by region, a region of zeros (the ledger's default) left out; no
`int` pass rebuilds it. -/
def netRebuild : OrdK K → (K.Denote → K.Denote) → List Int → Ledger → Ledger
  | .uint, f, B, l => regionList .uint B (fun b => (lookupBy (f (OrdK.uint.ofInt b)) l).getD 0) (· == 0)
  | .int, _, _, l => l

/-- What a rebuilt ledger reads: at a `uint` pass, at each address its
floor's entry; never at an `int` pass. -/
def NetFloor : OrdK K → (K.Denote → K.Denote) → Ledger → Ledger → Prop
  | .uint, f, l', l => ∀ a, (lookupBy a l').getD 0 = (lookupBy (f a) l).getD 0
  | .int, _, _, _ => False

theorem netRebuild_floor (f : PrimTy.uint.Denote → PrimTy.uint.Denote) (B : List Int)
    (hf : FloorsOn .uint f B) (l : Ledger) : NetFloor .uint f (netRebuild .uint f B l) l := by
  intro a
  simp only [netRebuild]
  rw [lookupBy_regionList .uint B _ _ hf.1 hf.2.1 a]
  split
  · rename_i hs
    have h0 : (lookupBy (f (OrdK.uint.ofInt (floorIn OrdK.uint.lo B (OrdK.uint.val a)))) l).getD 0 = 0 :=
      beq_iff_eq.1 hs
    rw [hf.2.2 a] at h0
    exact h0.symm
  · show (lookupBy (f _) l).getD 0 = _
    rw [hf.2.2 a]

/-! ## The fragment's terms -/

/-- **What a pass rebuilds**: the roots its blocks read at their
variables, and whether they read the ledger so (`uint` passes only:
`apfRoots` sets `net` from `OrdK.netB`, and `NetRel`, `NetFloor` are
`False` at `int`; a flag rather than an index of `OrdK`, so the terms'
fragment `ApfTm` stays one type for both passes). -/
structure ARoots where
  names : List Name
  net : Bool

/-- **A term of the fragment** (`false`): roots of `Rs` read only along a
path of their own (`true`: `rroot`, then keys, `rkey`, and members,
`rfield`), the word there (`rword`); every other path at a root outside
`Rs`; no other storage access; the starting ledger read at an address
(`net`), KeY `int` literals, `uint`s read as KeY `int`s and their
arithmetic and comparisons (`zlit`, `toInt`, `zbin`, `zcmp`). -/
inductive ApfTm (Rs : ARoots) : Bool → {s : Srt} → LTm C s → Type where
  | var {p : PrimTy} (k : Nat) : ApfTm Rs false (LTm.var (p := p) k)
  | lit {p : PrimTy} (v : p.Denote) : ApfTm Rs false (.app0 (.lit v))
  | env (k : EnvKey) : ApfTm Rs false (.app0 (.env k))
  | root (r : Name) {T : Ty} (h : C.rootType r = some T) (hr : r ∉ Rs.names) : ApfTm Rs false (.app0 (.root r h))
  | rroot (r : Name) {T : Ty} (h : C.rootType r = some T) (hr : r ∈ Rs.names) : ApfTm Rs true (.app0 (.root r h))
  | field {s f : Name} {T : Ty} (h : C.fieldType s f = some T) {q : LTm C (.path (.ref (.struct s)))}
      (hq : ApfTm Rs false q) : ApfTm Rs false (.app1 (.field h) q)
  | rfield {s f : Name} {T : Ty} (h : C.fieldType s f = some T) {q : LTm C (.path (.ref (.struct s)))}
      (hq : ApfTm Rs true q) : ApfTm Rs true (.app1 (.field h) q)
  | index {K : PrimTy} {T : Ty} {q : LTm C (.path (.ref (.mapping K T)))} {i : LTm C (.val K)}
      (hq : ApfTm Rs false q) (hi : ApfTm Rs false i) : ApfTm Rs false (.index .map q i)
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
  | zlit (n : Int) : ApfTm Rs false (.app0 (.zlit n))
  | toInt {t : LTm C (.val .uint)} (ht : ApfTm Rs false t) : ApfTm Rs false (.app1 .toInt t)
  | net {t : LTm C (.val .uint)} (ht : ApfTm Rs false t) : ApfTm Rs false (.app1 .net t)
  | zbin (op : BinOp) (h : op.zArith = true) {a b : LTm C .kint} (ha : ApfTm Rs false a)
      (hb : ApfTm Rs false b) : ApfTm Rs false (.app2 (.zbin op h) a b)
  | zcmp (op : BinOp) (h : op.zCmp = true) {a b : LTm C .kint} (ha : ApfTm Rs false a)
      (hb : ApfTm Rs false b) : ApfTm Rs false (.app2 (.zcmp op h) a b)
  /-- An array element along a path of a root of `Rs` (feature 32). -/
  | rat {R : RefTy} {E : Ty} (ar : ArrTy R E) {q : LTm C (.path (.ref R))} {i : LTm C (.val .uint)}
      (hq : ApfTm Rs true q) (hi : ApfTm Rs false i) : ApfTm Rs true (.index (.arr ar) q i)
  /-- An array element elsewhere. -/
  | aidx {R : RefTy} {E : Ty} (ar : ArrTy R E) {q : LTm C (.path (.ref R))} {i : LTm C (.val .uint)}
      (hq : ApfTm Rs false q) (hi : ApfTm Rs false i) : ApfTm Rs false (.index (.arr ar) q i)
  /-- Whether a location is there, along a path of a root of `Rs`, or elsewhere. -/
  | rhas {T : Ty} {q : LTm C (.path T)} (hq : ApfTm Rs true q) : ApfTm Rs false (.obsH q)
  | has {T : Ty} {q : LTm C (.path T)} (hq : ApfTm Rs false q) : ApfTm Rs false (.obsH q)
  /-- An array's live length, along a path of a root of `Rs`, or elsewhere. -/
  | rlen {E : Ty} {q : LTm C (.path (.ref (.array E)))} (hq : ApfTm Rs true q) : ApfTm Rs false (.obsL q)
  | len {E : Ty} {q : LTm C (.path (.ref (.array E)))} (hq : ApfTm Rs false q) : ApfTm Rs false (.obsL q)
  /-- A conditional value (the Theory's read of a slot: its word where it is
  there, `⊥` where not). -/
  | ite {p : PrimTy} {c : LTm C (.val .bool)} {a b : LTm C (.val p)} (hc : ApfTm Rs false c)
      (ha : ApfTm Rs false a) (hb : ApfTm Rs false b) : ApfTm Rs false (.app3 .ite c a b)

namespace ApfTm

variable {Rs : ARoots}

/-- Recognize the fragment: a term (`false`), or a path at a root of `Rs`
(`true`). -/
def ofTerm? (Rs : ARoots) : (b : Bool) → {s : Srt} → (t : LTm C s) → Option (ApfTm Rs b t)
  | false, _, .var k => some (.var k)
  | false, _, .app0 (.lit v) => some (.lit v)
  | false, _, .app0 (.env k) => some (.env k)
  | false, _, .app0 (.zlit n) => some (.zlit n)
  | false, _, .app0 (.root r h) => if hr : r ∈ Rs.names then none else some (.root r h hr)
  | true, _, .app0 (.root r h) => if hr : r ∈ Rs.names then some (.rroot r h hr) else none
  | false, _, .app1 (.field h) q => (ofTerm? Rs false q).map (.field h)
  | true, _, .app1 (.field h) q => (ofTerm? Rs true q).map (.rfield h)
  | false, _, .app1 (.unop op h) t => (ofTerm? Rs false t).map (.unop op h)
  | false, _, .app1 .toInt t => (ofTerm? Rs false t).map .toInt
  | false, _, .app1 .net t => (ofTerm? Rs false t).map .net
  | false, _, .app2 (.binop op h) a b => do return .binop op h (← ofTerm? Rs false a) (← ofTerm? Rs false b)
  | false, _, .app2 (.zbin op h) a b => do return .zbin op h (← ofTerm? Rs false a) (← ofTerm? Rs false b)
  | false, _, .app2 (.zcmp op h) a b => do return .zcmp op h (← ofTerm? Rs false a) (← ofTerm? Rs false b)
  | false, _, .obsW q =>
    match ofTerm? Rs true q with
    | some hq => some (.rword hq)
    | none => (ofTerm? Rs false q).map .word
  | false, _, .index it q i =>
    match it, q, i with
    | .map, q, i => do return .index (← ofTerm? Rs false q) (← ofTerm? Rs false i)
    | .arr ar, q, i => do return .aidx ar (← ofTerm? Rs false q) (← ofTerm? Rs false i)
  | true, _, .index it q i =>
    match it, q, i with
    | .map, q, i => do return .rkey (← ofTerm? Rs true q) (← ofTerm? Rs false i)
    | .arr ar, q, i => do return .rat ar (← ofTerm? Rs true q) (← ofTerm? Rs false i)
  | false, _, .seq d a => do return .seq (← ofTerm? Rs false d) (← ofTerm? Rs false a)
  | false, _, .orElse a b => do return .orElse (← ofTerm? Rs false a) (← ofTerm? Rs false b)
  | false, _, .kite a b t e => do
    return .kite (← ofTerm? Rs false a) (← ofTerm? Rs false b) (← ofTerm? Rs false t) (← ofTerm? Rs false e)
  | false, _, .err => some .err
  | false, _, .app3 .ite c a b => do
    return .ite (← ofTerm? Rs false c) (← ofTerm? Rs false a) (← ofTerm? Rs false b)
  | false, _, .obsH q =>
    match ofTerm? Rs true q with
    | some hq => some (.rhas hq)
    | none => (ofTerm? Rs false q).map .has
  | false, _, .obsL q =>
    match ofTerm? Rs true q with
    | some hq => some (.rlen hq)
    | none => (ofTerm? Rs false q).map .len
  | _, _, _ => none

/-- A path of a root of `Rs` still along its mappings: keys only. -/
def pre : {b : Bool} → {s : Srt} → {t : LTm C s} → ApfTm Rs b t → Bool
  | _, _, _, .rroot .. => true
  | _, _, _, .rkey hq _ => hq.pre
  | _, _, _, _ => false

/-- A path value at a root of `Rs` exactly where `b`. -/
def RootsAt (Rs : ARoots) (b : Bool) {H : HTy} : (s : Srt) → Option (s.Den C H) → Prop
  | .path _, some r => decide (r.root ∈ Rs.names) = b
  | _, _ => True

theorem RootsAt.none (Rs : ARoots) (b : Bool) {H : HTy} : ∀ s : Srt, RootsAt (C := C) Rs b (H := H) s none
  | .path _ | .val _ | .st | .sv _ | .ident _ | .addr _ | .mem | .mv _ | .sts _ | .spath _ _ | .kint => trivial

/-- **The fragment's paths are at roots of `Rs` exactly where `b`.** -/
theorem rootsAt (g : State C []) (ν : AEnv) {b : Bool} {s : Srt} {t : LTm C s} (ht : ApfTm Rs b t) :
    RootsAt Rs b s (t.eval g ν) := by
  induction ht with
  | var | lit | env | word | rword | unop | binop | zlit | toInt | net | zbin | zcmp | rhas | has | rlen | len
  | ite =>
    trivial
  | root r h hr => exact decide_eq_false hr
  | rroot r h hr => exact decide_eq_true hr
  | @field _ _ _ h q hq ih | @rfield _ _ _ h q hq ih =>
    rw [LTm.eval_app1, Close.Op1.eval_field]
    cases hq' : (q.eval g ν : Option (SRef C _)) with
    | none => exact RootsAt.none Rs _ _
    | some r => rw [hq'] at ih; exact ih
  | @index _ _ q i hq hi ihq ihi | @rkey _ _ q i hq hi ihq ihi | @aidx _ _ _ q i hq hi ihq ihi
  | @rat _ _ _ q i hq hi ihq ihi =>
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

/-- The positions of `ks`, at `K`. -/
def ksP (K : PrimTy) (ks : List Nat) : List Parameter := ks.map (⟨K, ·⟩)

end ApfTm

/-- A key of type `K'` read at `K`, where they are one type. -/
def castKey {K' : PrimTy} (h : K' = K) (i : LTm C (.val K')) : LTm C (.val K) := h ▸ i

theorem castKey_rfl (i : LTm C (.val K)) : castKey rfl i = i := rfl

/-- **A ledger address read at its floor**: at a `uint` pass, a block
variable, or a ground term of the index set read alike (`R`); never at an
`int` pass. -/
def NetRel : OrdK K → List Nat → List Parameter → (LTm C (.val K) → Prop) → LTm C (.val .uint) → Prop → Prop
  | .uint, ks, Bs, Gd, i, R => (∃ k ∈ ks, i = .var k) ∨ ((∀ q ∈ i.parameters, q ∉ Bs) ∧ Gd i ∧ R)
  | .int, _, _, _, _, _ => False

namespace ApfTm

variable {Rs : ARoots}

/-- **Where a term reads alike in the rebuilt storage**: the variables of
`ks` only as keys of type `K` along a root of `Rs`'s mappings, or as
ledger addresses where the ledger is rebuilt; every other such key ground
(`Gd`), mentioning no binder of `Bs`; no key past them one of type `K`
along the mappings. -/
def Rel (ok : OrdK K) (ks : List Nat) (Bs : List Parameter) (Gd : LTm C (.val K) → Prop) :
    {b : Bool} → {s : Srt} → {t : LTm C s} → ApfTm Rs b t → Prop
  | _, _, _, @ApfTm.var _ _ p k => (⟨p, k⟩ : Parameter) ∉ ksP K ks
  | _, _, _, .lit _ | _, _, _, .env _ | _, _, _, .root .. | _, _, _, .rroot .. | _, _, _, .err
  | _, _, _, .zlit _ => True
  | _, _, _, .field _ hq | _, _, _, .rfield _ hq => hq.Rel ok ks Bs Gd
  | _, _, _, .index hq hi => hq.Rel ok ks Bs Gd ∧ hi.Rel ok ks Bs Gd
  | _, _, _, .rkey (K := K') (i := i) hq hi =>
    hq.Rel ok ks Bs Gd ∧ (if h : K' = K then
      (hq.pre = true ∧ ((∃ k ∈ ks, castKey h i = .var k) ∨
        ((∀ q ∈ i.parameters, q ∉ Bs) ∧ Gd (castKey h i) ∧ hi.Rel ok ks Bs Gd))) ∨
      (hq.pre = false ∧ hi.Rel ok ks Bs Gd)
      else hi.Rel ok ks Bs Gd)
  | _, _, _, .word hq | _, _, _, .rword hq => hq.Rel ok ks Bs Gd
  | _, _, _, .unop _ _ ht | _, _, _, .toInt ht => ht.Rel ok ks Bs Gd
  | _, _, _, .net (t := i) hi =>
    if Rs.net = true then NetRel ok ks Bs Gd i (hi.Rel ok ks Bs Gd) else hi.Rel ok ks Bs Gd
  | _, _, _, .binop _ _ ha hb | _, _, _, .zbin _ _ ha hb | _, _, _, .zcmp _ _ ha hb =>
    ha.Rel ok ks Bs Gd ∧ hb.Rel ok ks Bs Gd
  | _, _, _, .seq hd ha => hd.Rel ok ks Bs Gd ∧ ha.Rel ok ks Bs Gd
  | _, _, _, .orElse ha hb => ha.Rel ok ks Bs Gd ∧ hb.Rel ok ks Bs Gd
  | _, _, _, .kite ha hb ht he =>
    ha.Rel ok ks Bs Gd ∧ hb.Rel ok ks Bs Gd ∧ ht.Rel ok ks Bs Gd ∧ he.Rel ok ks Bs Gd
  | _, _, _, .aidx _ hq hi => hq.Rel ok ks Bs Gd ∧ hi.Rel ok ks Bs Gd
  | _, _, _, .rat (R := R) (i := i) _ hq hi =>
    hq.Rel ok ks Bs Gd ∧ (if h : PrimTy.uint = K then
      (if (hq.pre && (FloorShape.of K (.ref R)).isArr) = true then
        (∃ k ∈ ks, castKey h i = .var k) ∨
          ((∀ q ∈ i.parameters, q ∉ Bs) ∧ Gd (castKey h i) ∧ hi.Rel ok ks Bs Gd)
        else hi.Rel ok ks Bs Gd)
      else hi.Rel ok ks Bs Gd)
  | _, _, _, .rhas hq | _, _, _, .has hq | _, _, _, .rlen hq | _, _, _, .len hq => hq.Rel ok ks Bs Gd
  | _, _, _, .ite hc ha hb => hc.Rel ok ks Bs Gd ∧ ha.Rel ok ks Bs Gd ∧ hb.Rel ok ks Bs Gd

end ApfTm

/-! ## Reads in the rebuilt storage -/

/-- What the rebuilding keeps: other roots whole, and the words, slot tests
and lengths of a root of `Rs` at the floors of their keys and slots
(`SRef.floorRef`); the ledger, or its entries at their floors where `Rs`
reads it. -/
structure Surg (ok : OrdK K) (g : State C []) (st' : Storage C) (nt' : Ledger) (Rs : ARoots)
    (f : K.Denote → K.Denote) : Prop where
  other : ∀ {T : Ty} {a : Name} (h : C.rootType a = some T), a ∉ Rs.names → st'.get h = g.storage.get h
  keyAt : ∀ {P : PrimTy} (r : SRef C (.prim P)), r.root ∈ Rs.names →
    st'.obs.word (.ref r) = g.storage.obs.word (.ref (r.floorRef K f))
  hasAt : ∀ {U : Ty} (r : SRef C U), r.root ∈ Rs.names →
    st'.obs.has (.ref r) = g.storage.obs.has (.ref (r.floorRef K f))
  lenAt : ∀ {E : Ty} (r : SRef C (.ref (.array E))), r.root ∈ Rs.names →
    st'.obs.len (.ref r) = g.storage.obs.len (.ref (r.floorRef K f))
  netKeep : Rs.net = false → nt' = g.net
  netAt : Rs.net = true → NetFloor ok f nt' g.net

theorem Parameter.read_var {p : PrimTy} (k : Nat) (μ : AEnv) :
    (⟨p, k⟩ : Parameter).read μ = μ.get p k := rfl

/-- **How a term reads in the rebuilt storage** at `μ'` against the old
one at `μ`: a value alike; a path of a root of `Rs` at its floors, the
shape it reaches its type's along the mappings (`pre`) and `keep` past
them. -/
def TRel (f : K.Denote → K.Denote) (pre : Bool) {H : HTy} :
    (b : Bool) → (s : Srt) → Option (s.Den C H) → Option (s.Den C H) → Prop
  | true, .path U, x', x => x = x'.map (SRef.floorRef K f) ∧
      ∀ r' ∈ x', (FloorShape.of K r'.ty).follow r'.path = (if pre then FloorShape.of K U else .keep U)
  | _, _, x', x => x' = x

theorem TRel.of_false {f : K.Denote → K.Denote} {pre : Bool} {H : HTy} {s : Srt}
    {x' x : Option (s.Den C H)} (h : TRel f pre false s x' x) : x' = x := h

theorem TRel.of_eq {f : K.Denote → K.Denote} {pre : Bool} {H : HTy} {s : Srt}
    {x' x : Option (s.Den C H)} (h : x' = x) : TRel f pre false s x' x := h

/-- A key appended to a reference, at the floors. -/
theorem SRef.floorRef_index (f : K.Denote → K.Denote) {K' : PrimTy} {V : Ty}
    (r : SRef C (.ref (.mapping K' V))) (k : K'.Denote) :
    (r.index .map k).floorRef K f =
      ⟨r.root, r.hroot, ((FloorShape.of K r.ty).floorPath f r.path).append
        (((FloorShape.of K r.ty).follow r.path).floorPath f (.key k .nil))⟩ := by
  show (⟨r.root, r.hroot, (FloorShape.of K r.ty).floorPath f (r.path.append (Path.index .map k))⟩ : SRef C V) = _
  rw [Path.index_map, FloorShape.floorPath_append]

theorem SRef.index_eq {K' : PrimTy} {V : Ty} (r : SRef C (.ref (.mapping K' V))) (k : K'.Denote) :
    r.index .map k = ⟨r.root, r.hroot, r.path.append (.key k .nil)⟩ := by
  show r.append _ = _
  rw [Path.index_map]
  rfl

theorem FloorShape.floorPath_floor_key (f : K.Denote → K.Denote) {V U : Ty} (s : FloorShape K V)
    (k : K.Denote) (p : Path V U) : (FloorShape.floor s).floorPath f (.key k p) = .key (f k) (s.floorPath f p) :=
  rfl

theorem FloorShape.floorPath_outer_key (f : K.Denote → K.Denote) {K' : PrimTy} {V U : Ty}
    (s : FloorShape K V) (k : K'.Denote) (p : Path V U) :
    (FloorShape.outer K' s).floorPath f (.key k p) = .key k (s.floorPath f p) := rfl

theorem SRef.follow_index {K' : PrimTy} {V : Ty} (r : SRef C (.ref (.mapping K' V))) (k : K'.Denote) :
    (FloorShape.of K (r.index .map k).ty).follow (r.index .map k).path =
      ((FloorShape.of K r.ty).follow r.path).follow (.key k .nil) := by
  show (FloorShape.of K r.ty).follow (r.path.append (Path.index .map k)) = _
  rw [Path.index_map, FloorShape.follow_append]

theorem SRef.floorRef_field (f : K.Denote → K.Denote) {s fn : Name} {T : Ty}
    (r : SRef C (.ref (.struct s))) (h : C.fieldType s fn = some T)
    (hk : (FloorShape.of K r.ty).follow r.path = .keep _) :
    (r.field h).floorRef K f = (r.floorRef K f).field h := by
  show (⟨r.root, r.hroot, (FloorShape.of K r.ty).floorPath f (r.path.append (.field h .nil))⟩ : SRef C T) =
    ⟨r.root, r.hroot, ((FloorShape.of K r.ty).floorPath f r.path).append (.field h .nil)⟩
  rw [FloorShape.floorPath_append, hk, FloorShape.floorPath_keep]

theorem SRef.follow_field {s fn : Name} {T : Ty} (r : SRef C (.ref (.struct s))) (h : C.fieldType s fn = some T)
    (hk : (FloorShape.of K r.ty).follow r.path = .keep _) :
    (FloorShape.of K (r.field h).ty).follow (r.field h).path = .keep T := by
  show (FloorShape.of K r.ty).follow (r.path.append (.field h .nil)) = _
  rw [FloorShape.follow_append, hk, FloorShape.follow_keep]

/-- Only a `uint` pass floors an array's slots. -/
theorem FloorShape.of_isArr {T : Ty} (h : (FloorShape.of K T).isArr = true) : K = .uint := by
  unfold FloorShape.of at h
  split at h
  · split at h
    · rename_i hK'
      subst hK'
      simp only [FloorShape.floorEq, FloorShape.isArr, Bool.false_eq_true] at h
    · simp only [FloorShape.isArr, Bool.false_eq_true] at h
  · split at h
    · assumption
    · simp only [FloorShape.isArr, Bool.false_eq_true] at h
  · simp only [FloorShape.isArr, Bool.false_eq_true] at h

/-- An array type's shape: floored slots, or kept. -/
theorem FloorShape.of_arr_keep {R : RefTy} {E : Ty} (ar : ArrTy R E)
    (h : (FloorShape.of K (.ref R)).isArr = false) : FloorShape.of K (.ref R) = .keep _ := by
  cases ar with
  | dyn =>
    cases E with
    | prim e =>
      by_cases hK : K = .uint
      · simp only [FloorShape.of, dif_pos hK, FloorShape.isArr, Bool.true_eq_false] at h
      · simp only [FloorShape.of, dif_neg hK]
    | _ => rfl
  | fixed => rfl

/-- An array step reaches a kept shape. -/
theorem FloorShape.follow_arrStep {R : RefTy} {E : Ty} (s : FloorShape K (.ref R)) (ar : ArrTy R E)
    (k : PrimTy.uint.Denote) : s.follow (Path.index (.arr ar) k) = .keep E := by
  cases ar with
  | dyn =>
    rw [Path.index_dyn]
    cases s with
    | keep => rfl
    | arr => rfl
  | fixed =>
    rw [Path.index_fixed]
    cases s with
    | keep => rfl

theorem SRef.follow_at {R : RefTy} {E : Ty} (r : SRef C (.ref R)) (ar : ArrTy R E) (k : PrimTy.uint.Denote) :
    (FloorShape.of K (r.index (.arr ar) k).ty).follow (r.index (.arr ar) k).path = .keep E := by
  show (FloorShape.of K r.ty).follow (r.path.append (Path.index (.arr ar) k)) = _
  rw [FloorShape.follow_append, FloorShape.follow_arrStep]

/-- An array step past a kept shape is kept. -/
theorem SRef.floorRef_at_keep (f : K.Denote → K.Denote) {R : RefTy} {E : Ty} (r : SRef C (.ref R))
    (ar : ArrTy R E) (k : PrimTy.uint.Denote) (hk : (FloorShape.of K r.ty).follow r.path = .keep _) :
    (r.index (.arr ar) k).floorRef K f = (r.floorRef K f).index (.arr ar) k := by
  show (⟨r.root, r.hroot, (FloorShape.of K r.ty).floorPath f (r.path.append (Path.index (.arr ar) k))⟩ :
    SRef C E) = ⟨r.root, r.hroot, ((FloorShape.of K r.ty).floorPath f r.path).append (Path.index (.arr ar) k)⟩
  rw [FloorShape.floorPath_append, hk, FloorShape.floorPath_keep]

/-- An array step where the shape floors the slots: at its floor. -/
theorem SRef.floorRef_at_arr (f : PrimTy.uint.Denote → PrimTy.uint.Denote) {R : RefTy} {E : Ty}
    (r : SRef C (.ref R)) (ar : ArrTy R E) (k : PrimTy.uint.Denote)
    (hk : ((FloorShape.of .uint r.ty).follow r.path).isArr = true) :
    (r.index (.arr ar) k).floorRef .uint f = (r.floorRef .uint f).index (.arr ar) (f k) := by
  show (⟨r.root, r.hroot, (FloorShape.of .uint r.ty).floorPath f (r.path.append (Path.index (.arr ar) k))⟩ :
    SRef C E) = ⟨r.root, r.hroot, ((FloorShape.of .uint r.ty).floorPath f r.path).append (Path.index (.arr ar) (f k))⟩
  rw [FloorShape.floorPath_append]
  generalize (FloorShape.of .uint r.ty).follow r.path = s at hk ⊢
  cases ar with
  | dyn =>
    cases s with
    | keep => simp only [FloorShape.isArr, Bool.false_eq_true] at hk
    | arr hK => rw [Path.index_dyn, Path.index_dyn]; rfl
  | fixed =>
    cases s with
    | keep => simp only [FloorShape.isArr, Bool.false_eq_true] at hk

/-- **A ledger address reads at its floor.** -/
theorem NetRel.eval (ok : OrdK K) {g : State C []} {st' : Storage C} {nt' : Ledger} {Rs : ARoots}
    {f : K.Denote → K.Denote} (hS : Surg ok g st' nt' Rs f) (hn : Rs.net = true) {ks : List Nat}
    {Bs : List Parameter} {Gd : LTm C (.val K) → Prop} {ν μ' μ : AEnv}
    (hGd : ∀ x, Gd x → ∀ v, (x.eval g ν : Option K.Denote) = some v → f v = v)
    (hk : ∀ k ∈ ks, μ.get K k = f (μ'.get K k))
    (hν : ∀ q, q ∉ Bs → q.read μ = q.read ν) {i : LTm C (.val .uint)} {R : Prop}
    (hR : R → i.eval { g with storage := st', net := nt' } μ' = i.eval g μ) (h : NetRel ok ks Bs Gd i R) :
    (i.eval { g with storage := st', net := nt' } μ' : Option PrimTy.uint.Denote).map
        (fun n => (lookupBy n nt').getD 0) =
      (i.eval g μ : Option PrimTy.uint.Denote).map (fun n => (lookupBy n g.net).getD 0) := by
  cases ok with
  | int => exact h.elim
  | uint =>
    have hF : ∀ a, (lookupBy a nt').getD 0 = (lookupBy (f a) g.net).getD 0 := hS.netAt hn
    have hkeys : (i.eval g μ : Option PrimTy.uint.Denote) =
        (i.eval { g with storage := st', net := nt' } μ' : Option PrimTy.uint.Denote).map f := by
      rcases h with ⟨k, hk', rfl⟩ | ⟨hb, hg, hx'⟩
      · show some (μ.get .uint k) = some (f (μ'.get .uint k))
        rw [hk k hk']
      · rw [← hR hx']
        cases he : (i.eval { g with storage := st', net := nt' } μ' : Option PrimTy.uint.Denote) with
        | none => rfl
        | some v =>
          have hv : (i.eval g ν : Option PrimTy.uint.Denote) = some v := by
            rw [← he, hR hx']
            exact (i.eval_agree_parameters g fun q hq => hν q (hb q hq)).symm
          rw [Option.map_some, hGd i hg v hv]
    rw [hkeys]
    cases (i.eval { g with storage := st', net := nt' } μ' : Option PrimTy.uint.Denote) with
    | none => rfl
    | some a => exact congrArg some (hF a)

/-- **The relation**: in the rebuilt storage, at `μ'`, a term reads what it
reads at `μ` in the old one, where `μ` holds the floors of `μ'` at `ks`;
a path of a root of `Rs`, at its floors. -/
theorem ApfTm.eval_trel {Rs : ARoots} (ok : OrdK K) (g : State C []) (st' : Storage C) (nt' : Ledger)
    {f : K.Denote → K.Denote} (hS : Surg ok g st' nt' Rs f) {ks : List Nat}
    {Bs : List Parameter} {Gd : LTm C (.val K) → Prop} {ν μ' μ : AEnv}
    (hGd : ∀ x, Gd x → ∀ v, (x.eval g ν : Option K.Denote) = some v → f v = v)
    (hμ : ∀ q, q ∉ ApfTm.ksP K ks → q.read μ' = q.read μ)
    (hk : ∀ k ∈ ks, μ.get K k = f (μ'.get K k))
    (hν : ∀ q, q ∉ Bs → q.read μ = q.read ν) {b : Bool} {s : Srt} {t : LTm C s} (ht : ApfTm Rs b t)
    (hr : ht.Rel ok ks Bs Gd) :
    TRel f ht.pre b s (t.eval { g with storage := st', net := nt' } μ') (t.eval g μ) := by
  induction ht with
  | @var p k => exact congrArg some (hμ ⟨p, k⟩ hr)
  | lit | env | root | err | zlit => rfl
  | @rroot r T h hr' =>
    refine ⟨?_, fun r' hr' => ?_⟩
    · show some (SRef.ofRoot r h) = some ((SRef.ofRoot r h).floorRef K f)
      show some (⟨r, h, .nil⟩ : SRef C T) = some ⟨r, h, (FloorShape.of K T).floorPath f .nil⟩
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
    cases hq' : (q.eval { g with storage := st', net := nt' } μ' : Option (SRef C _)) with
    | none => exact ⟨rfl, fun _ h => nomatch h⟩
    | some r' =>
      have hk' : (FloorShape.of K r'.ty).follow r'.path = .keep _ := by
        have := hsh r' (by rw [hq']; rfl)
        rw [this]
        split <;> rfl
      refine ⟨?_, fun r'' hr'' => ?_⟩
      · show some ((r'.floorRef K f).field h) = some ((r'.field h).floorRef K f)
        rw [SRef.floorRef_field f r' h hk']
      · obtain rfl : r'.field h = r'' := Option.some.inj hr''
        exact SRef.follow_field r' h hk'
  | index hq hi ihq ihi =>
    apply TRel.of_eq
    rw [LTm.eval_index, LTm.eval_index, (ihq hr.1).of_false, (ihi hr.2).of_false]
  | @rkey K' T q i hq hi ihq ihi =>
    obtain ⟨hx, hsh⟩ := ihq hr.1
    show TRel f hq.pre true _ _ _
    rw [LTm.eval_index, LTm.eval_index, hx]
    cases hq' : (q.eval { g with storage := st', net := nt' } μ' : Option (SRef C _)) with
    | none => exact ⟨rfl, fun _ h => nomatch h⟩
    | some r' =>
      have hshr := hsh r' (by rw [hq']; rfl)
      dsimp only [Option.map_some, Option.bind_some]
      have hr2 := hr.2
      by_cases hK : K' = K
      · subst hK
        rw [dif_pos rfl] at hr2
        rcases hr2 with ⟨hp, hkey⟩ | ⟨hp, hir⟩
        · -- a floored key: at the floor
          rw [hp] at hshr
          have hfol : (FloorShape.of K' r'.ty).follow r'.path = .floor (FloorShape.of K' T) := by
            rw [hshr, if_pos rfl, FloorShape.of_self]
          have hkeys : (i.eval g μ : Option K'.Denote) =
              (i.eval { g with storage := st', net := nt' } μ' : Option K'.Denote).map f := by
            rcases hkey with ⟨k, hk', rfl⟩ | ⟨hb, hg, hx'⟩
            · show some (μ.get K' k) = some (f (μ'.get K' k))
              rw [hk k hk']
            · rw [← (ihi hx').of_false]
              cases he : (i.eval { g with storage := st', net := nt' } μ' : Option K'.Denote) with
              | none => rfl
              | some v =>
                have hv : (i.eval g ν : Option K'.Denote) = some v := by
                  rw [← he, (ihi hx').of_false]
                  exact (i.eval_agree_parameters g fun q hq => hν q (hb q hq)).symm
                rw [Option.map_some, hGd i hg v hv]
          rw [hkeys]
          cases (i.eval { g with storage := st', net := nt' } μ' : Option K'.Denote) with
          | none => exact ⟨rfl, fun _ h => nomatch h⟩
          | some k' =>
            refine ⟨?_, fun r'' hr'' => ?_⟩
            · show some ((r'.floorRef K' f).index .map (f k')) = some ((r'.index .map k').floorRef K' f)
              rw [SRef.floorRef_index, hfol, SRef.index_eq, FloorShape.floorPath_floor_key,
                FloorShape.floorPath_nil]
              rfl
            · obtain rfl : r'.index .map k' = r'' := Option.some.inj hr''
              rw [SRef.follow_index, hfol, hp]
              exact FloorShape.follow_nil _
        · -- after a member: copied
          rw [hp] at hshr
          have hfol : (FloorShape.of K' r'.ty).follow r'.path = .keep _ := hshr
          rw [← (ihi hir).of_false]
          cases (i.eval { g with storage := st', net := nt' } μ' : Option K'.Denote) with
          | none => exact ⟨rfl, fun _ h => nomatch h⟩
          | some k' =>
            refine ⟨?_, fun r'' hr'' => ?_⟩
            · show some ((r'.floorRef K' f).index .map k') = some ((r'.index .map k').floorRef K' f)
              rw [SRef.floorRef_index, hfol, FloorShape.floorPath_keep, SRef.index_eq]
              rfl
            · obtain rfl : r'.index .map k' = r'' := Option.some.inj hr''
              rw [SRef.follow_index, hfol, FloorShape.follow_keep, hp]
              rfl
      · rw [dif_neg hK] at hr2
        rw [← (ihi hr2).of_false]
        cases (i.eval { g with storage := st', net := nt' } μ' : Option K'.Denote) with
        | none => exact ⟨rfl, fun _ h => nomatch h⟩
        | some k' =>
          cases hp : hq.pre with
          | true =>
            rw [hp] at hshr
            have hfol : (FloorShape.of K r'.ty).follow r'.path = .outer K' (FloorShape.of K T) := by
              rw [hshr, if_pos rfl, FloorShape.of_mapping_ne hK]
            refine ⟨?_, fun r'' hr'' => ?_⟩
            · show some ((r'.floorRef K f).index .map k') = some ((r'.index .map k').floorRef K f)
              rw [SRef.floorRef_index, hfol, SRef.index_eq, FloorShape.floorPath_outer_key,
                FloorShape.floorPath_nil]
              rfl
            · obtain rfl : r'.index .map k' = r'' := Option.some.inj hr''
              rw [SRef.follow_index, hfol]
              exact FloorShape.follow_nil _
          | false =>
            rw [hp] at hshr
            have hfol : (FloorShape.of K r'.ty).follow r'.path = .keep _ := hshr
            refine ⟨?_, fun r'' hr'' => ?_⟩
            · show some ((r'.floorRef K f).index .map k') = some ((r'.index .map k').floorRef K f)
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
      exact congrArg some (word_of_get r (hS.other r.hroot (of_decide_eq_false hroot)))
  | @rword p q hq ih =>
    obtain ⟨hx, -⟩ := ih hr
    apply TRel.of_eq
    rw [LTm.eval_obsW, LTm.eval_obsW, hx]
    have hroot := ApfTm.rootsAt { g with storage := st', net := nt' } μ' hq
    cases hq' : (q.eval { g with storage := st', net := nt' } μ' : Option (SRef C (.prim p))) with
    | none => rfl
    | some r =>
      rw [hq'] at hroot
      exact congrArg some (hS.keyAt r (of_decide_eq_true hroot))
  | unop op h ht ih =>
    apply TRel.of_eq
    rw [LTm.eval_app1, LTm.eval_app1, (ih hr).of_false]
    rfl
  | toInt ht ih =>
    apply TRel.of_eq
    rw [LTm.eval_app1, LTm.eval_app1, (ih hr).of_false]
    rfl
  | @net i hi ih =>
    apply TRel.of_eq
    rw [LTm.eval_app1, LTm.eval_app1, Close.Op1.eval_net, Close.Op1.eval_net]
    have hr' : if Rs.net = true then NetRel ok ks Bs Gd i (hi.Rel ok ks Bs Gd) else hi.Rel ok ks Bs Gd := hr
    by_cases hn : Rs.net = true
    · rw [if_pos hn] at hr'
      exact NetRel.eval ok hS hn hGd hk hν (fun h => (ih h).of_false) hr'
    · rw [if_neg hn] at hr'
      rw [(ih hr').of_false, hS.netKeep (by simpa only [Bool.not_eq_true] using hn)]
  | binop op h ha hb iha ihb =>
    apply TRel.of_eq
    rw [LTm.eval_app2, LTm.eval_app2, (iha hr.1).of_false, (ihb hr.2).of_false]
    rfl
  | zbin op h ha hb iha ihb =>
    apply TRel.of_eq
    rw [LTm.eval_app2, LTm.eval_app2, (iha hr.1).of_false, (ihb hr.2).of_false]
    rfl
  | zcmp op h ha hb iha ihb =>
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
  | aidx ar hq hi ihq ihi =>
    apply TRel.of_eq
    rw [LTm.eval_index, LTm.eval_index, (ihq hr.1).of_false, (ihi hr.2).of_false]
  | ite hc ha hb ihc iha ihb =>
    apply TRel.of_eq
    rw [LTm.eval_app3, LTm.eval_app3, (ihc hr.1).of_false, (iha hr.2.1).of_false, (ihb hr.2.2).of_false]
    rfl
  | @has T q hq ih =>
    apply TRel.of_eq
    rw [LTm.eval_obsH, LTm.eval_obsH, (ih hr).of_false]
    have hroot := ApfTm.rootsAt g μ hq
    cases hq' : (q.eval g μ : Option (SRef C T)) with
    | none => rfl
    | some r =>
      rw [hq'] at hroot
      exact congrArg some (has_of_get r (hS.other r.hroot (of_decide_eq_false hroot)))
  | @rhas T q hq ih =>
    obtain ⟨hx, -⟩ := ih hr
    apply TRel.of_eq
    rw [LTm.eval_obsH, LTm.eval_obsH, hx]
    have hroot := ApfTm.rootsAt { g with storage := st', net := nt' } μ' hq
    cases hq' : (q.eval { g with storage := st', net := nt' } μ' : Option (SRef C T)) with
    | none => rfl
    | some r =>
      rw [hq'] at hroot
      exact congrArg some (hS.hasAt r (of_decide_eq_true hroot))
  | @len E q hq ih =>
    apply TRel.of_eq
    rw [LTm.eval_obsL, LTm.eval_obsL, (ih hr).of_false]
    have hroot := ApfTm.rootsAt g μ hq
    cases hq' : (q.eval g μ : Option (SRef C (.ref (.array E)))) with
    | none => rfl
    | some r =>
      rw [hq'] at hroot
      exact congrArg (fun n => some (uintOfNat n)) (len_of_get r (hS.other r.hroot (of_decide_eq_false hroot)))
  | @rlen E q hq ih =>
    obtain ⟨hx, -⟩ := ih hr
    apply TRel.of_eq
    rw [LTm.eval_obsL, LTm.eval_obsL, hx]
    have hroot := ApfTm.rootsAt { g with storage := st', net := nt' } μ' hq
    cases hq' : (q.eval { g with storage := st', net := nt' } μ' : Option (SRef C (.ref (.array E)))) with
    | none => rfl
    | some r =>
      rw [hq'] at hroot
      exact congrArg (fun n => some (uintOfNat n)) (hS.lenAt r (of_decide_eq_true hroot))
  | @rat R E ar q i hq hi ihq ihi =>
    obtain ⟨hx, hsh⟩ := ihq hr.1
    show TRel f false true _ _ _
    rw [LTm.eval_index, LTm.eval_index, hx]
    cases hq' : (q.eval { g with storage := st', net := nt' } μ' : Option (SRef C (.ref R))) with
    | none => exact ⟨rfl, fun _ h => nomatch h⟩
    | some r' =>
      have hshr := hsh r' (by rw [hq']; rfl)
      dsimp only [Option.map_some, Option.bind_some]
      have hr2 := hr.2
      have hkeep : ¬ (PrimTy.uint = K ∧ (hq.pre && (FloorShape.of K (.ref R)).isArr) = true) →
          (FloorShape.of K r'.ty).follow r'.path = .keep _ := by
        intro hn
        rw [hshr]
        cases hp : hq.pre with
        | false => rfl
        | true =>
          rw [if_pos rfl]
          apply FloorShape.of_arr_keep ar
          cases h' : (FloorShape.of K (.ref R)).isArr with
          | false => rfl
          | true => exact absurd ⟨(FloorShape.of_isArr h').symm, by rw [hp, h']; rfl⟩ hn
      by_cases hc : PrimTy.uint = K ∧ (hq.pre && (FloorShape.of K (.ref R)).isArr) = true
      · obtain ⟨hK, hpa⟩ := hc
        subst hK
        rw [dif_pos rfl, if_pos hpa] at hr2
        rw [Bool.and_eq_true] at hpa
        have hfol : ((FloorShape.of .uint r'.ty).follow r'.path).isArr = true := by
          rw [hshr, if_pos hpa.1]; exact hpa.2
        have hkeys : (i.eval g μ : Option PrimTy.uint.Denote) =
            (i.eval { g with storage := st', net := nt' } μ' : Option PrimTy.uint.Denote).map f := by
          rcases hr2 with ⟨k, hk', he⟩ | ⟨hb, hg, hx'⟩
          · rw [castKey_rfl] at he
            subst he
            show some (μ.get .uint k) = some (f (μ'.get .uint k))
            rw [hk k hk']
          · rw [castKey_rfl] at hg
            rw [← (ihi hx').of_false]
            cases he : (i.eval { g with storage := st', net := nt' } μ' : Option PrimTy.uint.Denote) with
            | none => rfl
            | some v =>
              have hv : (i.eval g ν : Option PrimTy.uint.Denote) = some v := by
                rw [← he, (ihi hx').of_false]
                exact (i.eval_agree_parameters g fun q hq => hν q (hb q hq)).symm
              rw [Option.map_some, hGd i hg v hv]
        rw [hkeys]
        cases (i.eval { g with storage := st', net := nt' } μ' : Option PrimTy.uint.Denote) with
        | none => exact ⟨rfl, fun _ h => nomatch h⟩
        | some k' =>
          refine ⟨?_, fun r'' hr'' => ?_⟩
          · show some ((r'.floorRef .uint f).index (.arr ar) (f k')) =
              some ((r'.index (.arr ar) k').floorRef .uint f)
            rw [SRef.floorRef_at_arr f r' ar k' hfol]
          · obtain rfl : r'.index (.arr ar) k' = r'' := Option.some.inj hr''
            exact SRef.follow_at r' ar k'
      · have hk0 := hkeep hc
        have hir : hi.Rel ok ks Bs Gd := by
          by_cases hK : PrimTy.uint = K
          · rw [dif_pos hK, if_neg (fun h => hc ⟨hK, h⟩)] at hr2
            exact hr2
          · rw [dif_neg hK] at hr2
            exact hr2
        rw [← (ihi hir).of_false]
        cases (i.eval { g with storage := st', net := nt' } μ' : Option PrimTy.uint.Denote) with
        | none => exact ⟨rfl, fun _ h => nomatch h⟩
        | some k' =>
          refine ⟨?_, fun r'' hr'' => ?_⟩
          · show some ((r'.floorRef K f).index (.arr ar) k') = some ((r'.index (.arr ar) k').floorRef K f)
            rw [SRef.floorRef_at_keep f r' ar k' hk0]
          · obtain rfl : r'.index (.arr ar) k' = r'' := Option.some.inj hr''
            exact SRef.follow_at r' ar k'

/-- **A term reads alike** in the rebuilt storage at `μ'` and the old one at
`μ`. -/
theorem ApfTm.eval_rel {Rs : ARoots} (ok : OrdK K) (g : State C []) (st' : Storage C) (nt' : Ledger)
    {f : K.Denote → K.Denote} (hS : Surg ok g st' nt' Rs f) {ks : List Nat}
    {Bs : List Parameter} {Gd : LTm C (.val K) → Prop} {ν μ' μ : AEnv}
    (hGd : ∀ x, Gd x → ∀ v, (x.eval g ν : Option K.Denote) = some v → f v = v)
    (hμ : ∀ q, q ∉ ApfTm.ksP K ks → q.read μ' = q.read μ)
    (hk : ∀ k ∈ ks, μ.get K k = f (μ'.get K k))
    (hν : ∀ q, q ∉ Bs → q.read μ = q.read ν) {s : Srt} {t : LTm C s} (ht : ApfTm Rs false t)
    (hr : ht.Rel ok ks Bs Gd) : t.eval { g with storage := st', net := nt' } μ' = t.eval g μ :=
  (ApfTm.eval_trel ok g st' nt' hS hGd hμ hk hν ht hr).of_false

/-! ## Guards: true at a key, true at its floor -/

/-- How an operand's value relates to its value at the floor: a block
variable's is its floor (`lastIn`); a ground operand's is the same, in the
index set with its successor, and among the strict guards' operands. -/
def FRel (S : ApfSet) (v : Bool) (x' x : Int) : Prop :=
  if v then x = lastIn S x'
  else x = x' ∧ x ∈ S ∧ x ∈ S.strict ∧ (x + 1 < S.hi → x + 1 ∈ S)

theorem le_mono (S : ApfSet) {vx vy : Bool} {x' y' x y : Int} (h0 : S.lo ≤ x') (h0' : S.lo ≤ y')
    (hx : FRel S vx x' x) (hy : FRel S vy y' y) (h : x' ≤ y') : x ≤ y := by
  unfold FRel at hx hy
  cases vx <;> cases vy <;> simp only [Bool.false_eq_true, if_false, if_true] at hx hy
  · omega
  · obtain ⟨rfl, hm, -⟩ := hx; rw [hy]; exact lastIn_ge S y' hm h
  · obtain ⟨rfl, hm, -⟩ := hy; rw [hx]; exact lastIn_le S h0 hm h
  · rw [hx, hy]; exact lastIn_mono S h0 h

theorem lt_mono (S : ApfSet) {vx vy : Bool} {x' y' x y : Int} (h0 : S.lo ≤ x')
    (hb : y' < S.hi) (hx : FRel S vx x' x) (hy : FRel S vy y' y)
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

theorem eq_mono (S : ApfSet) {vx vy : Bool} {x' y' x y : Int} (h0 : S.lo ≤ x')
    (hx : FRel S vx x' x) (hy : FRel S vy y' y) (h : x' = y') : x = y := by
  subst h
  unfold FRel at hx hy
  cases vx <;> cases vy <;> simp only [Bool.false_eq_true, if_false, if_true] at hx hy
  · omega
  · obtain ⟨rfl, hm, -⟩ := hx; rw [hy, lastIn_fix S hm h0]
  · obtain ⟨rfl, hm, -⟩ := hy; rw [hx, lastIn_fix S hm h0]
  · rw [hx, hy]

/-- **A comparison true of the values is true of their floors.** -/
theorem cmp_mono (S : ApfSet) (op : BinOp) {vx vy : Bool} {x' y' x y : Int} (h0 : S.lo ≤ x') (h0' : S.lo ≤ y')
    (hb : x' < S.hi) (hb' : y' < S.hi)
    (hx : FRel S vx x' x) (hy : FRel S vy y' y) (hs : op.isStrict = true → (vx && vy) = false)
    (h : cmpOf op x' y' = true) : cmpOf op x y = true := by
  cases op <;> simp only [cmpOf, decide_eq_true_eq, Bool.false_eq_true] at h ⊢
  · exact lt_mono S h0 hb' hx hy (hs rfl) h
  · exact lt_mono S h0' hb hy hx (by rw [Bool.and_comm]; exact hs rfl) h
  · exact le_mono S h0 h0' hx hy h
  · exact le_mono S h0' h0 hy hx h
  · exact eq_mono S h0 hx hy h

/-- The values in the index set. -/
def InS (ok : OrdK K) (S : List Int) (g : State C []) (ν : AEnv) (x : LTm C (.val K)) : Prop :=
  ∀ v, (x.eval g ν : Option K.Denote) = some v → ok.val v ∈ S

/-- Their successors in the index set, where they are values. -/
def InSucc (ok : OrdK K) (S : List Int) (g : State C []) (ν : AEnv) (x : LTm C (.val K)) : Prop :=
  ∀ v, (x.eval g ν : Option K.Denote) = some v → ok.val v + 1 < ok.hi → ok.val v + 1 ∈ S

/-- A variable of `ks`. -/
def LTm.isBVar (ks : List Nat) : {s : Srt} → LTm C s → Bool
  | _, .var k => decide (k ∈ ks)
  | _, _ => false

theorem LTm.isBVar_spec {ks : List Nat} {x : LTm C (.val K)} (h : x.isBVar ks = true) :
    ∃ k ∈ ks, x = .var k := by
  cases x with
  | var k => exact ⟨k, by simpa only [LTm.isBVar, decide_eq_true_eq] using h, rfl⟩
  | _ => simp only [LTm.isBVar, Bool.false_eq_true] at h

/-- **An operand of a guard comparison**: a block variable, or a ground
term of the index set (`Gd`) whose successor is in it too (`Lo`); it may
halt (`k < x - 1`). -/
inductive IdxP {Rs : ARoots} (ok : OrdK K) (Gd Lo : LTm C (.val K) → Prop) (ks : List Nat)
    (Bs : List Parameter) : Bool → {a : LTm C (.val K)} → ApfTm Rs false a → Prop where
  | var (k : Nat) (hk : k ∈ ks) (hv : ApfTm Rs false (LTm.var (p := K) k)) : IdxP ok Gd Lo ks Bs true hv
  | gnd {a : LTm C (.val K)} (ha : ApfTm Rs false a) (hr : ha.Rel ok ks Bs Gd)
      (hb : ∀ q ∈ a.parameters, q ∉ Bs) (hs : Gd a) (hl : Lo a) :
      IdxP ok Gd Lo ks Bs false ha

/-- **A guard**: `&&` and `||` of comparisons of operands (`IdxP`), never a
strict one of two block variables.  `tot` where it returns wherever its
atoms do (its operands block variables or total); `ds` where it returns
at the floors wherever it returned at the keys, as the left operand of
every `||` must: a comparison does, a `&&` where its left operand does and
its right one is total (a `&&` that skipped a halting right operand at the
keys may evaluate it at the floors), a `||` where its right one is total. -/
inductive GuardP {Rs : ARoots} (ok : OrdK K) (Gd Lo : LTm C (.val K) → Prop) (ks : List Nat)
    (Bs : List Parameter) : Bool → Bool → {p : PrimTy} → {t : LTm C (.val p)} → ApfTm Rs false t → Prop where
  | and (h : BinOp.and.accepts .bool = true) {ta da tb db : Bool} {a b : LTm C (.val .bool)}
      {ha : ApfTm Rs false a} {hb : ApfTm Rs false b} :
      GuardP ok Gd Lo ks Bs ta da ha → GuardP ok Gd Lo ks Bs tb db hb →
      GuardP ok Gd Lo ks Bs (ta && tb) (da && tb) (.binop .and h ha hb)
  | or (h : BinOp.or.accepts .bool = true) {ta tb db : Bool} {a b : LTm C (.val .bool)}
      {ha : ApfTm Rs false a} {hb : ApfTm Rs false b} :
      GuardP ok Gd Lo ks Bs ta true ha → GuardP ok Gd Lo ks Bs tb db hb →
      GuardP ok Gd Lo ks Bs (ta && tb) tb (.binop .or h ha hb)
  | cmp (op : BinOp) (h : op.accepts K = true) (hop : op.isGuardOp = true) {va vb : Bool}
      {a b : LTm C (.val K)} {ha : ApfTm Rs false a} {hb : ApfTm Rs false b} {tot : Bool} :
      IdxP ok Gd Lo ks Bs va ha → IdxP ok Gd Lo ks Bs vb hb → (op.isStrict = true → (va && vb) = false) →
      (tot = true → (a.isBVar ks || a.totalB) = true ∧ (b.isBVar ks || b.totalB) = true) →
      GuardP ok Gd Lo ks Bs tot true (.binop op h ha hb)

/-- The setting of a rebuilt storage: `μ'` reads the keys, `μ` their
floors; both are `ν` off the binders; the terms `Gd` and their successors
`Lo` are in the index set at `ν`, which ranges over the key type. -/
structure Setting (ok : OrdK K) (g : State C []) (st' : Storage C) (nt' : Ledger) (Rs : ARoots) (S : ApfSet)
    (Gd Lo : LTm C (.val K) → Prop) (ks : List Nat) (Bs : List Parameter) (ν μ' μ : AEnv) : Prop where
  lo : S.lo = ok.lo
  hi : S.hi = ok.hi
  surg : Surg ok g st' nt' Rs (lastK ok S)
  gdS : ∀ x, Gd x → InS ok S.vals g ν x
  loS : ∀ x, Lo x → InSucc ok S.vals g ν x
  loT : ∀ x, Lo x → InS ok S.strict g ν x
  hμ : ∀ q, q ∉ ApfTm.ksP K ks → q.read μ' = q.read μ
  hk : ∀ k ∈ ks, μ.get K k = lastK ok S (μ'.get K k)
  hν : ∀ q, q ∉ Bs → q.read μ = q.read ν

section Setting

variable {ok : OrdK K} {g : State C []} {st' : Storage C} {nt' : Ledger} {Rs : ARoots} {S : ApfSet}
  {Gd Lo : LTm C (.val K) → Prop} {ks : List Nat} {Bs : List Parameter} {ν μ' μ : AEnv}

theorem Setting.gd (hs : Setting ok g st' nt' Rs S Gd Lo ks Bs ν μ' μ) :
    ∀ x, Gd x → ∀ v, (x.eval g ν : Option K.Denote) = some v → lastK ok S v = v := fun _ hx v hv =>
  ok.ext (by
    rw [lastK_val ok S hs.lo hs.hi]
    exact lastIn_fix S (hs.gdS _ hx v hv) (by rw [hs.lo]; exact (ok.bounds v).1))

theorem Setting.eval (hs : Setting ok g st' nt' Rs S Gd Lo ks Bs ν μ' μ) {s : Srt}
    {t : LTm C s} (ht : ApfTm Rs false t) (hr : ht.Rel ok ks Bs Gd) :
    t.eval { g with storage := st', net := nt' } μ' = t.eval g μ :=
  ApfTm.eval_rel ok g st' nt' hs.surg hs.gd hs.hμ hs.hk hs.hν ht hr

theorem IdxP.values (hs : Setting ok g st' nt' Rs S Gd Lo ks Bs ν μ' μ) {v : Bool}
    {a : LTm C (.val K)} {ha : ApfTm Rs false a} (hi : IdxP ok Gd Lo ks Bs v ha) {x' : K.Denote}
    (hx' : (a.eval { g with storage := st', net := nt' } μ' : Option _) = some x') :
    ∃ x : K.Denote, (a.eval g μ : Option _) = some x ∧ FRel S v (ok.val x') (ok.val x) := by
  cases hi with
  | var k hk _ =>
    obtain rfl : μ'.get K k = x' := Option.some.inj hx'
    refine ⟨μ.get K k, rfl, ?_⟩
    show ok.val (μ.get K k) = lastIn S (ok.val (μ'.get K k))
    rw [hs.hk k hk, lastK_val ok S hs.lo hs.hi]
  | gnd ha hr hb hsS hl =>
    have hx : (a.eval g μ : Option K.Denote) = some x' := (hs.eval ha hr).symm.trans hx'
    have hxν : (a.eval g ν : Option K.Denote) = some x' := by
      rw [← hx]; exact (a.eval_agree_parameters g fun q hq => hs.hν q (hb q hq)).symm
    exact ⟨x', hx, rfl, hs.gdS _ hsS x' hxν, hs.loT _ hl x' hxν, fun h => hs.loS _ hl x' hxν (by
      rw [← hs.hi]; exact h)⟩

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

theorem eval_of_tot (g : State C []) (ν : AEnv) {ks : List Nat} {a : LTm C (.val K)}
    (h : (a.isBVar ks || a.totalB) = true) : ∃ x, (a.eval g ν : Option K.Denote) = some x := by
  rcases Bool.or_eq_true _ _ ▸ h with h | h
  · obtain ⟨k, _, rfl⟩ := LTm.isBVar_spec h
    exact ⟨_, rfl⟩
  · exact Option.isSome_iff_exists.1 (LTm.totalB_eval g ν a h)

/-- **A total guard returns.** -/
theorem GuardP.defined {Rs : ARoots} {ok : OrdK K} {Gd Lo : LTm C (.val K) → Prop} {ks : List Nat}
    {Bs : List Parameter} (g : State C []) (μ : AEnv) {tot ds : Bool} {p : PrimTy}
    {t : LTm C (.val p)} {ht : ApfTm Rs false t} (hg : GuardP ok Gd Lo ks Bs tot ds ht) :
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
    obtain ⟨c, e, -⟩ := ok.cmp_some op h hop x y
    exact ⟨c, by rw [LTm.eval_app2, Close.Op2.eval_binop, hx, Option.bind_some, hy]; exact e⟩

/-- **A guard at the keys and at their floors**: true at the keys, true at
the floors; where `ds`, returning at the keys, returning at the floors. -/
theorem GuardP.floors {ok : OrdK K} {g : State C []} {st' : Storage C} {nt' : Ledger} {Rs : ARoots}
    {S : ApfSet} {Gd Lo : LTm C (.val K) → Prop} {ks : List Nat} {Bs : List Parameter} {ν μ' μ : AEnv}
    (hs : Setting ok g st' nt' Rs S Gd Lo ks Bs ν μ' μ) {tot ds : Bool} {p : PrimTy}
    {t : LTm C (.val p)} {ht : ApfTm Rs false t} (hg : GuardP ok Gd Lo ks Bs tot ds ht) :
    (∀ x' : p.Denote, (t.eval { g with storage := st', net := nt' } μ' : Option _) = some x' → IsTrue p x' →
      ∃ x : p.Denote, (t.eval g μ : Option _) = some x ∧ IsTrue p x) ∧
    (ds = true → ∀ x' : p.Denote, (t.eval { g with storage := st', net := nt' } μ' : Option _) = some x' →
      ∃ x : p.Denote, (t.eval g μ : Option _) = some x) := by
  induction hg with
  | @and h ta da tb db a b ha hb _ hgb iha ihb =>
    refine ⟨fun c' hc' htc => ?_, fun hds c' hc' => ?_⟩
    · have htc' : c' = true := htc
      subst htc'
      rw [LTm.eval_app2, Close.Op2.eval_binop] at hc'
      cases hxa : (a.eval { g with storage := st', net := nt' } μ' : Option Bool) with
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
      cases hxa : (a.eval { g with storage := st', net := nt' } μ' : Option Bool) with
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
      cases hxa : (a.eval { g with storage := st', net := nt' } μ' : Option Bool) with
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
      cases hxa : (a.eval { g with storage := st', net := nt' } μ' : Option Bool) with
      | none => rw [hxa] at hc'; cases hc'
      | some a' =>
        obtain ⟨a0, ha0⟩ := iha.2 rfl a' hxa
        obtain ⟨b0, hb0⟩ := GuardP.defined g μ hgb hds
        exact ⟨a0 || b0, by rw [LTm.eval_app2, Close.Op2.eval_binop, ha0, Option.bind_some, hb0]; exact binopT_orB h a0 b0⟩
  | @cmp op h hop va vb a b ha hb tot ia ib hst _ =>
    have key : ∀ c', (LTm.eval { g with storage := st', net := nt' } μ' (.app2 (.binop op h) a b) : Option _) =
        some c' → ∃ c2, (LTm.eval g μ (.app2 (.binop op h) a b) : Option _) = some c2 ∧
          (IsTrue (op.ret K) c' → IsTrue (op.ret K) c2) := by
      intro c' hc'
      rw [LTm.eval_app2, Close.Op2.eval_binop] at hc'
      cases hxa : (a.eval { g with storage := st', net := nt' } μ' : Option K.Denote) with
      | none => rw [hxa] at hc'; cases hc'
      | some x' =>
        rw [hxa, Option.bind_some] at hc'
        cases hyb : (b.eval { g with storage := st', net := nt' } μ' : Option K.Denote) with
        | none => rw [hyb, ok.cmp_none op h hop] at hc'; cases hc'
        | some y' =>
          rw [hyb] at hc'
          obtain ⟨c1, e1, i1⟩ := ok.cmp_some op h hop x' y'
          rw [e1] at hc'
          cases hc'
          obtain ⟨x, hx, hfx⟩ := ia.values hs hxa
          obtain ⟨y, hy, hfy⟩ := ib.values hs hyb
          obtain ⟨c2, e2, i2⟩ := ok.cmp_some op h hop x y
          have bx := ok.bounds x'
          have bY := ok.bounds y'
          rw [← hs.lo, ← hs.hi] at bx bY
          refine ⟨c2, ?_, fun htc => i2.2 (cmp_mono S op bx.1 bY.1 bx.2 bY.2 hfx hfy hst (i1.1 htc))⟩
          rw [LTm.eval_app2, Close.Op2.eval_binop, hx, Option.bind_some, hy]
          exact e2
    exact ⟨fun c' hc' htc => (key c' hc').imp fun _ h => ⟨h.1, h.2 htc⟩,
      fun _ c' hc' => (key c' hc').imp fun _ h => h.1⟩

/-- **A guard true at the keys is true at their floors.** -/
theorem GuardP.mono {ok : OrdK K} {g : State C []} {st' : Storage C} {nt' : Ledger} {Rs : ARoots}
    {S : ApfSet} {Gd Lo : LTm C (.val K) → Prop} {ks : List Nat} {Bs : List Parameter} {ν μ' μ : AEnv}
    (hs : Setting ok g st' nt' Rs S Gd Lo ks Bs ν μ' μ) {tot ds : Bool} {p : PrimTy}
    {t : LTm C (.val p)} {ht : ApfTm Rs false t} (hg : GuardP ok Gd Lo ks Bs tot ds ht) :
    ∀ x' : p.Denote, (t.eval { g with storage := st', net := nt' } μ' : Option _) = some x' → IsTrue p x' →
      ∃ x : p.Denote, (t.eval g μ : Option _) = some x ∧ IsTrue p x :=
  (GuardP.floors hs hg).1

/-! ## Instances -/

/-- The position `j` at `p`, the position `k` at `K` replaced by `u`. -/
def LTm.substVar (k : Nat) (u : LTm C (.val K)) (p : PrimTy) (j : Nat) : LTm C (.val p) :=
  if h : K = p ∧ j = k then h.1 ▸ u else .var j

/-- `t[u/k]`: the position `k` at `K` replaced by `u`. -/
def LTm.subst1 (k : Nat) (u : LTm C (.val K)) : {s : Srt} → LTm C s → LTm C s
  | _, @LTm.var _ p j => LTm.substVar k u p j
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

theorem AEnv.get_set_ty (ν : AEnv) (K p : PrimTy) {k j : Nat} (v : K.Denote)
    (h : ¬ (K = p ∧ j = k)) : (ν.set K k v).get p j = ν.get p j := by
  cases K <;> cases p <;> simp only [AEnv.set, AEnv.get] <;>
    first | rfl | (rw [if_neg (fun e => h ⟨rfl, e⟩)])

/-- **Substitution is evaluation at the value.** -/
theorem LTm.eval_subst1 (g : State C []) (ν : AEnv) (k : Nat) (u : LTm C (.val K))
    {v : K.Denote} (hu : (u.eval g ν : Option K.Denote) = some v) {s : Srt}
    (t : LTm C s) : (LTm.subst1 k u t).eval g ν = t.eval g (ν.set K k v) := by
  induction t with
  | @var p j =>
    show ((LTm.substVar k u p j).eval g ν : Option _) = some ((ν.set K k v).get p j)
    unfold LTm.substVar
    by_cases hj : K = p ∧ j = k
    · obtain ⟨rfl, rfl⟩ := hj
      rw [dif_pos ⟨rfl, rfl⟩, AEnv.get_set_self]
      exact hu
    · rw [dif_neg hj, AEnv.get_set_ty ν K p v hj]; rfl
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
def LFml.subst1 (k : Nat) (u : LTm C (.val K)) : LFml C → LFml C
  | .tt => .tt
  | .eq a b => .eq (LTm.subst1 k u a) (LTm.subst1 k u b)
  | .not φ => .not (φ.subst1 k u)
  | .and φ ψ => .and (φ.subst1 k u) (ψ.subst1 k u)
  | .imp φ ψ => .imp (φ.subst1 k u) (ψ.subst1 k u)
  | .all j p φ => .all j p φ

theorem LFml.qfB_subst1 (k : Nat) (u : LTm C (.val K)) : ∀ φ : LFml C, φ.qfB = true → (φ.subst1 k u).qfB = true
  | .tt, _ | .eq _ _, _ => rfl
  | .not φ, h => LFml.qfB_subst1 k u φ h
  | .and φ ψ, h | .imp φ ψ, h => by
    simp only [LFml.qfB, Bool.and_eq_true] at h
    simp only [LFml.subst1, LFml.qfB, LFml.qfB_subst1 k u φ h.1, LFml.qfB_subst1 k u ψ h.2, Bool.and_self]

theorem LFml.holds_subst1 (g : State C []) (ν : AEnv) (k : Nat) (u : LTm C (.val K))
    {v : K.Denote} (hu : (u.eval g ν : Option K.Denote) = some v) :
    ∀ φ : LFml C, φ.qfB = true → ((φ.subst1 k u).holds g ν ↔ φ.holds g (ν.set K k v))
  | .tt, _ => Iff.rfl
  | .eq a b, _ => by simp only [LFml.subst1, LFml.holds, LTm.eval_subst1 g ν k u hu]
  | .not φ, h => not_congr (LFml.holds_subst1 g ν k u hu φ h)
  | .and φ ψ, h => by
    simp only [LFml.qfB, Bool.and_eq_true] at h
    exact and_congr (LFml.holds_subst1 g ν k u hu φ h.1) (LFml.holds_subst1 g ν k u hu ψ h.2)
  | .imp φ ψ, h => by
    simp only [LFml.qfB, Bool.and_eq_true] at h
    exact imp_congr (LFml.holds_subst1 g ν k u hu φ h.1) (LFml.holds_subst1 g ν k u hu ψ h.2)

/-- A chain of binders of `K` over a quantifier-free body. -/
def LFml.chainQF (K : PrimTy) : LFml C → Bool
  | .all _ p φ => decide (p = K) && φ.chainQF K
  | φ => φ.qfB

/-- The chain's variables. -/
def LFml.chainVars (K : PrimTy) : LFml C → List Nat
  | .all k p φ => if p = K then k :: φ.chainVars K else []
  | _ => []

/-- The chain's body. -/
def LFml.chainBody (K : PrimTy) : LFml C → LFml C
  | .all k p φ => if p = K then φ.chainBody K else .all k p φ
  | φ => φ

/-- **The block's instances at `us`**: one per tuple, each guarded by its
terms returning. -/
def LFml.inst (us : List (LTm C (.val K))) : LFml C → LFml C
  | .all k p φ =>
    if p = K then LFml.conj (us.map fun u => .imp (.eq u u) ((φ.inst us).subst1 k u)) else .all k p φ
  | φ => φ

theorem LFml.chainQF_all {k : Nat} {p : PrimTy} {φ : LFml C} (h : (LFml.all k p φ).chainQF K = true) :
    p = K ∧ φ.chainQF K = true := by
  simpa only [LFml.chainQF, Bool.and_eq_true, decide_eq_true_eq] using h

theorem LFml.chainVars_all (k : Nat) (φ : LFml C) : (LFml.all k K φ).chainVars K = k :: φ.chainVars K := by
  rw [LFml.chainVars, if_pos rfl]

theorem LFml.chainBody_all (k : Nat) (φ : LFml C) : (LFml.all k K φ).chainBody K = φ.chainBody K := by
  rw [LFml.chainBody, if_pos rfl]

theorem LFml.inst_all (us : List (LTm C (.val K))) (k : Nat) (φ : LFml C) :
    (LFml.all k K φ).inst us = LFml.conj (us.map fun u => .imp (.eq u u) ((φ.inst us).subst1 k u)) := by
  rw [LFml.inst, if_pos rfl]

theorem LFml.qfB_conj : ∀ ds : List (LFml C), (∀ d ∈ ds, d.qfB = true) → (LFml.conj ds).qfB = true
  | [], _ => rfl
  | [d], h => h d List.mem_cons_self
  | d :: e :: ds, h => by
    show (d.qfB && (LFml.conj (e :: ds)).qfB) = true
    rw [h d List.mem_cons_self, LFml.qfB_conj (e :: ds) fun d' hd' => h d' (List.mem_cons_of_mem _ hd')]
    rfl

theorem LFml.qfB_inst (us : List (LTm C (.val K))) : ∀ φ : LFml C, φ.chainQF K = true → (φ.inst us).qfB = true
  | .all k p φ, h => by
    obtain ⟨hp, hc⟩ := LFml.chainQF_all h
    clear h
    subst p
    rw [LFml.inst_all]
    exact LFml.qfB_conj _ fun d hd => by
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 hd
      show (true && ((φ.inst us).subst1 k u).qfB) = true
      rw [LFml.qfB_subst1 k u _ (LFml.qfB_inst us φ hc)]
      rfl
  | .tt, h | .eq _ _, h | .not _, h | .and _ _, h | .imp _ _, h => h

/-- **The block implies its instances.** -/
theorem LFml.inst_sound (g : State C []) (us : List (LTm C (.val K))) :
    ∀ (φ : LFml C) (ν : AEnv), φ.chainQF K = true → φ.holds g ν → (φ.inst us).holds g ν
  | .all k p φ, ν, hc, h => by
    obtain ⟨hp, hc'⟩ := LFml.chainQF_all hc
    subst p
    rw [LFml.inst_all]
    show (LFml.conj _).holds g ν
    rw [LFml.holds_conj]
    intro d hd
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hd
    intro hu
    obtain ⟨v, hv, -⟩ := (LFml.holds_eq_iff g ν u u).1 hu
    rw [LFml.holds_subst1 g ν k u hv _ (LFml.qfB_inst us φ hc')]
    exact LFml.inst_sound g us φ _ hc' (h v)
  | .tt, _, _, h | .eq _ _, _, _, h | .not _, _, _, h | .and _ _, _, _, h | .imp _ _, _, _, h => h

/-! ## Blocks, instantiated at their polarity -/

/-- The root a path of keys and members starts at. -/
def LTm.pathRoot? : {s : Srt} → LTm C s → Option Name
  | _, .app0 (.root r _) => some r
  | _, .index _ q _ => q.pathRoot?
  | _, .app1 (.field _) q => q.pathRoot?
  | _, _ => none

/-- The term reads a root of `Rs` at a variable of `ks` as a key of type
`K` of a path, or the ledger at one (`Rs.net`, at `uint`). -/
def LTm.readsAtVar (K : PrimTy) (Rs : ARoots) (ks : List Nat) : {s : Srt} → LTm C s → Bool
  | _, .index (k := K') _ q (.var j) =>
    (decide (K' = K) && q.pathRoot?.any (· ∈ Rs.names) && decide (j ∈ ks)) || q.readsAtVar K Rs ks
  | _, .app1 .net (.var j) => decide (K = .uint) && Rs.net && decide (j ∈ ks)
  | _, .app1 _ a | _, .obsW a | _, .obsL a | _, .obsH a => a.readsAtVar K Rs ks
  | _, .app2 _ a b | _, .index _ a b | _, .seq a b | _, .orElse a b => a.readsAtVar K Rs ks || b.readsAtVar K Rs ks
  | _, .app3 _ a b c => a.readsAtVar K Rs ks || b.readsAtVar K Rs ks || c.readsAtVar K Rs ks
  | _, .kite a b t e =>
    a.readsAtVar K Rs ks || b.readsAtVar K Rs ks || t.readsAtVar K Rs ks || e.readsAtVar K Rs ks
  | _, _ => false

/-- The roots the term reads at a variable of `ks`, as a key of type `K`. -/
def LTm.rootsAtVar (K : PrimTy) (ks : List Nat) : {s : Srt} → LTm C s → List Name
  | _, .index (k := K') _ q (.var j) =>
    (if K' = K ∧ j ∈ ks then q.pathRoot?.toList else []) ++ q.rootsAtVar K ks
  | _, .app1 _ a | _, .obsW a | _, .obsL a | _, .obsH a => a.rootsAtVar K ks
  | _, .app2 _ a b | _, .index _ a b | _, .seq a b | _, .orElse a b => a.rootsAtVar K ks ++ b.rootsAtVar K ks
  | _, .app3 _ a b c => a.rootsAtVar K ks ++ b.rootsAtVar K ks ++ c.rootsAtVar K ks
  | _, .kite a b t e => a.rootsAtVar K ks ++ b.rootsAtVar K ks ++ t.rootsAtVar K ks ++ e.rootsAtVar K ks
  | _, _ => []

/-- The term reads the ledger at a variable of `ks`. -/
def LTm.netAtVar (ks : List Nat) : {s : Srt} → LTm C s → Bool
  | _, .app1 .net (.var j) => decide (j ∈ ks)
  | _, .app1 _ a | _, .obsW a | _, .obsL a | _, .obsH a => a.netAtVar ks
  | _, .app2 _ a b | _, .index _ a b | _, .seq a b | _, .orElse a b => a.netAtVar ks || b.netAtVar ks
  | _, .app3 _ a b c => a.netAtVar ks || b.netAtVar ks || c.netAtVar ks
  | _, .kite a b t e => a.netAtVar ks || b.netAtVar ks || t.netAtVar ks || e.netAtVar ks
  | _, _ => false

def LFml.readsAtVar (K : PrimTy) (Rs : ARoots) (ks : List Nat) : LFml C → Bool
  | .tt => false
  | .eq a b => a.readsAtVar K Rs ks || b.readsAtVar K Rs ks
  | .not φ | .all _ _ φ => φ.readsAtVar K Rs ks
  | .and φ ψ | .imp φ ψ => φ.readsAtVar K Rs ks || ψ.readsAtVar K Rs ks

def LFml.rootsAtVar (K : PrimTy) (ks : List Nat) : LFml C → List Name
  | .tt => []
  | .eq a b => a.rootsAtVar K ks ++ b.rootsAtVar K ks
  | .not φ | .all _ _ φ => φ.rootsAtVar K ks
  | .and φ ψ | .imp φ ψ => φ.rootsAtVar K ks ++ ψ.rootsAtVar K ks

def LFml.netAtVar (ks : List Nat) : LFml C → Bool
  | .tt => false
  | .eq a b => a.netAtVar ks || b.netAtVar ks
  | .not φ | .all _ _ φ => φ.netAtVar ks
  | .and φ ψ | .imp φ ψ => φ.netAtVar ks || ψ.netAtVar ks

/-- **A block of the fragment's shape**: binders of `K` over a
quantifier-free body reading a root of `Rs`, or the ledger, at one of them. -/
def LFml.isBlock (K : PrimTy) (Rs : ARoots) (φ : LFml C) : Bool :=
  φ.chainQF K && !(φ.chainVars K).isEmpty && (φ.chainBody K).readsAtVar K Rs (φ.chainVars K)

/-- The roots the negative chains of `K` outside binders read at their
variables. -/
def LFml.blockRoots (K : PrimTy) : Bool → LFml C → List Name
  | pol, .not φ => φ.blockRoots K (!pol)
  | pol, .and φ ψ => φ.blockRoots K pol ++ ψ.blockRoots K pol
  | pol, .imp φ ψ => φ.blockRoots K (!pol) ++ ψ.blockRoots K pol
  | pol, .all k p φ =>
    if !pol && (LFml.all k p φ).chainQF K then
      ((LFml.all k p φ).chainBody K).rootsAtVar K ((LFml.all k p φ).chainVars K)
    else []
  | _, _ => []

/-- Whether the negative chains of `K` outside binders read the ledger at
their variables. -/
def LFml.blockNet (K : PrimTy) : Bool → LFml C → Bool
  | pol, .not φ => φ.blockNet K (!pol)
  | pol, .and φ ψ => φ.blockNet K pol || ψ.blockNet K pol
  | pol, .imp φ ψ => φ.blockNet K (!pol) || ψ.blockNet K pol
  | pol, .all k p φ =>
    !pol && (LFml.all k p φ).chainQF K && ((LFml.all k p φ).chainBody K).netAtVar ((LFml.all k p φ).chainVars K)
  | _, _ => false

/-- **The body, each negative block replaced by its instances at `us`.** -/
def LFml.apfInst (Rs : ARoots) (us : List (LTm C (.val K))) : Bool → LFml C → LFml C
  | pol, .not φ => .not (φ.apfInst Rs us (!pol))
  | pol, .and φ ψ => .and (φ.apfInst Rs us pol) (ψ.apfInst Rs us pol)
  | pol, .imp φ ψ => .imp (φ.apfInst Rs us (!pol)) (ψ.apfInst Rs us pol)
  | pol, .all k p φ =>
    if !pol && (LFml.all k p φ).isBlock K Rs then (LFml.all k p φ).inst us else .all k p φ
  | _, φ => φ

/-- **Instantiation is sound**: at a positive polarity the instantiated
formula implies the formula, at a negative one the converse. -/
theorem LFml.apfInst_sound (g : State C []) (Rs : ARoots) (us : List (LTm C (.val K))) :
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
      show LFml.holds g ν (if (!false && (LFml.all k p φ).isBlock K Rs) = true then
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
inductive ApfFml (Rs : ARoots) : LFml C → Type where
  | tt : ApfFml Rs .tt
  | eq {p : PrimTy} {a b : LTm C (.val p)} (ha : ApfTm Rs false a) (hb : ApfTm Rs false b) : ApfFml Rs (.eq a b)
  | not {φ : LFml C} (h : ApfFml Rs φ) : ApfFml Rs (.not φ)
  | and {φ ψ : LFml C} (h₁ : ApfFml Rs φ) (h₂ : ApfFml Rs ψ) : ApfFml Rs (.and φ ψ)
  | imp {φ ψ : LFml C} (h₁ : ApfFml Rs φ) (h₂ : ApfFml Rs ψ) : ApfFml Rs (.imp φ ψ)
  | all (k : Nat) (p : PrimTy) {φ : LFml C} (h : ApfFml Rs φ) : ApfFml Rs (.all k p φ)

def ApfFml.ofFormula? (Rs : ARoots) : (φ : LFml C) → Option (ApfFml Rs φ)
  | .tt => some .tt
  | .eq a b => do return .eq (← ApfTm.ofTerm? Rs false a) (← ApfTm.ofTerm? Rs false b)
  | .not φ => (ofFormula? Rs φ).map .not
  | .and φ ψ => do return .and (← ofFormula? Rs φ) (← ofFormula? Rs ψ)
  | .imp φ ψ => do return .imp (← ofFormula? Rs φ) (← ofFormula? Rs ψ)
  | .all k p φ => (ofFormula? Rs φ).map (.all k p)

section Refute

variable {ok : OrdK K} {Rs : ARoots} {Gd Lo : LTm C (.val K) → Prop} {Bs : List Parameter}

/-- **A formula reading alike in the rebuilt storage**: each term ground
(`ApfTm.Rel` at no block variable), each binder among `Bs`. -/
def ApfFml.Frame (ok : OrdK K) (Bs : List Parameter) (Gd : LTm C (.val K) → Prop) :
    {φ : LFml C} → ApfFml Rs φ → Prop
  | _, .tt => True
  | _, .eq ha hb => ha.Rel ok [] Bs Gd ∧ hb.Rel ok [] Bs Gd
  | _, .not h => h.Frame ok Bs Gd
  | _, .and h₁ h₂ | _, .imp h₁ h₂ => h₁.Frame ok Bs Gd ∧ h₂.Frame ok Bs Gd
  | _, .all k p h => (⟨p, k⟩ : Parameter) ∈ Bs ∧ h.Frame ok Bs Gd

variable {g : State C []} {st' : Storage C} {nt' : Ledger} {S : ApfSet} {ks : List Nat} {ν μ' μ : AEnv}

/-- The setting under a binder of `Bs` that is no block variable. -/
theorem Setting.set (hs : Setting ok g st' nt' Rs S Gd Lo ks Bs ν μ' μ) (p : PrimTy) (k : Nat) (v : p.Denote)
    (hB : (⟨p, k⟩ : Parameter) ∈ Bs) (hk : (⟨p, k⟩ : Parameter) ∉ ApfTm.ksP K ks) :
    Setting ok g st' nt' Rs S Gd Lo ks Bs ν (μ'.set p k v) (μ.set p k v) where
  lo := hs.lo
  hi := hs.hi
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
    have hne : (⟨p, k⟩ : Parameter) ≠ ⟨K, j⟩ := fun e => hk (e ▸ List.mem_map.2 ⟨j, hj, rfl⟩)
    have h1 : (μ.set p k v).get K j = μ.get K j :=
      Parameter.read_set_ne ⟨K, j⟩ ⟨p, k⟩ (Ne.symm hne) μ v
    have h2 : (μ'.set p k v).get K j = μ'.get K j :=
      Parameter.read_set_ne ⟨K, j⟩ ⟨p, k⟩ (Ne.symm hne) μ' v
    rw [h1, h2]
    exact hs.hk j hj
  hν q hq := by
    have hne : q ≠ ⟨p, k⟩ := fun e => hq (e ▸ hB)
    exact (Parameter.read_set_ne q ⟨p, k⟩ hne μ v).trans (hs.hν q hq)

/-- **Outside the blocks the formula reads alike.** -/
theorem ApfFml.frame_holds : ∀ {φ : LFml C} (h : ApfFml Rs φ) {μ : AEnv},
    Setting ok g st' nt' Rs S Gd Lo [] Bs ν μ μ → h.Frame ok Bs Gd →
      (φ.holds { g with storage := st', net := nt' } μ ↔ φ.holds g μ)
  | _, .tt, _, _, _ => Iff.rfl
  | _, .eq ha hb, _, hs, hf => by
    rw [LFml.holds_eq_iff, LFml.holds_eq_iff, hs.eval ha hf.1, hs.eval hb hf.2]
  | _, .not h, _, hs, hf => not_congr (ApfFml.frame_holds h hs hf)
  | _, .and h₁ h₂, _, hs, hf => and_congr (ApfFml.frame_holds h₁ hs hf.1) (ApfFml.frame_holds h₂ hs hf.2)
  | _, .imp h₁ h₂, _, hs, hf => imp_congr (ApfFml.frame_holds h₁ hs hf.1) (ApfFml.frame_holds h₂ hs hf.2)
  | _, .all k p h, _, hs, hf => forall_congr' fun v =>
      ApfFml.frame_holds h (hs.set p k v hf.1 (fun h => nomatch h)) hf.2

/-- **A guard atom**: a guard against `true`, or an equation of operands. -/
inductive GAtom (ok : OrdK K) (Gd Lo : LTm C (.val K) → Prop) (ks : List Nat) (Bs : List Parameter) :
    {p : PrimTy} → {a b : LTm C (.val p)} → ApfTm Rs false a → ApfTm Rs false b → Prop where
  | tt {tot ds : Bool} {G : LTm C (.val .bool)} {hG : ApfTm Rs false G}
      {hT : ApfTm Rs false (LTm.app0 (.lit (p := .bool) true))} :
      GuardP ok Gd Lo ks Bs tot ds hG → GAtom ok Gd Lo ks Bs hG hT
  | idx {a b : LTm C (.val K)} {ha : ApfTm Rs false a} {hb : ApfTm Rs false b} {va vb : Bool} :
      IdxP ok Gd Lo ks Bs va ha → IdxP ok Gd Lo ks Bs vb hb → GAtom ok Gd Lo ks Bs ha hb

/-- **A block body of the fragment**, at a polarity: guard atoms only in
negative positions, every other atom read alike. -/
def ApfFml.BodyOk (ok : OrdK K) (Gd Lo : LTm C (.val K) → Prop) (ks : List Nat) (Bs : List Parameter) :
    Bool → {φ : LFml C} → ApfFml Rs φ → Prop
  | _, _, .tt => True
  | pol, _, .eq ha hb =>
    (ha.Rel ok ks Bs Gd ∧ hb.Rel ok ks Bs Gd) ∨ (pol = false ∧ GAtom ok Gd Lo ks Bs ha hb)
  | pol, _, .not h => h.BodyOk ok Gd Lo ks Bs (!pol)
  | pol, _, .and h₁ h₂ => h₁.BodyOk ok Gd Lo ks Bs pol ∧ h₂.BodyOk ok Gd Lo ks Bs pol
  | pol, _, .imp h₁ h₂ => h₁.BodyOk ok Gd Lo ks Bs (!pol) ∧ h₂.BodyOk ok Gd Lo ks Bs pol
  | _, _, .all .. => False

theorem GAtom.holds (hs : Setting ok g st' nt' Rs S Gd Lo ks Bs ν μ' μ) {p : PrimTy} {a b : LTm C (.val p)}
    {ha : ApfTm Rs false a} {hb : ApfTm Rs false b} (hg : GAtom ok Gd Lo ks Bs ha hb) :
    (LFml.eq a b).holds { g with storage := st', net := nt' } μ' → (LFml.eq a b).holds g μ := by
  cases hg with
  | @tt tot ds G hG hT hg =>
    intro h
    cases hx' : (G.eval { g with storage := st', net := nt' } μ' : Option Bool) with
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
    rw [hy, ok.ext (eq_mono S (by rw [hs.lo]; exact (ok.bounds x').1) hfx hfy rfl)]

/-- **A block body true at the floors is true at the keys.** -/
theorem ApfFml.body_holds (hs : Setting ok g st' nt' Rs S Gd Lo ks Bs ν μ' μ) :
    ∀ (pol : Bool) {φ : LFml C} (h : ApfFml Rs φ), h.BodyOk ok Gd Lo ks Bs pol →
      (pol = true → φ.holds g μ → φ.holds { g with storage := st', net := nt' } μ') ∧
      (pol = false → φ.holds { g with storage := st', net := nt' } μ' → φ.holds g μ)
  | _, _, .tt, _ => ⟨fun _ h => h, fun _ h => h⟩
  | pol, _, @ApfFml.eq _ _ _ a b ha hb, hok => by
    rcases hok with ⟨hr₁, hr₂⟩ | ⟨rfl, hg⟩
    · have e : (LFml.eq a b).holds { g with storage := st', net := nt' } μ' ↔ (LFml.eq a b).holds g μ := by
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
theorem Setting.push (hs : Setting ok g st' nt' Rs S Gd Lo ks Bs ν μ' μ) (k : Nat) (i : K.Denote)
    (hB : (⟨K, k⟩ : Parameter) ∈ Bs) :
    Setting ok g st' nt' Rs S Gd Lo (ks ++ [k]) Bs ν (μ'.set K k i) (μ.set K k (lastK ok S i)) where
  lo := hs.lo
  hi := hs.hi
  surg := hs.surg
  gdS := hs.gdS
  loS := hs.loS
  loT := hs.loT
  hμ q hq := by
    have hne : q ≠ ⟨K, k⟩ := fun e => hq (by
      rw [e]; exact List.mem_map.2 ⟨k, List.mem_append_right _ List.mem_cons_self, rfl⟩)
    exact (Parameter.read_set_ne q _ hne μ' i).trans ((hs.hμ q fun h => hq (by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
      exact List.mem_map.2 ⟨j, List.mem_append_left _ hj, rfl⟩)).trans
        (Parameter.read_set_ne q _ hne μ (lastK ok S i)).symm)
  hk j hj := by
    by_cases he : j = k
    · subst he; rw [AEnv.get_set_self, AEnv.get_set_self]
    · rw [AEnv.get_set_ne μ K K _ he, AEnv.get_set_ne μ' K K _ he]
      exact hs.hk j ((List.mem_append.1 hj).resolve_right fun h => he (List.mem_singleton.1 h))
  hν q hq := by
    have hne : q ≠ ⟨K, k⟩ := fun e => hq (e ▸ hB)
    exact (Parameter.read_set_ne q _ hne μ (lastK ok S i)).trans (hs.hν q hq)

/-- **The block holds where its instances hold** (Bradley, Manna, Sipma):
at the keys `μ'` read in the rebuilt storage, by the instance at their
floors, which the index set `us` names. -/
theorem LFml.block_refute (us : List (LTm C (.val K)))
    (hus : ∀ u ∈ us, ∀ q ∈ u.parameters, q ∉ Bs)
    (hcover : ∀ s ∈ S, ∃ u ∈ us, ∃ v : K.Denote, (u.eval g ν : Option _) = some v ∧ ok.val v = s)
    (h0 : S.lo ∈ S) :
    ∀ (φ : LFml C) (done : List Nat) (μ' μ : AEnv), φ.chainQF K = true →
      Setting ok g st' nt' Rs S Gd Lo done Bs ν μ' μ →
      (∀ k ∈ φ.chainVars K, (⟨K, k⟩ : Parameter) ∈ Bs) →
      ∀ {B : LFml C}, φ.chainBody K = B → ∀ hb : ApfFml Rs B,
      hb.BodyOk ok Gd Lo (done ++ φ.chainVars K) Bs true →
      (φ.inst us).holds g μ → φ.holds { g with storage := st', net := nt' } μ'
  | .all k p φ, done, μ', μ, hc₀, hs, hB, B, hBe, hb, hok, hi => by
    obtain ⟨hp, hc⟩ := LFml.chainQF_all hc₀
    clear hc₀
    subst p
    rw [LFml.chainVars_all] at hB hok
    rw [LFml.chainBody_all] at hBe
    rw [LFml.inst_all] at hi
    intro i
    have hkB : (⟨K, k⟩ : Parameter) ∈ Bs := hB k List.mem_cons_self
    have hfS : ok.val (lastK ok S i) ∈ S := by
      rw [lastK_val ok S hs.lo hs.hi]
      rcases lastIn_mem S (ok.val i) with h | h
      · rw [h]; exact h0
      · exact h
    obtain ⟨u, hu, v, hv, hvs⟩ := hcover _ hfS
    have hv' : v = lastK ok S i := ok.ext hvs
    subst hv'
    have huμ : (u.eval g μ : Option K.Denote) = some (lastK ok S i) := by
      rw [← hv]; exact u.eval_agree_parameters g fun q hq => hs.hν q (hus u hu q hq)
    have hconj := (LFml.holds_conj g μ _).1 hi _ (List.mem_map.2 ⟨u, hu, rfl⟩)
    have hsub := hconj ((LFml.holds_eq_iff g μ u u).2 ⟨_, huμ, huμ⟩)
    rw [LFml.holds_subst1 g μ k u huμ _ (LFml.qfB_inst us φ hc)] at hsub
    exact LFml.block_refute us hus hcover h0 φ (done ++ [k]) _ _ hc (hs.push k i hkB)
      (fun j hj => hB j (List.mem_cons_of_mem _ hj)) hBe hb
      (by rw [List.append_assoc, List.singleton_append]; exact hok) hsub
  | .tt, done, μ', μ, _, hs, _, _, hBe, hb, hok, hi | .eq _ _, done, μ', μ, _, hs, _, _, hBe, hb, hok, hi
  | .not _, done, μ', μ, _, hs, _, _, hBe, hb, hok, hi | .and _ _, done, μ', μ, _, hs, _, _, hBe, hb, hok, hi
  | .imp _ _, done, μ', μ, _, hs, _, _, hBe, hb, hok, hi => by
    subst hBe
    exact (ApfFml.body_holds hs true hb (by simpa only [LFml.chainVars, List.append_nil] using hok)).1 rfl hi

/-- **The conditions the refutation needs**, outside the blocks: terms
read alike; at a negative block, its variables among `Bs` and its body
of the fragment; at any other quantifier, a formula read alike. -/
def ApfFml.TopOk (ok : OrdK K) (Gd Lo : LTm C (.val K) → Prop) (Bs : List Parameter) :
    Bool → {φ : LFml C} → ApfFml Rs φ → Prop
  | _, _, .tt => True
  | _, _, .eq ha hb => ha.Rel ok [] Bs Gd ∧ hb.Rel ok [] Bs Gd
  | pol, _, .not h => h.TopOk ok Gd Lo Bs (!pol)
  | pol, _, .and h₁ h₂ => h₁.TopOk ok Gd Lo Bs pol ∧ h₂.TopOk ok Gd Lo Bs pol
  | pol, _, .imp h₁ h₂ => h₁.TopOk ok Gd Lo Bs (!pol) ∧ h₂.TopOk ok Gd Lo Bs pol
  | pol, _, @ApfFml.all _ _ k p φ h =>
    if (!pol && (LFml.all k p φ).isBlock K Rs) = true then
      (∀ j ∈ (LFml.all k p φ).chainVars K, (⟨K, j⟩ : Parameter) ∈ Bs) ∧
        ∃ hb : ApfFml Rs ((LFml.all k p φ).chainBody K),
          hb.BodyOk ok Gd Lo ((LFml.all k p φ).chainVars K) Bs true
    else (⟨p, k⟩ : Parameter) ∈ Bs ∧ h.Frame ok Bs Gd

/-- **Instantiation is exact**: where the instantiated formula fails at
`ν`, the formula fails at `ν` in the rebuilt storage. -/
theorem ApfFml.apfInst_refute (us : List (LTm C (.val K)))
    (hus : ∀ u ∈ us, ∀ q ∈ u.parameters, q ∉ Bs)
    (hcover : ∀ s ∈ S, ∃ u ∈ us, ∃ v : K.Denote, (u.eval g ν : Option _) = some v ∧ ok.val v = s)
    (h0 : S.lo ∈ S) (hs : Setting ok g st' nt' Rs S Gd Lo [] Bs ν ν ν) :
    ∀ (pol : Bool) {φ : LFml C} (h : ApfFml Rs φ), h.TopOk ok Gd Lo Bs pol →
      (pol = true → φ.holds { g with storage := st', net := nt' } ν → (φ.apfInst Rs us pol).holds g ν) ∧
      (pol = false → (φ.apfInst Rs us pol).holds g ν → φ.holds { g with storage := st', net := nt' } ν)
  | _, _, .tt, _ => ⟨fun _ h => h, fun _ h => h⟩
  | _, _, @ApfFml.eq _ _ _ a b ha hb, hok => by
    have e : (LFml.eq a b).holds { g with storage := st', net := nt' } ν ↔ (LFml.eq a b).holds g ν := by
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
    by_cases hb : (!pol && (LFml.all k p φ).isBlock K Rs) = true
    · rw [if_pos hb] at hok
      have hpol : pol = false := by cases pol <;> simp_all only [Bool.not_true, Bool.false_and,
        Bool.false_eq_true]
      subst hpol
      obtain ⟨hB, hbd, hok⟩ := hok
      have hc : (LFml.all k p φ).chainQF K = true := by
        simp only [LFml.isBlock, Bool.not_false, Bool.true_and, Bool.and_eq_true] at hb
        exact hb.1.1
      refine ⟨nofun, fun _ hi => ?_⟩
      have hi' : ((LFml.all k p φ).inst us).holds g ν := by
        simpa only [LFml.apfInst, hb, if_true] using hi
      exact LFml.block_refute us hus hcover h0 _ [] ν ν hc hs hB rfl hbd
        (by simpa only [List.nil_append] using hok) hi'
    · rw [if_neg hb] at hok
      have e := ApfFml.frame_holds (.all k p h) hs hok
      have hx : (LFml.all k p φ).apfInst Rs us pol = .all k p φ := by
        simp only [LFml.apfInst, hb]
        rfl
      rw [hx]
      exact ⟨fun _ h => e.1 h, fun _ h => e.2 h⟩

end Refute

/-! ## Terms evaluated -/

/-- **`LTm.eval`, computed**: by `match`, the symbols by their compiled
`eval`s; the index set's values (`IdxKey.value`) read through it. -/
def LTm.evalC (g : State C []) (ν : AEnv) : {s : Srt} → LTm C s → Option (s.Den C g.H)
  | _, .var k => some (ν.get _ k)
  | _, .app0 o => o.eval g
  | _, .app1 o x => o.eval g (x.evalC g ν)
  | _, .app2 o x y => o.eval g (x.evalC g ν) (y.evalC g ν)
  | _, .app3 o x y z => o.eval g (x.evalC g ν) (y.evalC g ν) (z.evalC g ν)
  | _, .index it q i => (q.evalC g ν).bind fun r => (i.evalC g ν).bind fun j => some (r.index it j)
  | _, .obsW q => (q.evalC g ν).bind fun r => some (g.storage.obs.word (.ref r))
  | _, .obsL q => (q.evalC g ν).bind fun r => some (uintOfNat (g.storage.obs.len (.ref r)))
  | _, .obsH q => (q.evalC g ν).bind fun r => some (g.storage.obs.has (.ref r))
  | _, .seq d a => (d.evalC g ν).bind fun _ => a.evalC g ν
  | _, .orElse a b => (a.evalC g ν).or (b.evalC g ν)
  | _, .kite (p := p) a b t e =>
    (a.evalC g ν : Option p.Denote).bind fun x => (b.evalC g ν : Option p.Denote).bind fun y =>
      if x = y then t.evalC g ν else e.evalC g ν
  | _, .err => none

theorem LTm.evalC_eq (g : State C []) (ν : AEnv) : ∀ {s : Srt} (t : LTm C s), t.evalC g ν = t.eval g ν := by
  intro s t
  induction t with
  | var k => rfl
  | app0 o => rfl
  | app1 o x ih => rw [LTm.evalC, ih]; rfl
  | app2 o x y ihx ihy => rw [LTm.evalC, ihx, ihy]; rfl
  | app3 o x y z ihx ihy ihz => rw [LTm.evalC, ihx, ihy, ihz]; rfl
  | index it q i ihq ihi => rw [LTm.evalC, ihq, ihi]; rfl
  | obsW q ih => rw [LTm.evalC, ih]; rfl
  | obsL q ih => rw [LTm.evalC, ih]; rfl
  | obsH q ih => rw [LTm.evalC, ih]; rfl
  | seq d a ihd iha => rw [LTm.evalC, ihd, iha]; rfl
  | orElse a b iha ihb => rw [LTm.evalC, iha, ihb]; rfl
  | kite a b t e iha ihb iht ihe => rw [LTm.evalC, iha, ihb, iht, ihe]; rfl
  | err => rfl

/-! ## The checks, computed -/

/-- An index term; its value is computed by `LTm.evalC`. -/
abbrev IdxKey (C : Contract) (K : PrimTy) := LTm C (.val K)

/-- An index term of type `K'` at `K`, where they are one type. -/
def castIdx {K' : PrimTy} (h : K' = K) (e : IdxKey C K') : IdxKey C K := h ▸ e

theorem castIdx_rfl (e : IdxKey C K) : castIdx rfl e = e := rfl

/-- A ledger address in the index set: at a `uint` pass. -/
def netIdx : OrdK K → IdxKey C .uint → List (IdxKey C K)
  | .uint, e => [e]
  | .int, _ => []

/-- `NetRel`, computed. -/
def netB : OrdK K → List Nat → List Parameter → LTm C (.val .uint) → Bool → Bool
  | .uint, ks, Bs, i, r => i.isBVar ks || (i.parameters.all (fun q => decide (q ∉ Bs)) && r)
  | .int, _, _, _, _ => false

namespace ApfTm

variable {Rs : ARoots}

/-- `ApfTm.Rel`, computed: its ground keys are `gkeys`. -/
def relB (ok : OrdK K) (ks : List Nat) (Bs : List Parameter) :
    {b : Bool} → {s : Srt} → {t : LTm C s} → ApfTm Rs b t → Bool
  | _, _, _, @ApfTm.var _ _ p k => decide ((⟨p, k⟩ : Parameter) ∉ ksP K ks)
  | _, _, _, .lit _ | _, _, _, .env _ | _, _, _, .root .. | _, _, _, .rroot .. | _, _, _, .err
  | _, _, _, .zlit _ => true
  | _, _, _, .field _ hq | _, _, _, .rfield _ hq => hq.relB ok ks Bs
  | _, _, _, .index hq hi => hq.relB ok ks Bs && hi.relB ok ks Bs
  | _, _, _, .rkey (K := K') (i := i) hq hi =>
    hq.relB ok ks Bs && (if K' = K then
      (if hq.pre then i.isBVar ks || (i.parameters.all (fun q => decide (q ∉ Bs)) && hi.relB ok ks Bs)
        else hi.relB ok ks Bs)
      else hi.relB ok ks Bs)
  | _, _, _, .word hq | _, _, _, .rword hq => hq.relB ok ks Bs
  | _, _, _, .unop _ _ ht | _, _, _, .toInt ht => ht.relB ok ks Bs
  | _, _, _, .net (t := i) hi => if Rs.net then netB ok ks Bs i (hi.relB ok ks Bs) else hi.relB ok ks Bs
  | _, _, _, .binop _ _ ha hb | _, _, _, .zbin _ _ ha hb | _, _, _, .zcmp _ _ ha hb =>
    ha.relB ok ks Bs && hb.relB ok ks Bs
  | _, _, _, .seq hd ha => hd.relB ok ks Bs && ha.relB ok ks Bs
  | _, _, _, .orElse ha hb => ha.relB ok ks Bs && hb.relB ok ks Bs
  | _, _, _, .kite ha hb ht he =>
    ha.relB ok ks Bs && hb.relB ok ks Bs && ht.relB ok ks Bs && he.relB ok ks Bs
  | _, _, _, .aidx _ hq hi => hq.relB ok ks Bs && hi.relB ok ks Bs
  | _, _, _, .rat (R := R) (i := i) _ hq hi =>
    hq.relB ok ks Bs && (if PrimTy.uint = K then
      (if (hq.pre && (FloorShape.of K (.ref R)).isArr) = true then
        i.isBVar ks || (i.parameters.all (fun q => decide (q ∉ Bs)) && hi.relB ok ks Bs)
        else hi.relB ok ks Bs)
      else hi.relB ok ks Bs)
  | _, _, _, .rhas hq | _, _, _, .has hq | _, _, _, .rlen hq | _, _, _, .len hq => hq.relB ok ks Bs
  | _, _, _, .ite hc ha hb => hc.relB ok ks Bs && ha.relB ok ks Bs && hb.relB ok ks Bs

/-- The ground keys of type `K` along the mappings of the roots of `Rs`
(`pre`), and the ground ledger addresses where `Rs` reads the ledger. -/
def gkeys (ok : OrdK K) (ks : List Nat) : {b : Bool} → {s : Srt} → {t : LTm C s} → ApfTm Rs b t → List (IdxKey C K)
  | _, _, _, .var _ | _, _, _, .lit _ | _, _, _, .env _ | _, _, _, .root .. | _, _, _, .rroot ..
  | _, _, _, .err | _, _, _, .zlit _ => []
  | _, _, _, .field _ hq | _, _, _, .rfield _ hq | _, _, _, .word hq | _, _, _, .rword hq
  | _, _, _, .unop _ _ hq | _, _, _, .toInt hq => hq.gkeys ok ks
  | _, _, _, .net (t := i) hi =>
    (if Rs.net && !i.isBVar ks then netIdx ok i else []) ++ hi.gkeys ok ks
  | _, _, _, .index hq hi => hq.gkeys ok ks ++ hi.gkeys ok ks
  | _, _, _, .rkey (K := K') (i := i) hq hi =>
    hq.gkeys ok ks ++ (if h : K' = K then
      (if hq.pre && !i.isBVar ks then castIdx h i :: hi.gkeys ok ks else hi.gkeys ok ks)
      else hi.gkeys ok ks)
  | _, _, _, .binop _ _ ha hb | _, _, _, .seq ha hb | _, _, _, .orElse ha hb | _, _, _, .zbin _ _ ha hb
  | _, _, _, .zcmp _ _ ha hb => ha.gkeys ok ks ++ hb.gkeys ok ks
  | _, _, _, .kite ha hb ht he => ha.gkeys ok ks ++ hb.gkeys ok ks ++ ht.gkeys ok ks ++ he.gkeys ok ks
  | _, _, _, .aidx _ hq hi => hq.gkeys ok ks ++ hi.gkeys ok ks
  | _, _, _, .rat (R := R) (i := i) _ hq hi =>
    hq.gkeys ok ks ++ (if h : PrimTy.uint = K then
      (if hq.pre && (FloorShape.of K (.ref R)).isArr && !i.isBVar ks then castIdx h i :: hi.gkeys ok ks
        else hi.gkeys ok ks)
      else hi.gkeys ok ks)
  | _, _, _, .rhas hq | _, _, _, .has hq | _, _, _, .rlen hq | _, _, _, .len hq => hq.gkeys ok ks
  | _, _, _, .ite hc ha hb => hc.gkeys ok ks ++ ha.gkeys ok ks ++ hb.gkeys ok ks

theorem netB_sound {ok : OrdK K} {ks : List Nat} {Bs : List Parameter} {Gd : LTm C (.val K) → Prop}
    {i : LTm C (.val .uint)} {r : Bool} {R : Prop} (hr : r = true → R)
    (h : netB ok ks Bs i r = true) (hg : ∀ e ∈ (if !i.isBVar ks then netIdx ok i else []), Gd e) :
    NetRel ok ks Bs Gd i R := by
  cases ok with
  | int => simp only [netB, Bool.false_eq_true] at h
  | uint =>
    by_cases hv : i.isBVar ks = true
    · exact .inl (LTm.isBVar_spec hv)
    · simp only [netB, hv, Bool.false_or, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
      simp only [hv, Bool.not_false, if_true, netIdx, List.mem_singleton, forall_eq] at hg
      exact .inr ⟨h.1, hg, hr h.2⟩

theorem relB_sound {ok : OrdK K} {ks : List Nat} {Bs : List Parameter} {Gd : LTm C (.val K) → Prop} :
    ∀ {b : Bool} {s : Srt} {t : LTm C s} (ht : ApfTm Rs b t), ht.relB ok ks Bs = true →
      (∀ e ∈ ht.gkeys ok ks, Gd e) → ht.Rel ok ks Bs Gd
  | _, _, _, .var _, h, _ => by simpa only [relB, decide_eq_true_eq] using h
  | _, _, _, .lit _, _, _ | _, _, _, .env _, _, _ | _, _, _, .root .., _, _ | _, _, _, .rroot .., _, _
  | _, _, _, .err, _, _ | _, _, _, .zlit _, _, _ => trivial
  | _, _, _, .field _ hq, h, hg | _, _, _, .rfield _ hq, h, hg | _, _, _, .word hq, h, hg
  | _, _, _, .rword hq, h, hg | _, _, _, .unop _ _ hq, h, hg | _, _, _, .toInt hq, h, hg =>
    relB_sound hq h hg
  | _, _, _, .index hq hi, h, hg | _, _, _, .binop _ _ hq hi, h, hg
  | _, _, _, .seq hq hi, h, hg | _, _, _, .orElse hq hi, h, hg | _, _, _, .zbin _ _ hq hi, h, hg
  | _, _, _, .zcmp _ _ hq hi, h, hg => by
    simp only [relB, Bool.and_eq_true] at h
    exact ⟨relB_sound hq h.1 fun e he => hg e (List.mem_append_left _ he),
      relB_sound hi h.2 fun e he => hg e (List.mem_append_right _ he)⟩
  | _, _, _, .kite ha hb ht he, h, hg => by
    simp only [relB, Bool.and_eq_true] at h
    simp only [gkeys, List.append_assoc] at hg
    exact ⟨relB_sound ha h.1.1.1 fun e h' => hg e (List.mem_append_left _ h'),
      relB_sound hb h.1.1.2 fun e h' => hg e (List.mem_append_right _ (List.mem_append_left _ h')),
      relB_sound ht h.1.2 fun e h' => hg e (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _ h'))),
      relB_sound he h.2 fun e h' => hg e (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ h')))⟩
  | _, _, _, .net (t := i) hi, h, hg => by
    show if Rs.net = true then NetRel ok ks Bs Gd i (hi.Rel ok ks Bs Gd) else hi.Rel ok ks Bs Gd
    unfold gkeys at hg
    unfold relB at h
    have hg2 := fun e he => hg e (List.mem_append_right _ he)
    by_cases hn : Rs.net = true
    · rw [if_pos hn]
      rw [if_pos hn] at h
      simp only [hn, Bool.true_and] at hg
      exact netB_sound (fun hr => relB_sound hi hr hg2) h fun e he => hg e (List.mem_append_left _ he)
    · rw [if_neg hn]
      rw [if_neg hn] at h
      exact relB_sound hi h hg2
  | _, _, _, .rkey (K := K') (i := x) hq hx, h, hg => by
    have ihx : hx.relB ok ks Bs = true → (∀ e ∈ hx.gkeys ok ks, Gd e) → hx.Rel ok ks Bs Gd := relB_sound hx
    unfold gkeys at hg
    simp only [relB, Bool.and_eq_true] at h
    refine ⟨relB_sound hq h.1 fun e he => hg e (List.mem_append_left _ he), ?_⟩
    have hg' := fun e he => hg e (List.mem_append_right _ he)
    have h2 := h.2
    by_cases hK : K' = K
    · subst K'
      rw [dif_pos rfl]
      rw [if_pos rfl] at h2
      rw [dif_pos rfl] at hg'
      cases hp : hq.pre with
      | false =>
        simp only [hp, Bool.false_and, Bool.false_eq_true, if_false] at h2 hg'
        exact .inr ⟨rfl, ihx h2 hg'⟩
      | true =>
        refine .inl ⟨rfl, ?_⟩
        by_cases hv : x.isBVar ks = true
        · exact .inl (LTm.isBVar_spec hv)
        · simp only [hp, hv, Bool.not_false, Bool.and_self, if_true] at hg'
          simp only [hp, hv, if_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true,
            decide_eq_true_eq] at h2
          exact .inr ⟨h2.1, hg' _ List.mem_cons_self,
            ihx h2.2 fun e he => hg' e (List.mem_cons_of_mem _ he)⟩
    · rw [dif_neg hK]
      rw [if_neg hK] at h2
      rw [dif_neg hK] at hg'
      exact ihx h2 hg'
  | _, _, _, .aidx _ hq hi, h, hg => by
    simp only [relB, Bool.and_eq_true] at h
    exact ⟨relB_sound hq h.1 fun e he => hg e (List.mem_append_left _ he),
      relB_sound hi h.2 fun e he => hg e (List.mem_append_right _ he)⟩
  | _, _, _, .rhas hq, h, hg | _, _, _, .has hq, h, hg | _, _, _, .rlen hq, h, hg
  | _, _, _, .len hq, h, hg => relB_sound hq h hg
  | _, _, _, .ite hc ha hb, h, hg => by
    simp only [relB, Bool.and_eq_true] at h
    simp only [gkeys, List.append_assoc] at hg
    exact ⟨relB_sound hc h.1.1 fun e h' => hg e (List.mem_append_left _ h'),
      relB_sound ha h.1.2 fun e h' => hg e (List.mem_append_right _ (List.mem_append_left _ h')),
      relB_sound hb h.2 fun e h' => hg e (List.mem_append_right _ (List.mem_append_right _ h'))⟩
  | _, _, _, .rat (R := R) (i := x) _ hq hx, h, hg => by
    have ihx : hx.relB ok ks Bs = true → (∀ e ∈ hx.gkeys ok ks, Gd e) → hx.Rel ok ks Bs Gd := relB_sound hx
    unfold gkeys at hg
    simp only [relB, Bool.and_eq_true] at h
    refine ⟨relB_sound hq h.1 fun e he => hg e (List.mem_append_left _ he), ?_⟩
    have hg' := fun e he => hg e (List.mem_append_right _ he)
    have h2 := h.2
    by_cases hK : PrimTy.uint = K
    · subst hK
      rw [dif_pos rfl]
      rw [if_pos rfl] at h2
      rw [dif_pos rfl] at hg'
      by_cases hpa : (hq.pre && (FloorShape.of PrimTy.uint (.ref R)).isArr) = true
      · rw [if_pos hpa]
        rw [if_pos (by simpa only [Bool.and_eq_true] using hpa)] at h2
        by_cases hv : x.isBVar ks = true
        · exact .inl (by rw [castKey_rfl]; exact LTm.isBVar_spec hv)
        · simp only [hpa, hv, Bool.not_false, Bool.and_self, if_true] at hg'
          simp only [hv, Bool.false_or, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h2
          exact .inr ⟨h2.1, hg' _ List.mem_cons_self,
            ihx h2.2 fun e he => hg' e (List.mem_cons_of_mem _ he)⟩
      · rw [if_neg hpa]
        rw [if_neg (by simpa only [Bool.and_eq_true] using hpa)] at h2
        have hpa' : (hq.pre && (FloorShape.of PrimTy.uint (.ref R)).isArr && !x.isBVar ks) = false := by
          simp only [Bool.not_eq_true] at hpa
          rw [hpa, Bool.false_and]
        rw [hpa'] at hg'
        exact ihx h2 hg'
    · rw [dif_neg hK]
      rw [if_neg hK] at h2
      rw [dif_neg hK] at hg'
      exact ihx h2 hg'

/-- An operand of a guard comparison, computed. -/
def idxB (ok : OrdK K) (ks : List Nat) (Bs : List Parameter) {s : Srt} {a : LTm C s} (ha : ApfTm Rs false a) :
    Bool :=
  a.isBVar ks || (ha.relB ok ks Bs && a.parameters.all (fun q => decide (q ∉ Bs)))

/-- An operand's terms in the index set: itself and its keys, at `K`. -/
def idxGd (ok : OrdK K) (ks : List Nat) {p : PrimTy} {a : LTm C (.val p)} (ha : ApfTm Rs false a) :
    List (IdxKey C K) :=
  if h : p = K then (if a.isBVar ks then [] else castIdx h a :: ha.gkeys ok ks) else []

/-- An operand whose successor is in the index set, at `K`. -/
def idxLo (ks : List Nat) {p : PrimTy} {a : LTm C (.val p)} (_ha : ApfTm Rs false a) : List (IdxKey C K) :=
  if h : p = K then (if a.isBVar ks then [] else [castIdx h a]) else []

theorem idxB_sound {ok : OrdK K} {ks : List Nat} {Bs : List Parameter} {Gd Lo : LTm C (.val K) → Prop}
    {a : LTm C (.val K)} (ha : ApfTm Rs false a) (h : ha.idxB ok ks Bs = true)
    (hg : ∀ e ∈ idxGd ok ks ha, Gd e) (hl : ∀ e ∈ idxLo ks ha, Lo e) :
    IdxP ok Gd Lo ks Bs (a.isBVar ks) ha := by
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
  | _, _, .var _ | _, _, .lit _ | _, _, .env _ | _, _, .root .. | _, _, .field .. | _, _, .index ..
  | _, _, .word _ | _, _, .rword .. | _, _, .unop .. | _, _, .seq .. | _, _, .orElse ..
  | _, _, .kite .. | _, _, .err | _, _, .zlit _ | _, _, .toInt _ | _, _, .net _ | _, _, .zbin ..
  | _, _, .zcmp .. | _, _, .aidx .. | _, _, .rhas _ | _, _, .has _ | _, _, .rlen _ | _, _, .len _
  | _, _, .ite .. => true

/-- Whether a guard returns at the floors where it returned at the keys
(`GuardP`'s `ds`). -/
def guardDs (ks : List Nat) : {s : Srt} → {t : LTm C s} → ApfTm Rs false t → Bool
  | _, _, @ApfTm.binop _ _ op _ _ _ _ ha hb =>
    if op == .and then ha.guardDs ks && hb.guardTot ks
    else if op == .or then hb.guardTot ks
    else true
  | _, _, .var _ | _, _, .lit _ | _, _, .env _ | _, _, .root .. | _, _, .field .. | _, _, .index ..
  | _, _, .word _ | _, _, .rword .. | _, _, .unop .. | _, _, .seq .. | _, _, .orElse ..
  | _, _, .kite .. | _, _, .err | _, _, .zlit _ | _, _, .toInt _ | _, _, .net _ | _, _, .zbin ..
  | _, _, .zcmp .. | _, _, .aidx .. | _, _, .rhas _ | _, _, .has _ | _, _, .rlen _ | _, _, .len _
  | _, _, .ite .. => true

/-- A guard, computed. -/
def guardB (ok : OrdK K) (ks : List Nat) (Bs : List Parameter) :
    {s : Srt} → {t : LTm C s} → ApfTm Rs false t → Bool
  | _, _, @ApfTm.binop _ _ op p _ a b ha hb =>
    ((op == .and || op == .or) && p == .bool && ha.guardB ok ks Bs && hb.guardB ok ks Bs &&
        (op != .or || ha.guardDs ks)) ||
      (op.isGuardOp && p == K && ha.idxB ok ks Bs && hb.idxB ok ks Bs &&
        (!op.isStrict || !(a.isBVar ks && b.isBVar ks)))
  | _, _, .var _ | _, _, .lit _ | _, _, .env _ | _, _, .root .. | _, _, .field .. | _, _, .index ..
  | _, _, .word _ | _, _, .rword .. | _, _, .unop .. | _, _, .seq .. | _, _, .orElse ..
  | _, _, .kite .. | _, _, .err | _, _, .zlit _ | _, _, .toInt _ | _, _, .net _ | _, _, .zbin ..
  | _, _, .zcmp .. | _, _, .aidx .. | _, _, .rhas _ | _, _, .has _ | _, _, .rlen _ | _, _, .len _
  | _, _, .ite .. => false

/-- A guard's terms in the index set. -/
def guardGd (ok : OrdK K) (ks : List Nat) : {s : Srt} → {t : LTm C s} → ApfTm Rs false t → List (IdxKey C K)
  | _, _, @ApfTm.binop _ _ op _ _ _ _ ha hb =>
    (if op == .and || op == .or then ha.guardGd ok ks ++ hb.guardGd ok ks else []) ++
      (idxGd ok ks ha ++ idxGd ok ks hb)
  | _, _, .var _ | _, _, .lit _ | _, _, .env _ | _, _, .root .. | _, _, .field .. | _, _, .index ..
  | _, _, .word _ | _, _, .rword .. | _, _, .unop .. | _, _, .seq .. | _, _, .orElse ..
  | _, _, .kite .. | _, _, .err | _, _, .zlit _ | _, _, .toInt _ | _, _, .net _ | _, _, .zbin ..
  | _, _, .zcmp .. | _, _, .aidx .. | _, _, .rhas _ | _, _, .has _ | _, _, .rlen _ | _, _, .len _
  | _, _, .ite .. => []

/-- A guard's terms whose successors are in the index set. -/
def guardLo (ks : List Nat) : {s : Srt} → {t : LTm C s} → ApfTm Rs false t → List (IdxKey C K)
  | _, _, @ApfTm.binop _ _ op _ _ _ _ ha hb =>
    (if op == .and || op == .or then ha.guardLo ks ++ hb.guardLo ks else []) ++
      (idxLo ks ha ++ idxLo ks hb)
  | _, _, .var _ | _, _, .lit _ | _, _, .env _ | _, _, .root .. | _, _, .field .. | _, _, .index ..
  | _, _, .word _ | _, _, .rword .. | _, _, .unop .. | _, _, .seq .. | _, _, .orElse ..
  | _, _, .kite .. | _, _, .err | _, _, .zlit _ | _, _, .toInt _ | _, _, .net _ | _, _, .zbin ..
  | _, _, .zcmp .. | _, _, .aidx .. | _, _, .rhas _ | _, _, .has _ | _, _, .rlen _ | _, _, .len _
  | _, _, .ite .. => []

theorem guardB_sound {ok : OrdK K} {ks : List Nat} {Bs : List Parameter} {Gd Lo : LTm C (.val K) → Prop} :
    ∀ {p : PrimTy} {t : LTm C (.val p)} (ht : ApfTm Rs false t), ht.guardB ok ks Bs = true →
      (∀ e ∈ ht.guardGd ok ks, Gd e) → (∀ e ∈ ht.guardLo (K := K) ks, Lo e) →
        GuardP ok Gd Lo ks Bs (ht.guardTot ks) (ht.guardDs ks) ht
  | _, _, @ApfTm.binop _ _ op p h a b ha hb, hg, hd, hl => by
    have iha : ha.guardB ok ks Bs = true → (∀ e ∈ ha.guardGd ok ks, Gd e) →
        (∀ e ∈ ha.guardLo (K := K) ks, Lo e) →
        GuardP ok Gd Lo ks Bs (ha.guardTot ks) (ha.guardDs ks) ha := guardB_sound ha
    have ihb : hb.guardB ok ks Bs = true → (∀ e ∈ hb.guardGd ok ks, Gd e) →
        (∀ e ∈ hb.guardLo (K := K) ks, Lo e) →
        GuardP ok Gd Lo ks Bs (hb.guardTot ks) (hb.guardDs ks) hb := guardB_sound hb
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
  | _, _, .orElse .., hg, _, _ | _, _, .kite .., hg, _, _ | _, _, .err, hg, _, _
  | _, _, .zcmp .., hg, _, _ | _, _, .rhas _, hg, _, _ | _, _, .has _, hg, _, _
  | _, _, .rlen _, hg, _, _ | _, _, .len _, hg, _, _ | _, _, .ite .., hg, _, _ => by
    simp only [guardB, Bool.false_eq_true] at hg

end ApfTm

/-- The literal `true`. -/
def LTm.isTrueAt : {s : Srt} → LTm C s → Bool
  | _, .app0 (.lit (p := .bool) v) => v
  | _, _ => false

namespace ApfFml

variable {Rs : ARoots}

/-- A guard atom, computed. -/
def eqGuardB (ok : OrdK K) (ks : List Nat) (Bs : List Parameter) {p : PrimTy} {a b : LTm C (.val p)}
    (ha : ApfTm Rs false a) (hb : ApfTm Rs false b) : Bool :=
  (b.isTrueAt && ha.guardB ok ks Bs) || (p == K && ha.idxB ok ks Bs && hb.idxB ok ks Bs)

theorem eqGuardB_sound {ok : OrdK K} {ks : List Nat} {Bs : List Parameter} {Gd Lo : LTm C (.val K) → Prop}
    {p : PrimTy} {a b : LTm C (.val p)} (ha : ApfTm Rs false a) (hb : ApfTm Rs false b)
    (h : eqGuardB ok ks Bs ha hb = true)
    (hd : ∀ e ∈ ha.guardGd ok ks ++ ApfTm.idxGd ok ks ha ++ ApfTm.idxGd ok ks hb, Gd e)
    (hl : ∀ e ∈ ha.guardLo (K := K) ks ++ ApfTm.idxLo ks ha ++ ApfTm.idxLo ks hb, Lo e) :
    GAtom ok Gd Lo ks Bs ha hb := by
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
def bodyB (ok : OrdK K) (ks : List Nat) (Bs : List Parameter) : Bool → {φ : LFml C} → ApfFml Rs φ → Bool
  | _, _, .tt => true
  | pol, _, .eq ha hb => (ha.relB ok ks Bs && hb.relB ok ks Bs) || (!pol && eqGuardB ok ks Bs ha hb)
  | pol, _, .not h => h.bodyB ok ks Bs (!pol)
  | pol, _, .and h₁ h₂ => h₁.bodyB ok ks Bs pol && h₂.bodyB ok ks Bs pol
  | pol, _, .imp h₁ h₂ => h₁.bodyB ok ks Bs (!pol) && h₂.bodyB ok ks Bs pol
  | _, _, .all .. => false

/-- A body's terms in the index set. -/
def bodyGd (ok : OrdK K) (ks : List Nat) (Bs : List Parameter) : {φ : LFml C} → ApfFml Rs φ → List (IdxKey C K)
  | _, .tt | _, .all .. => []
  | _, .eq ha hb =>
    if (ha.relB ok ks Bs && hb.relB ok ks Bs) = true then ha.gkeys ok ks ++ hb.gkeys ok ks
    else ha.guardGd ok ks ++ ApfTm.idxGd ok ks ha ++ ApfTm.idxGd ok ks hb
  | _, .not h => h.bodyGd ok ks Bs
  | _, .and h₁ h₂ | _, .imp h₁ h₂ => h₁.bodyGd ok ks Bs ++ h₂.bodyGd ok ks Bs

/-- A body's terms whose successors are in the index set. -/
def bodyLo (ok : OrdK K) (ks : List Nat) (Bs : List Parameter) : {φ : LFml C} → ApfFml Rs φ → List (IdxKey C K)
  | _, .tt | _, .all .. => []
  | _, .eq ha hb =>
    if (ha.relB ok ks Bs && hb.relB ok ks Bs) = true then []
    else ha.guardLo ks ++ ApfTm.idxLo ks ha ++ ApfTm.idxLo ks hb
  | _, .not h => h.bodyLo ok ks Bs
  | _, .and h₁ h₂ | _, .imp h₁ h₂ => h₁.bodyLo ok ks Bs ++ h₂.bodyLo ok ks Bs

theorem bodyB_sound {ok : OrdK K} {ks : List Nat} {Bs : List Parameter} {Gd Lo : LTm C (.val K) → Prop} :
    ∀ (pol : Bool) {φ : LFml C} (h : ApfFml Rs φ), h.bodyB ok ks Bs pol = true →
      (∀ e ∈ h.bodyGd ok ks Bs, Gd e) → (∀ e ∈ h.bodyLo ok ks Bs, Lo e) → h.BodyOk ok Gd Lo ks Bs pol
  | _, _, .tt, _, _, _ => trivial
  | pol, _, .eq ha hb, hb', hd, hl => by
    unfold bodyGd at hd
    unfold bodyLo at hl
    by_cases hr : (ha.relB ok ks Bs && hb.relB ok ks Bs) = true
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
def frameB (ok : OrdK K) (Bs : List Parameter) : {φ : LFml C} → ApfFml Rs φ → Bool
  | _, .tt => true
  | _, .eq ha hb => ha.relB ok [] Bs && hb.relB ok [] Bs
  | _, .not h => h.frameB ok Bs
  | _, .and h₁ h₂ | _, .imp h₁ h₂ => h₁.frameB ok Bs && h₂.frameB ok Bs
  | _, .all k p h => decide ((⟨p, k⟩ : Parameter) ∈ Bs) && h.frameB ok Bs

/-- Its ground keys. -/
def frameGd (ok : OrdK K) : {φ : LFml C} → ApfFml Rs φ → List (IdxKey C K)
  | _, .tt => []
  | _, .eq ha hb => ha.gkeys ok [] ++ hb.gkeys ok []
  | _, .not h | _, .all _ _ h => h.frameGd ok
  | _, .and h₁ h₂ | _, .imp h₁ h₂ => h₁.frameGd ok ++ h₂.frameGd ok

theorem frameB_sound {ok : OrdK K} {Bs : List Parameter} {Gd : LTm C (.val K) → Prop} :
    ∀ {φ : LFml C} (h : ApfFml Rs φ), h.frameB ok Bs = true → (∀ e ∈ h.frameGd ok, Gd e) → h.Frame ok Bs Gd
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
def blockBody? (K : PrimTy) (Rs : ARoots) (φ : LFml C) : Option (ApfFml Rs (φ.chainBody K)) :=
  ofFormula? Rs (φ.chainBody K)

/-- `ApfFml.TopOk`, computed. -/
def topB (ok : OrdK K) (Bs : List Parameter) : Bool → {φ : LFml C} → ApfFml Rs φ → Bool
  | _, _, .tt => true
  | _, _, .eq ha hb => ha.relB ok [] Bs && hb.relB ok [] Bs
  | pol, _, .not h => h.topB ok Bs (!pol)
  | pol, _, .and h₁ h₂ => h₁.topB ok Bs pol && h₂.topB ok Bs pol
  | pol, _, .imp h₁ h₂ => h₁.topB ok Bs (!pol) && h₂.topB ok Bs pol
  | pol, _, @ApfFml.all _ _ k p φ h =>
    if (!pol && (LFml.all k p φ).isBlock K Rs) = true then
      ((LFml.all k p φ).chainVars K).all (fun j => decide ((⟨K, j⟩ : Parameter) ∈ Bs)) &&
        (match blockBody? K Rs (LFml.all k p φ) with
          | some hb => hb.bodyB ok ((LFml.all k p φ).chainVars K) Bs true
          | none => false)
    else decide ((⟨p, k⟩ : Parameter) ∈ Bs) && h.frameB ok Bs

/-- The terms the conditions put in the index set. -/
def topGd (ok : OrdK K) (Bs : List Parameter) : Bool → {φ : LFml C} → ApfFml Rs φ → List (IdxKey C K)
  | _, _, .tt => []
  | _, _, .eq ha hb => ha.gkeys ok [] ++ hb.gkeys ok []
  | pol, _, .not h => h.topGd ok Bs (!pol)
  | pol, _, .and h₁ h₂ => h₁.topGd ok Bs pol ++ h₂.topGd ok Bs pol
  | pol, _, .imp h₁ h₂ => h₁.topGd ok Bs (!pol) ++ h₂.topGd ok Bs pol
  | pol, _, @ApfFml.all _ _ k p φ h =>
    if (!pol && (LFml.all k p φ).isBlock K Rs) = true then
      (match blockBody? K Rs (LFml.all k p φ) with
        | some hb => hb.bodyGd ok ((LFml.all k p φ).chainVars K) Bs
        | none => [])
    else h.frameGd ok

/-- The terms whose successors the conditions put in the index set. -/
def topLo (ok : OrdK K) (Bs : List Parameter) : Bool → {φ : LFml C} → ApfFml Rs φ → List (IdxKey C K)
  | _, _, .tt | _, _, .eq _ _ => []
  | pol, _, .not h => h.topLo ok Bs (!pol)
  | pol, _, .and h₁ h₂ => h₁.topLo ok Bs pol ++ h₂.topLo ok Bs pol
  | pol, _, .imp h₁ h₂ => h₁.topLo ok Bs (!pol) ++ h₂.topLo ok Bs pol
  | pol, _, @ApfFml.all _ _ k p φ _ =>
    if (!pol && (LFml.all k p φ).isBlock K Rs) = true then
      (match blockBody? K Rs (LFml.all k p φ) with
        | some hb => hb.bodyLo ok ((LFml.all k p φ).chainVars K) Bs
        | none => [])
    else []

theorem topB_sound {ok : OrdK K} {Bs : List Parameter} {Gd Lo : LTm C (.val K) → Prop} :
    ∀ (pol : Bool) {φ : LFml C} (h : ApfFml Rs φ), h.topB ok Bs pol = true →
      (∀ e ∈ h.topGd ok Bs pol, Gd e) → (∀ e ∈ h.topLo ok Bs pol, Lo e) → h.TopOk ok Gd Lo Bs pol
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
      cases hbb : blockBody? K Rs (LFml.all k p φ) with
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
def LTm.succO (ok : OrdK K) (x : LTm C (.val K)) : LTm C (.val K) :=
  .app2 (.binop .add ok.addOk) x (.app0 (.lit (ok.ofInt 1)))

theorem LTm.eval_succO (ok : OrdK K) (g : State C []) (ν : AEnv) (x : LTm C (.val K)) {v : K.Denote}
    (hv : (x.eval g ν : Option _) = some v) (hb : ok.val v + 1 < ok.hi) :
    ∃ w : K.Denote, ((x.succO ok).eval g ν : Option _) = some w ∧ ok.val w = ok.val v + 1 := by
  refine ⟨ok.ofInt (ok.val v + 1), ?_, ok.val_ofInt (by have := ok.bounds v; omega) hb⟩
  rw [LTm.succO, LTm.eval_app2, Close.Op2.eval_binop, hv]
  exact ok.add_one v hb

/-- The successor's key. -/
def IdxKey.succ (ok : OrdK K) (e : IdxKey C K) : IdxKey C K := e.succO ok

/-- The key type's least value. -/
def IdxKey.base (ok : OrdK K) : IdxKey C K := .app0 (.lit (ok.ofInt ok.lo))

/-- The key type's largest value. -/
def IdxKey.top (ok : OrdK K) : IdxKey C K := .app0 (.lit ok.top)

/-- A key's value at `g`, `ν`, computed (`LTm.evalC`). -/
def IdxKey.value (g : State C []) (ν : AEnv) (e : IdxKey C K) : Option K.Denote := e.evalC g ν

theorem IdxKey.value_eq (g : State C []) (ν : AEnv) (e : IdxKey C K) :
    e.value g ν = (e.eval g ν : Option K.Denote) := LTm.evalC_eq g ν e

/-- **The index set's values** at `g`, `ν`. -/
def apfValues (ok : OrdK K) (us : List (IdxKey C K)) (g : State C []) (ν : AEnv) : List Int :=
  us.filterMap fun e => (e.value g ν).map ok.val

theorem mem_apfValues {ok : OrdK K} {us : List (IdxKey C K)} {g : State C []} {ν : AEnv} {s : Int} :
    s ∈ apfValues ok us g ν ↔ ∃ e ∈ us, ∃ v : K.Denote, (e.eval g ν : Option _) = some v ∧ ok.val v = s := by
  simp only [apfValues, List.mem_filterMap, Option.map_eq_some_iff, IdxKey.value_eq]

/-- **The index set without repeated terms**: a term written twice is one
instance, not two (`LTm.beqR`, structural). -/
def dedupKeys : List (IdxKey C K) → List (IdxKey C K)
  | [] => []
  | e :: l => e :: (dedupKeys l).filter fun e' => !(e'.beqR e)

theorem dedupKeys_mem : ∀ {l : List (IdxKey C K)} {e : IdxKey C K}, e ∈ l → ∃ e' ∈ dedupKeys l, e' = e
  | e₀ :: l, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨e, List.mem_cons_self, rfl⟩
    · obtain ⟨e', he', hee⟩ := dedupKeys_mem h
      by_cases hb : e'.beqR e₀ = true
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

/-- Whether a pass reads the ledger: only a `uint` one. -/
def OrdK.netB : OrdK K → Bool
  | .uint => true
  | .int => false

/-- The roots to rebuild, their names, and whether the ledger is. -/
def apfRoots (ok : OrdK K) (B : LFml C) : List (MRoot C) × ARoots :=
  let roots := (B.blockRoots K true).eraseDups.filterMap (MRoot.of? (C := C))
  (roots, ⟨roots.map (·.name), ok.netB && B.blockNet K true⟩)

/-- **The index set**: the least value; the largest where the pass reads the
ledger or is an `int` one (the regions past the goal's keys then read a
free word, not the last key's); the conditions' terms and the successors
of the guards' operands; the terms `extra` (an array's length atom,
feature 32); each term once. -/
def apfKeys (ok : OrdK K) (Rs : ARoots) (B : LFml C) (h : ApfFml Rs B) (extra : List (IdxKey C K) := []) :
    List (IdxKey C K) :=
  dedupKeys (IdxKey.base ok :: ((if Rs.net || !ok.netB then [IdxKey.top ok] else []) ++
    ((h.topGd ok B.binders true ++ (h.topLo ok B.binders true).map (IdxKey.succ ok)) ++ extra)))

theorem mem_apfKeys_gd {ok : OrdK K} {Rs : ARoots} {B : LFml C} {h : ApfFml Rs B} {extra : List (IdxKey C K)}
    {e : IdxKey C K} (he : e ∈ h.topGd ok B.binders true) : ∃ e' ∈ apfKeys ok Rs B h extra, e' = e :=
  dedupKeys_mem (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_left _
    (List.mem_append_left _ he))))

theorem mem_apfKeys_lo {ok : OrdK K} {Rs : ARoots} {B : LFml C} {h : ApfFml Rs B} {extra : List (IdxKey C K)}
    {e : IdxKey C K} (he : e ∈ h.topLo ok B.binders true) :
    ∃ e' ∈ apfKeys ok Rs B h extra, e' = IdxKey.succ ok e :=
  dedupKeys_mem (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_map.2 ⟨e, he, rfl⟩)))))

theorem base_mem_apfKeys {ok : OrdK K} {Rs : ARoots} {B : LFml C} {h : ApfFml Rs B} {extra : List (IdxKey C K)} :
    IdxKey.base ok ∈ apfKeys ok Rs B h extra := List.mem_cons_self

/-- Where every value of the index set bounds a strict guard, no key reads
the largest value past its floor (`ApfSet.region`): `lastIn` is the floor. -/
theorem lastIn_eq_floorIn (S : ApfSet) (h : ∀ v ∈ S.vals, v ∈ S.strict) (x : Int) :
    lastIn S x = floorIn S.lo S.vals x := by
  unfold lastIn
  rw [if_neg]
  intro hr
  rcases apfTop_mem' S with ht | ht
  · have := hr.1; have := hr.2.1; have := apfSecond_ge_lo S; omega
  · exact hr.2.2.1 (h _ ht)

/-- **Such floors rebuild arrays** (`ArrOK`). -/
theorem lastK_arrOK (ok : OrdK K) (S : ApfSet) (hlo : S.lo = ok.lo) (hhi : S.hi = ok.hi)
    (h : ∀ v ∈ S.vals, v ∈ S.strict) : ArrOK ok (lastK ok S) := by
  refine ⟨fun x y hxy => ?_, fun x => ?_⟩
  · rw [lastK_val ok S hlo hhi, lastK_val ok S hlo hhi]
    exact lastIn_mono S (by rw [hlo]; exact (ok.bounds x).1) hxy
  · rw [lastK_val ok S hlo hhi, lastIn_eq_floorIn S h]
    exact floorIn_le S.lo S.vals (by rw [hlo]; exact (ok.bounds x).1)

/-- **The rebuilt state is set**: the roots floored, the ledger too where
the pass reads it, every guard monotone; so a state refuting the
instantiated body gives one refuting the body. -/
theorem apfFloors (ok : OrdK K) (S : ApfSet) (hlo : S.lo = ok.lo) (hhi : S.hi = ok.hi) :
    FloorsOn ok (lastK ok S) S.breaks := by
  refine ⟨fun b hb => by rw [← hlo, ← hhi]; exact S.breaks_range hb,
    by rw [← hlo]; exact S.mem_breaks (.inl rfl) (Int.le_refl _) (by rw [hlo, hhi]; have := ok.lo_lt; omega),
    fun k => ?_⟩
  have hk := ok.bounds k
  rw [← hlo] at hk ⊢
  rw [← hhi] at hk
  have hb0 := floorIn_ge_base S.lo S.breaks (ok.val k)
  have hb1 := floorIn_le S.lo S.breaks hk.1
  apply ok.ext
  rw [lastK_val ok S hlo hhi, lastK_val ok S hlo hhi, ok.val_ofInt (by rw [← hlo]; exact hb0)
    (by rw [← hhi]; omega)]
  exact lastIn_breaks S hk.1 hk.2

/-- **The rebuilt state**: the roots, and the ledger where the pass reads
it, at their keys' floors. -/
def apfState (ok : OrdK K) (S : ApfSet) (roots : List (MRoot C)) (Rs : ARoots) (g : State C []) : State C [] :=
  { g with storage := surgeryAll ok (lastK ok S) S.breaks roots g.storage,
           net := if Rs.net then netRebuild ok (lastK ok S) S.breaks g.net else g.net }

/-- Only a `uint` pass rebuilds the ledger. -/
theorem apfNetFloor (ok : OrdK K) (B : LFml C) {f : K.Denote → K.Denote} {Bk : List Int}
    (hf : FloorsOn ok f Bk) (l : Ledger) (hn : (apfRoots ok B).2.net = true) :
    NetFloor ok f (netRebuild ok f Bk l) l := by
  cases ok with
  | uint => exact netRebuild_floor f Bk hf l
  | int => simp only [apfRoots, OrdK.netB, Bool.false_and, Bool.false_eq_true] at hn

/-- **Array property instantiation of one key type as a preparation**
(`Prep`): the negative blocks of `K` over the roots they read at their
variables, and over the ledger at a `uint` pass, instantiated at the index
set (with the terms `extra`, `apfKeys`); the body itself where there is
none, or where the body is outside the fragment.  A pass that rebuilds an
array lists every value of the index set among the strict guards'
operands, so no key reads the largest value past its floor (`ArrOK`). -/
def apfPrepK (ok : OrdK K) (B : LFml C) (extra : List (IdxKey C K) := []) : Prep B :=
  let roots := (apfRoots ok B).1
  let Rs := (apfRoots ok B).2
  if hn : Rs.names.Nodup ∧ (Rs.names ≠ [] ∨ Rs.net = true) then
    match ApfFml.ofFormula? Rs B with
    | none => Prep.id B
    | some h =>
      let us := apfKeys ok Rs B h extra
      if hc : h.topB ok B.binders true = true ∧
          us.all (fun e => e.parameters.all fun q => decide (q ∉ B.binders)) = true then
        { body := B.apfInst Rs us true
          sound := fun hv g ν => (LFml.apfInst_sound g Rs _ B true ν).1 rfl (hv g ν)
          refute := fun g ν hneg =>
            let lo := h.topLo ok B.binders true
            let arrs := roots.any fun R => (FloorShape.of K R.ty).hasArr
            let S : ApfSet := ⟨apfValues ok us g ν,
              apfValues ok lo g ν ++ (if arrs then apfValues ok us g ν else []), ok.lo, ok.hi⟩
            ⟨apfState ok S roots Rs g, by
              have hf := apfFloors ok S rfl rfl
              have hA : ∀ R ∈ roots, (FloorShape.of K R.ty).hasArr = true → ArrOK ok (lastK ok S) :=
                fun R hR ha => lastK_arrOK ok S rfl rfl fun v hv => by
                  have harr : arrs = true := List.any_eq_true.2 ⟨R, hR, ha⟩
                  show v ∈ apfValues ok lo g ν ++ (if arrs then apfValues ok us g ν else [])
                  rw [if_pos harr]
                  exact List.mem_append_right _ hv
              have hsurg : Surg ok g (surgeryAll ok (lastK ok S) S.breaks roots g.storage)
                  (if Rs.net then netRebuild ok (lastK ok S) S.breaks g.net else g.net) Rs (lastK ok S) :=
                { other := fun h hr => surgeryAll_get_ne _ _ _ _ h roots hr
                  keyAt := fun r hr => surgeryAll_word _ _ _ _ hf r roots hn.1 hA hr
                  hasAt := fun r hr => surgeryAll_has _ _ _ _ hf r roots hn.1 hA hr
                  lenAt := fun r hr => surgeryAll_len _ _ _ _ hf r roots hn.1 hA hr
                  netKeep := fun he => if_neg (by rw [he]; exact Bool.false_ne_true)
                  netAt := fun he => by
                    rw [if_pos he]
                    exact apfNetFloor ok B hf g.net he }
              have hall := List.all_eq_true.1 hc.2
              have hus : ∀ u ∈ us, ∀ q ∈ u.parameters, q ∉ B.binders := fun u hu q hq => by
                have := List.all_eq_true.1 (hall u hu) q hq
                simpa only [decide_eq_true_eq] using this
              have hcover : ∀ s ∈ S, ∃ u ∈ us, ∃ v : K.Denote,
                  (u.eval g ν : Option _) = some v ∧ ok.val v = s := fun s hs => by
                obtain ⟨e, he, v, hv, rfl⟩ := mem_apfValues.1 hs
                exact ⟨e, he, v, hv, rfl⟩
              have h0 : S.lo ∈ S := mem_apfValues.2 ⟨IdxKey.base ok, base_mem_apfKeys, ok.ofInt ok.lo, rfl,
                ok.val_ofInt (Int.le_refl _) (by have := ok.lo_lt; omega)⟩
              have hset : Setting ok g (surgeryAll ok (lastK ok S) S.breaks roots g.storage)
                  (if Rs.net then netRebuild ok (lastK ok S) S.breaks g.net else g.net) Rs S
                  (fun x => x ∈ us) (fun x => x ∈ lo) [] B.binders ν ν ν :=
                { lo := rfl
                  hi := rfl
                  surg := hsurg
                  gdS := fun x hx v hv => mem_apfValues.2 ⟨x, hx, v, hv, rfl⟩
                  loS := fun x hx v hv hb => by
                    obtain ⟨w, hw, hw1⟩ := LTm.eval_succO ok g ν x hv hb
                    obtain ⟨e', he', hee⟩ := mem_apfKeys_lo hx
                    exact mem_apfValues.2 ⟨e', he', w, by rw [hee]; exact hw, hw1⟩
                  loT := fun x hx v hv => List.mem_append_left _ (mem_apfValues.2 ⟨x, hx, v, hv, rfl⟩)
                  hμ := fun _ _ => rfl
                  hk := fun _ h => nomatch h
                  hν := fun _ _ => rfl }
              have htop := ApfFml.topB_sound (Gd := fun x => x ∈ us)
                (Lo := fun x => x ∈ lo) true h hc.1
                (fun e he => by
                  obtain ⟨e', he', hee⟩ := mem_apfKeys_gd he
                  exact hee ▸ he')
                (fun e he => he)
              exact fun hB => hneg ((ApfFml.apfInst_refute us hus hcover h0 hset true h htop).1
                rfl hB)⟩ }
      else Prep.id B
  else Prep.id B

/-- **Array property instantiation as a preparation**: the `uint` blocks
(the ledger's among them), then the `int` ones. -/
def apfPrep (B : LFml C) : Prep B := (apfPrepK .uint B).trans (apfPrepK .int _)

/-- **Array property instantiation with more index terms** at the `uint`
pass (feature 32: an array's live length, read as an atom). -/
def apfPrepWith (extra : List (IdxKey C .uint)) (B : LFml C) : Prep B :=
  (apfPrepK .uint B extra).trans (apfPrepK .int _)

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

