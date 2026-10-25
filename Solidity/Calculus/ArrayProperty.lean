import Solidity.Calculus.QuantHoist
import Solidity.Calculus.QueryReduction

/-!
# The array property fragment, instantiated (M7, step 5)

A universal block in a negative position whose body reads mappings at its
variables (`(∀ k. k < 10 → balances[k] == 0) → balances[5] == 0`) is
decided as Bradley, Manna and Sipma decide it: replaced by its instances
at the index set `U`, the goal's ground keys of those mappings and the
guards' ground bounds (each also plus one), and `0`; the instance is
decided by the quantified pipeline.

* **Sound** (`apfInst_sound`): the block implies each instance, and it
  stands where the formula is antitone in it.
* **Exact** (`apfInst_refute`): from a state where the instantiated body
  fails, a state where the body fails: each mapping read at a block
  variable is rebuilt (`MRoot.surgery`) so that its key `i` holds what key
  `⌊i⌋` held, `⌊i⌋` the largest value of the index set at most `i`
  (`floorIn`).  Reads at the index set keep their values, so everything
  outside the blocks reads as before (`ATm.eval_rel`); a guard true at `i`
  is true at `⌊i⌋` (`GTm.mono`: guards compare a variable with a ground
  term, or two variables by `≤`, `≥`, `==`, never `<`), so each block
  holds by its instance at `⌊i⌋`.

The fragment (`ApfData`, `apfPrep`): mappings `mapping(uint => p)` at roots,
read at a block variable directly (`m[k]`) or at a ground key; block
variables of type `uint`, compared in guards (atoms in negative positions
of the block body) and read only as keys; every other read of such a
root outside the fragment.  Nested mappings `m[i][j]` with two bound
indices are outside (decision recorded in `docs/automation.md`, M7).

The rebuilt mapping lists one entry per key below the index set's
largest value (keys above read its default): a refutation is as long as
that value, which bounds the cost of constructing it, not its existence.
-/

namespace Solidity.Decide

open Semantics ReadRealization

variable {C : Contract}

/-! ## The mappings rebuilt -/

/-- A root holding a mapping from `uint` to a primitive type. -/
structure MRoot (C : Contract) where
  name : Name
  p : PrimTy
  h : C.rootType name = some (.ref (.mapping .uint (.prim p)))

/-- The location of the key `k`. -/
def MRoot.at (R : MRoot C) (k : PrimTy.uint.Denote) : SRef C (.prim R.p) :=
  (SRef.ofRoot R.name R.h).index .map k

/-- The word at the key `k`. -/
def MRoot.word (R : MRoot C) (st : Storage C) (k : PrimTy.uint.Denote) : R.p.Denote :=
  st.obs.word (.ref (R.at k))

/-- The largest `uint`. -/
def uintMax : PrimTy.uint.Denote := uintOfNat (2 ^ 256 - 1)

/-- **The mapping rebuilt**: the key `k` holds what `f k` held, one entry
per key below `top`, the default `f` of the largest key. -/
def MRoot.surgery (R : MRoot C) (f : PrimTy.uint.Denote → PrimTy.uint.Denote) (top : Nat)
    (st : Storage C) : Storage C :=
  st.set R.h (SVal.map (SMap.ofList ((List.range top).map fun j =>
    (uintOfNat j, SVal.prim (R.word st (f (uintOfNat j)))))) (SVal.prim (R.word st (f uintMax))))

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

/-- **The key `k` reads what `f k` read**, where `f` is constant past `top`. -/
theorem MRoot.surgery_at (R : MRoot C) (f : PrimTy.uint.Denote → PrimTy.uint.Denote) (top : Nat)
    (st : Storage C) (hf : ∀ k : PrimTy.uint.Denote, top ≤ k.1.toNat → f k = f uintMax)
    (k : PrimTy.uint.Denote) :
    R.word (R.surgery f top st) k = R.word st (f k) := by
  have hp : (R.at k).path = .key k .nil := by
    show Path.append .nil (Path.index .map k) = _
    rw [Path.append_nil, Path.index_map]
  unfold MRoot.word MRoot.surgery
  rw [Storage.obs_word_ref, SVal.obs_word, hp]
  show SVal.wordOf ((((st.set R.h _).get R.h)).findM (.key k .nil)) = _
  rw [SFields.get_set_same, ← SVal.find_eq_findM, SVal.find_key, SMap.toList_ofList,
    lookupBy_range top (fun k => SVal.prim (R.word st (f k))) k]
  by_cases hk : k.1.toNat < top
  · rw [if_pos hk]
    rfl
  · rw [if_neg hk, hf k (by omega)]
    rfl

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

theorem MRoot.eq_of_name {R R' : MRoot C} (h : R.name = R'.name) : R = R' := by
  obtain ⟨n, p, hp⟩ := R
  obtain ⟨n', p', hp'⟩ := R'
  simp only at h
  subst h
  have : p = p' := by
    rw [hp] at hp'
    simp only [Option.some.injEq, Ty.ref.injEq, RefTy.mapping.injEq, Ty.prim.injEq, true_and] at hp'
    exact hp'
  subst this
  rfl

theorem surgeryAll_at (f : PrimTy.uint.Denote → PrimTy.uint.Denote) (top : Nat) (st : Storage C)
    (hf : ∀ k : PrimTy.uint.Denote, top ≤ k.1.toNat → f k = f uintMax) :
    ∀ Rs : List (MRoot C), (Rs.map (·.name)).Nodup → ∀ R ∈ Rs, ∀ k,
      R.word (surgeryAll f top Rs st) k = R.word st (f k)
  | [], _, _, h, _ => nomatch h
  | R' :: Rs, hn, R, hR, k => by
    rw [List.map_cons, List.nodup_cons] at hn
    rw [surgeryAll]
    rcases List.mem_cons.1 hR with rfl | hR
    · rw [MRoot.surgery_at R f top _ hf k]
      exact surgeryAll_other f top st (R.at (f k)) Rs hn.1
    · have hne : R.name ≠ R'.name := fun e => hn.1 (e ▸ List.mem_map.2 ⟨R, hR, rfl⟩)
      rw [MRoot.word, MRoot.surgery_other R' f top _ (R.at k) hne]
      exact surgeryAll_at f top st hf Rs hn.2 R hR k

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

/-! ## The fragment's terms -/

/-- **A term of the fragment**: roots of `Rs` read only at a key
(`rread`), every other path at a root outside `Rs`; no other storage
access. -/
inductive ATm (Rs : List Name) : {s : Srt} → LTm C s → Type where
  | var {p : PrimTy} (k : Nat) : ATm Rs (LTm.var (p := p) k)
  | lit {p : PrimTy} (v : p.Denote) : ATm Rs (.app0 (.lit v))
  | env (k : EnvKey) : ATm Rs (.app0 (.env k))
  | root (r : Name) {T : Ty} (h : C.rootType r = some T) (hr : r ∉ Rs) : ATm Rs (.app0 (.root r h))
  | field {s f : Name} {T : Ty} (h : C.fieldType s f = some T) {q : LTm C (.path (.ref (.struct s)))}
      (hq : ATm Rs q) : ATm Rs (.app1 (.field h) q)
  | index {K : PrimTy} {T : Ty} {q : LTm C (.path (.ref (.mapping K T)))} {i : LTm C (.val K)}
      (hq : ATm Rs q) (hi : ATm Rs i) : ATm Rs (.index .map q i)
  | word {p : PrimTy} {q : LTm C (.path (.prim p))} (hq : ATm Rs q) : ATm Rs (.obsW q)
  | rread (R : MRoot C) (hR : R.name ∈ Rs) {x : LTm C (.val .uint)} (hx : ATm Rs x) :
      ATm Rs (.obsW (.index .map (.app0 (.root R.name R.h)) x))
  | unop (op : UnOp) {p : PrimTy} (h : op.accepts p = true) {t : LTm C (.val p)} (ht : ATm Rs t) :
      ATm Rs (.app1 (.unop op h) t)
  | binop (op : BinOp) {p : PrimTy} (h : op.accepts p = true) {a b : LTm C (.val p)}
      (ha : ATm Rs a) (hb : ATm Rs b) : ATm Rs (.app2 (.binop op h) a b)
  | seq {s' s : Srt} {d : LTm C s'} {a : LTm C s} (hd : ATm Rs d) (ha : ATm Rs a) : ATm Rs (.seq d a)
  | orElse {s : Srt} {a b : LTm C s} (ha : ATm Rs a) (hb : ATm Rs b) : ATm Rs (.orElse a b)
  | kite {p : PrimTy} {s : Srt} {a b : LTm C (.val p)} {t e : LTm C s}
      (ha : ATm Rs a) (hb : ATm Rs b) (ht : ATm Rs t) (he : ATm Rs e) : ATm Rs (.kite a b t e)
  | err {s : Srt} : ATm Rs (LTm.err (C := C) (s := s))

namespace ATm

variable {Rs : List Name}

/-- Recognize the fragment. -/
def ofTerm? (Rs : List Name) : {s : Srt} → (t : LTm C s) → Option (ATm Rs t)
  | _, .var k => some (.var k)
  | _, .app0 (.lit v) => some (.lit v)
  | _, .app0 (.env k) => some (.env k)
  | _, .app0 (.root r h) => if hr : r ∈ Rs then none else some (.root r h hr)
  | _, .app1 (.field h) q => (ofTerm? Rs q).map (.field h)
  | _, .app1 (.unop op h) t => (ofTerm? Rs t).map (.unop op h)
  | _, .app2 (.binop op h) a b => do return .binop op h (← ofTerm? Rs a) (← ofTerm? Rs b)
  | _, .obsW (.index (k := .uint) (V := .prim p) .map (.app0 (.root r h)) x) =>
    if hR : r ∈ Rs then (ofTerm? Rs x).map (.rread ⟨r, p, h⟩ hR)
    else do return .word (.index (.root r h hR) (← ofTerm? Rs x))
  | _, .index .map q i => do return .index (← ofTerm? Rs q) (← ofTerm? Rs i)
  | _, .obsW q => (ofTerm? Rs q).map .word
  | _, .seq d a => do return .seq (← ofTerm? Rs d) (← ofTerm? Rs a)
  | _, .orElse a b => do return .orElse (← ofTerm? Rs a) (← ofTerm? Rs b)
  | _, .kite a b t e => do return .kite (← ofTerm? Rs a) (← ofTerm? Rs b) (← ofTerm? Rs t) (← ofTerm? Rs e)
  | _, .err => some .err
  | _, _ => none

/-- The read query of a term of the fragment. -/
def toRead : {s : Srt} → {t : LTm C s} → ATm Rs t → ReadExpr t
  | _, _, .var k => .var k
  | _, _, .lit v => .lit v
  | _, _, .env k => .env k
  | _, _, .root r h _ => .root r h
  | _, _, .field h hq => .field h hq.toRead
  | _, _, .index hq hi => .index hq.toRead hi.toRead
  | _, _, .word hq => .word hq.toRead
  | _, _, .rread R _ hx => .word (.index (.root R.name R.h) hx.toRead)
  | _, _, .unop op h ht => .unop op h ht.toRead
  | _, _, .binop op h ha hb => .binop op h ha.toRead hb.toRead
  | _, _, .seq hd ha => .seq hd.toRead ha.toRead
  | _, _, .orElse ha hb => .orElse ha.toRead hb.toRead
  | _, _, .kite ha hb ht he => .kite ha.toRead hb.toRead ht.toRead he.toRead
  | _, _, .err => .err

/-- A path value at a root outside `Rs`. -/
def RootsOut (Rs : List Name) {H : HTy} : (s : Srt) → Option (s.Den C H) → Prop
  | .path _, some r => r.root ∉ Rs
  | _, _ => True

theorem RootsOut.none (Rs : List Name) {H : HTy} : ∀ s : Srt, RootsOut (C := C) Rs (H := H) s none
  | .path _ | .val _ | .st | .sv _ | .ident _ | .addr _ | .mem | .mv _ | .sts _ | .spath _ _ | .kint => trivial

/-- **The fragment's paths are at roots outside `Rs`.** -/
theorem rootsOut (g : State C []) (ν : AEnv) {s : Srt} {t : LTm C s} (ht : ATm Rs t) :
    RootsOut Rs s (t.eval g ν) := by
  induction ht with
  | var | lit | env | word | rread | unop | binop => trivial
  | root r h hr => exact hr
  | @field _ _ _ h q hq ih =>
    rw [LTm.eval_app1, Close.Op1.eval_field]
    cases hq' : (q.eval g ν : Option (SRef C _)) with
    | none => exact RootsOut.none Rs _
    | some r => rw [hq'] at ih; exact ih
  | @index _ _ q i hq hi ihq ihi =>
    rw [LTm.eval_index]
    cases hq' : (q.eval g ν : Option (SRef C _)) with
    | none => exact RootsOut.none Rs _
    | some r =>
      rw [hq'] at ihq
      cases (i.eval g ν : Option _) with
      | none => exact RootsOut.none Rs _
      | some _ => exact ihq
  | seq hd ha ihd iha =>
    rw [LTm.eval_seq]
    cases LTm.eval g ν _ with
    | none => exact RootsOut.none Rs _
    | some _ => exact iha
  | orElse ha hb iha ihb =>
    rw [LTm.eval_orElse]
    cases h : LTm.eval g ν _ with
    | none => rw [h] at iha; exact ihb
    | some _ => rw [h] at iha; exact iha
  | kite ha hb ht he iha ihb iht ihe =>
    rw [LTm.eval_kite]
    cases (LTm.eval g ν _ : Option _) with
    | none => exact RootsOut.none Rs _
    | some x =>
      cases (LTm.eval g ν _ : Option _) with
      | none => exact RootsOut.none Rs _
      | some y =>
        dsimp only [Option.bind_some]
        split
        · exact iht
        · exact ihe
  | err => exact RootsOut.none Rs _

/-- The positions of `ks`, at `uint`. -/
def ksP (ks : List Nat) : List Parameter := ks.map (⟨.uint, ·⟩)

/-- **Where a term reads alike in the rebuilt storage**: the variables of
`ks` only as keys of `Rs`; every other key ground (`Gd`), mentioning no
binder of `Bs`. -/
def Rel (ks : List Nat) (Bs : List Parameter) (Gd : LTm C (.val .uint) → Prop) :
    {s : Srt} → {t : LTm C s} → ATm Rs t → Prop
  | _, _, @ATm.var _ _ p k => (⟨p, k⟩ : Parameter) ∉ ksP ks
  | _, _, .lit _ | _, _, .env _ | _, _, .root .. | _, _, .err => True
  | _, _, .field _ hq => hq.Rel ks Bs Gd
  | _, _, .index hq hi => hq.Rel ks Bs Gd ∧ hi.Rel ks Bs Gd
  | _, _, .word hq => hq.Rel ks Bs Gd
  | _, _, @ATm.rread _ _ _ _ x hx =>
    (∃ k ∈ ks, x = .var k) ∨ ((∀ q ∈ x.parameters, q ∉ Bs) ∧ Gd x ∧ hx.Rel ks Bs Gd)
  | _, _, .unop _ _ ht => ht.Rel ks Bs Gd
  | _, _, .binop _ _ ha hb => ha.Rel ks Bs Gd ∧ hb.Rel ks Bs Gd
  | _, _, .seq hd ha => hd.Rel ks Bs Gd ∧ ha.Rel ks Bs Gd
  | _, _, .orElse ha hb => ha.Rel ks Bs Gd ∧ hb.Rel ks Bs Gd
  | _, _, .kite ha hb ht he => ha.Rel ks Bs Gd ∧ hb.Rel ks Bs Gd ∧ ht.Rel ks Bs Gd ∧ he.Rel ks Bs Gd

end ATm

/-! ## Reads in the rebuilt storage -/

/-- What the rebuilding keeps: other roots' words, and each key of a root
of `Rs` at its floor's word. -/
structure Surg (g : State C []) (st' : Storage C) (Rs : List Name)
    (f : PrimTy.uint.Denote → PrimTy.uint.Denote) : Prop where
  other : ∀ {P : PrimTy} (r : SRef C (.prim P)), r.root ∉ Rs →
    st'.obs.word (.ref r) = g.storage.obs.word (.ref r)
  keyAt : ∀ R : MRoot C, R.name ∈ Rs → ∀ k, R.word st' k = R.word g.storage (f k)

theorem eval_rread (g : State C []) (μ : AEnv) (R : MRoot C) (x : LTm C (.val .uint)) :
    ((LTm.obsW (.index .map (.app0 (.root R.name R.h)) x)).eval g μ : Option R.p.Denote) =
      (x.eval g μ : Option PrimTy.uint.Denote).bind fun k => some (R.word g.storage k) := by
  rw [LTm.eval_obsW, LTm.eval_index]
  cases (x.eval g μ : Option PrimTy.uint.Denote) <;> rfl

theorem Parameter.read_var {p : PrimTy} (k : Nat) (μ : AEnv) :
    (⟨p, k⟩ : Parameter).read μ = μ.get p k := rfl

/-- **The relation**: in the rebuilt storage, at `μ'`, a term reads what it
reads at `μ` in the old one, where `μ` holds the floors of `μ'` at `ks`. -/
theorem ATm.eval_rel {Rs : List Name} (g : State C []) (st' : Storage C)
    {f : PrimTy.uint.Denote → PrimTy.uint.Denote} (hS : Surg g st' Rs f) {ks : List Nat}
    {Bs : List Parameter} {Gd : LTm C (.val .uint) → Prop} {ν μ' μ : AEnv}
    (hGd : ∀ x, Gd x → ∀ v, (x.eval g ν : Option PrimTy.uint.Denote) = some v → f v = v)
    (hμ : ∀ q, q ∉ ksP ks → q.read μ' = q.read μ)
    (hk : ∀ k ∈ ks, μ.get .uint k = f (μ'.get .uint k))
    (hν : ∀ q, q ∉ Bs → q.read μ = q.read ν) {s : Srt} {t : LTm C s} (ht : ATm Rs t)
    (hr : ht.Rel ks Bs Gd) : t.eval { g with storage := st' } μ' = t.eval g μ := by
  induction ht with
  | @var p k => exact congrArg some (hμ ⟨p, k⟩ hr)
  | lit | env | root | err => rfl
  | field h hq ih => rw [LTm.eval_app1, LTm.eval_app1, ih hr]; rfl
  | index hq hi ihq ihi => rw [LTm.eval_index, LTm.eval_index, ihq hr.1, ihi hr.2]
  | @word p q hq ih =>
    rw [LTm.eval_obsW, LTm.eval_obsW, ih hr]
    have hroot := ATm.rootsOut g μ hq
    cases hq' : (q.eval g μ : Option (SRef C (.prim p))) with
    | none => rfl
    | some r =>
      rw [hq'] at hroot
      exact congrArg some (hS.other r hroot)
  | @rread R hR x hx ih =>
    rw [eval_rread, eval_rread]
    rcases hr with ⟨k, hk', rfl⟩ | ⟨hb, hg, hx'⟩
    · show some (R.word st' (μ'.get .uint k)) = some (R.word g.storage (μ.get .uint k))
      rw [hk k hk', hS.keyAt R hR]
    · rw [ih hx']
      cases he : (x.eval g μ : Option PrimTy.uint.Denote) with
      | none => rfl
      | some v =>
        have hv : (x.eval g ν : Option PrimTy.uint.Denote) = some v := by
          rw [← he]
          exact (x.eval_agree_parameters g fun q hq => hν q (hb q hq)).symm
        show some (R.word st' v) = some (R.word g.storage v)
        rw [hS.keyAt R hR, hGd x hg v hv]
  | unop op h ht ih => rw [LTm.eval_app1, LTm.eval_app1, ih hr]; rfl
  | binop op h ha hb iha ihb => rw [LTm.eval_app2, LTm.eval_app2, iha hr.1, ihb hr.2]; rfl
  | seq hd ha ihd iha => rw [LTm.eval_seq, LTm.eval_seq, ihd hr.1, iha hr.2]
  | orElse ha hb iha ihb => rw [LTm.eval_orElse, LTm.eval_orElse, iha hr.1, ihb hr.2]
  | kite ha hb ht he iha ihb iht ihe =>
    rw [LTm.eval_kite, LTm.eval_kite, iha hr.1, ihb hr.2.1, iht hr.2.2.1, ihe hr.2.2.2]

/-! ## Guards: true at a key, true at its floor -/

/-- How an operand's value relates to its value at the floor: a block
variable's is its floor; a ground operand's is the same, in the index set
with its successor. -/
def FRel (S : List Int) (v : Bool) (x' x : Int) : Prop :=
  if v then x = floorIn S x' else x = x' ∧ x ∈ S ∧ (x + 1 < ((2 ^ 256 : Nat) : Int) → x + 1 ∈ S)

theorem le_mono (S : List Int) {vx vy : Bool} {x' y' x y : Int} (h0 : 0 ≤ x') (h0' : 0 ≤ y')
    (hx : FRel S vx x' x) (hy : FRel S vy y' y) (h : x' ≤ y') : x ≤ y := by
  unfold FRel at hx hy
  cases vx <;> cases vy <;> simp only [Bool.false_eq_true, if_false, if_true] at hx hy
  · omega
  · obtain ⟨rfl, hm, -⟩ := hx; rw [hy]; exact floorIn_ge S y' hm h
  · obtain ⟨rfl, -, -⟩ := hy; rw [hx]; exact Int.le_trans (floorIn_le S h0) h
  · rw [hx, hy]; exact floorIn_mono S h0 h

theorem lt_mono (S : List Int) {vx vy : Bool} {x' y' x y : Int} (h0 : 0 ≤ x')
    (hb : y' < ((2 ^ 256 : Nat) : Int)) (hx : FRel S vx x' x) (hy : FRel S vy y' y)
    (hv : (vx && vy) = false) (h : x' < y') : x < y := by
  unfold FRel at hx hy
  cases vx <;> cases vy <;> simp only [Bool.false_eq_true, if_false, if_true, Bool.and_self] at hx hy hv
  · omega
  · obtain ⟨rfl, -, hs⟩ := hx
    rw [hy]
    have := floorIn_ge S y' (hs (by omega)) (by omega)
    omega
  · obtain ⟨rfl, -, -⟩ := hy; rw [hx]; have := floorIn_le S h0; omega
  · cases hv

theorem eq_mono (S : List Int) {vx vy : Bool} {x' y' x y : Int} (h0 : 0 ≤ x')
    (hx : FRel S vx x' x) (hy : FRel S vy y' y) (h : x' = y') : x = y := by
  subst h
  unfold FRel at hx hy
  cases vx <;> cases vy <;> simp only [Bool.false_eq_true, if_false, if_true] at hx hy
  · omega
  · obtain ⟨rfl, hm, -⟩ := hx; rw [hy, floorIn_fix S hm h0]
  · obtain ⟨rfl, hm, -⟩ := hy; rw [hx, floorIn_fix S hm h0]
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
theorem cmp_mono (S : List Int) (op : BinOp) {vx vy : Bool} {x' y' x y : Int} (h0 : 0 ≤ x') (h0' : 0 ≤ y')
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

/-- **An operand of a guard comparison**: a block variable, or a total
ground term of the index set (`Gd`) whose successor is in it too (`Lo`). -/
inductive IdxP {Rs : List Name} (Gd Lo : LTm C (.val .uint) → Prop) (ks : List Nat)
    (Bs : List Parameter) : Bool → {a : LTm C (.val .uint)} → ATm Rs a → Prop where
  | var (k : Nat) (hk : k ∈ ks) : IdxP Gd Lo ks Bs true (.var k)
  | gnd {a : LTm C (.val .uint)} (ha : ATm Rs a) (hr : ha.Rel ks Bs Gd)
      (hb : ∀ q ∈ a.parameters, q ∉ Bs) (ht : a.totalB = true) (hs : Gd a) (hl : Lo a) :
      IdxP Gd Lo ks Bs false ha

/-- **A guard**: `&&` and `||` of comparisons of operands (`IdxP`), never a
strict one of two block variables. -/
inductive GuardP {Rs : List Name} (Gd Lo : LTm C (.val .uint) → Prop) (ks : List Nat)
    (Bs : List Parameter) : {p : PrimTy} → {t : LTm C (.val p)} → ATm Rs t → Prop where
  | and (h : BinOp.and.accepts .bool = true) {a b : LTm C (.val .bool)} {ha : ATm Rs a} {hb : ATm Rs b} :
      GuardP Gd Lo ks Bs ha → GuardP Gd Lo ks Bs hb → GuardP Gd Lo ks Bs (.binop .and h ha hb)
  | or (h : BinOp.or.accepts .bool = true) {a b : LTm C (.val .bool)} {ha : ATm Rs a} {hb : ATm Rs b} :
      GuardP Gd Lo ks Bs ha → GuardP Gd Lo ks Bs hb → GuardP Gd Lo ks Bs (.binop .or h ha hb)
  | cmp (op : BinOp) (h : op.accepts .uint = true) (hop : op.isGuardOp = true) {va vb : Bool}
      {a b : LTm C (.val .uint)} {ha : ATm Rs a} {hb : ATm Rs b} :
      IdxP Gd Lo ks Bs va ha → IdxP Gd Lo ks Bs vb hb → (op.isStrict = true → (va && vb) = false) →
      GuardP Gd Lo ks Bs (.binop op h ha hb)

/-- `true`, at `bool`. -/
def IsTrue : (p : PrimTy) → p.Denote → Prop
  | .bool, b => b = true
  | _, _ => False

/-- The setting of a rebuilt storage: `μ'` reads the keys, `μ` their
floors; both are `ν` off the binders; the terms `Gd` and their successors
`Lo` are in the index set at `ν`. -/
structure Setting (g : State C []) (st' : Storage C) (Rs : List Name) (S : List Int)
    (Gd Lo : LTm C (.val .uint) → Prop) (ks : List Nat) (Bs : List Parameter) (ν μ' μ : AEnv) : Prop where
  surg : Surg g st' Rs (floorU S)
  gdS : ∀ x, Gd x → InS S g ν x
  loS : ∀ x, Lo x → InSucc S g ν x
  hμ : ∀ q, q ∉ ATm.ksP ks → q.read μ' = q.read μ
  hk : ∀ k ∈ ks, μ.get .uint k = floorU S (μ'.get .uint k)
  hν : ∀ q, q ∉ Bs → q.read μ = q.read ν

section Setting

variable {g : State C []} {st' : Storage C} {Rs : List Name} {S : List Int}
  {Gd Lo : LTm C (.val .uint) → Prop} {ks : List Nat} {Bs : List Parameter} {ν μ' μ : AEnv}

theorem Setting.gd (hs : Setting g st' Rs S Gd Lo ks Bs ν μ' μ) :
    ∀ x, Gd x → ∀ v, (x.eval g ν : Option PrimTy.uint.Denote) = some v → floorU S v = v :=
  fun _ hx v hv => Subtype.ext (floorIn_fix S (hs.gdS _ hx v hv) (uintVal_bounds v).1)

theorem Setting.eval (hs : Setting g st' Rs S Gd Lo ks Bs ν μ' μ) {s : Srt}
    {t : LTm C s} (ht : ATm Rs t) (hr : ht.Rel ks Bs Gd) :
    t.eval { g with storage := st' } μ' = t.eval g μ :=
  ATm.eval_rel g st' hs.surg hs.gd hs.hμ hs.hk hs.hν ht hr

theorem IdxP.values (hs : Setting g st' Rs S Gd Lo ks Bs ν μ' μ) {v : Bool}
    {a : LTm C (.val .uint)} {ha : ATm Rs a} (hi : IdxP Gd Lo ks Bs v ha) :
    ∃ x' x : PrimTy.uint.Denote, (a.eval { g with storage := st' } μ' : Option _) = some x' ∧
      (a.eval g μ : Option _) = some x ∧ FRel S v x'.1 x.1 := by
  cases hi with
  | var k hk =>
    refine ⟨μ'.get .uint k, μ.get .uint k, rfl, rfl, ?_⟩
    show (μ.get .uint k).1 = floorIn S (μ'.get .uint k).1
    rw [hs.hk k hk]
    rfl
  | gnd ha hr hb ht hsS hl =>
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (LTm.totalB_eval g μ a ht)
    have hxν : (a.eval g ν : Option PrimTy.uint.Denote) = some x := by
      rw [← hx]; exact (a.eval_agree_parameters g fun q hq => hs.hν q (hb q hq)).symm
    exact ⟨x, x, (hs.eval ha hr).trans hx, hx, rfl, hs.gdS _ hsS x hxν, hs.loS _ hl x hxν⟩

end Setting

theorem binopT_andB (h : BinOp.and.accepts .bool = true) (x y : Bool) :
    binopT .and h x (some y) = some (x && y) := by cases x <;> cases y <;> rfl

theorem binopT_orB (h : BinOp.or.accepts .bool = true) (x y : Bool) :
    binopT .or h x (some y) = some (x || y) := by cases x <;> cases y <;> rfl

/-- **A guard true at the keys is true at their floors.** -/
theorem GuardP.mono {g : State C []} {st' : Storage C} {Rs : List Name} {S : List Int}
    {Gd Lo : LTm C (.val .uint) → Prop} {ks : List Nat} {Bs : List Parameter} {ν μ' μ : AEnv}
    (hs : Setting g st' Rs S Gd Lo ks Bs ν μ' μ) {p : PrimTy}
    {t : LTm C (.val p)} {ht : ATm Rs t} (hg : GuardP Gd Lo ks Bs ht) :
    ∃ x' x : p.Denote, (t.eval { g with storage := st' } μ' : Option _) = some x' ∧
      (t.eval g μ : Option _) = some x ∧ (IsTrue p x' → IsTrue p x) := by
  induction hg with
  | and h _ _ iha ihb =>
    obtain ⟨a', a, ha', ha, hta⟩ := iha
    obtain ⟨b', b, hb', hb, htb⟩ := ihb
    refine ⟨a' && b', a && b, ?_, ?_, ?_⟩
    · rw [LTm.eval_app2, Close.Op2.eval_binop, ha', hb']; exact binopT_andB h a' b'
    · rw [LTm.eval_app2, Close.Op2.eval_binop, ha, hb]; exact binopT_andB h a b
    · intro hab
      have hab' : a' = true ∧ b' = true := Bool.and_eq_true _ _ ▸ (hab : (a' && b') = true)
      show (a && b) = true
      rw [Bool.and_eq_true]
      exact ⟨hta hab'.1, htb hab'.2⟩
  | or h _ _ iha ihb =>
    obtain ⟨a', a, ha', ha, hta⟩ := iha
    obtain ⟨b', b, hb', hb, htb⟩ := ihb
    refine ⟨a' || b', a || b, ?_, ?_, ?_⟩
    · rw [LTm.eval_app2, Close.Op2.eval_binop, ha', hb']; exact binopT_orB h a' b'
    · rw [LTm.eval_app2, Close.Op2.eval_binop, ha, hb]; exact binopT_orB h a b
    · intro hab
      have hab' : a' = true ∨ b' = true := Bool.or_eq_true _ _ ▸ (hab : (a' || b') = true)
      show (a || b) = true
      rw [Bool.or_eq_true]
      exact hab'.elim (fun h => .inl (hta h)) (fun h => .inr (htb h))
  | cmp op h hop ia ib hst =>
    obtain ⟨x', x, hx', hx, hfx⟩ := ia.values hs
    obtain ⟨y', y, hy', hy, hfy⟩ := ib.values hs
    have bx := uintVal_bounds x'
    have bY := uintVal_bounds y'
    cases op <;> simp only [BinOp.isGuardOp, Bool.false_eq_true] at hop <;>
      refine ⟨cmpOf _ x'.1 y'.1, cmpOf _ x.1 y.1, ?_, ?_, fun hc => cmp_mono S _ bx.1 bY.1 bx.2 bY.2 hfx hfy hst hc⟩ <;>
      first
        | (rw [LTm.eval_app2, Close.Op2.eval_binop, hx', hy']; rfl)
        | (rw [LTm.eval_app2, Close.Op2.eval_binop, hx, hy]; rfl)

end Solidity.Decide
