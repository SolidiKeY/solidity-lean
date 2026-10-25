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
  outside the blocks reads as before (`ApfTm.eval_rel`); a guard true at `i`
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
inductive ApfTm (Rs : List Name) : {s : Srt} → LTm C s → Type where
  | var {p : PrimTy} (k : Nat) : ApfTm Rs (LTm.var (p := p) k)
  | lit {p : PrimTy} (v : p.Denote) : ApfTm Rs (.app0 (.lit v))
  | env (k : EnvKey) : ApfTm Rs (.app0 (.env k))
  | root (r : Name) {T : Ty} (h : C.rootType r = some T) (hr : r ∉ Rs) : ApfTm Rs (.app0 (.root r h))
  | field {s f : Name} {T : Ty} (h : C.fieldType s f = some T) {q : LTm C (.path (.ref (.struct s)))}
      (hq : ApfTm Rs q) : ApfTm Rs (.app1 (.field h) q)
  | index {K : PrimTy} {T : Ty} {q : LTm C (.path (.ref (.mapping K T)))} {i : LTm C (.val K)}
      (hq : ApfTm Rs q) (hi : ApfTm Rs i) : ApfTm Rs (.index .map q i)
  | word {p : PrimTy} {q : LTm C (.path (.prim p))} (hq : ApfTm Rs q) : ApfTm Rs (.obsW q)
  | rread (R : MRoot C) (hR : R.name ∈ Rs) {x : LTm C (.val .uint)} (hx : ApfTm Rs x) :
      ApfTm Rs (.obsW (.index .map (.app0 (.root R.name R.h)) x))
  | unop (op : UnOp) {p : PrimTy} (h : op.accepts p = true) {t : LTm C (.val p)} (ht : ApfTm Rs t) :
      ApfTm Rs (.app1 (.unop op h) t)
  | binop (op : BinOp) {p : PrimTy} (h : op.accepts p = true) {a b : LTm C (.val p)}
      (ha : ApfTm Rs a) (hb : ApfTm Rs b) : ApfTm Rs (.app2 (.binop op h) a b)
  | seq {s' s : Srt} {d : LTm C s'} {a : LTm C s} (hd : ApfTm Rs d) (ha : ApfTm Rs a) : ApfTm Rs (.seq d a)
  | orElse {s : Srt} {a b : LTm C s} (ha : ApfTm Rs a) (hb : ApfTm Rs b) : ApfTm Rs (.orElse a b)
  | kite {p : PrimTy} {s : Srt} {a b : LTm C (.val p)} {t e : LTm C s}
      (ha : ApfTm Rs a) (hb : ApfTm Rs b) (ht : ApfTm Rs t) (he : ApfTm Rs e) : ApfTm Rs (.kite a b t e)
  | err {s : Srt} : ApfTm Rs (LTm.err (C := C) (s := s))

namespace ApfTm

variable {Rs : List Name}

/-- Recognize the fragment. -/
def ofTerm? (Rs : List Name) : {s : Srt} → (t : LTm C s) → Option (ApfTm Rs t)
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
def toRead : {s : Srt} → {t : LTm C s} → ApfTm Rs t → ReadExpr t
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
theorem rootsOut (g : State C []) (ν : AEnv) {s : Srt} {t : LTm C s} (ht : ApfTm Rs t) :
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
    {s : Srt} → {t : LTm C s} → ApfTm Rs t → Prop
  | _, _, @ApfTm.var _ _ p k => (⟨p, k⟩ : Parameter) ∉ ksP ks
  | _, _, .lit _ | _, _, .env _ | _, _, .root .. | _, _, .err => True
  | _, _, .field _ hq => hq.Rel ks Bs Gd
  | _, _, .index hq hi => hq.Rel ks Bs Gd ∧ hi.Rel ks Bs Gd
  | _, _, .word hq => hq.Rel ks Bs Gd
  | _, _, @ApfTm.rread _ _ _ _ x hx =>
    (∃ k ∈ ks, x = .var k) ∨ ((∀ q ∈ x.parameters, q ∉ Bs) ∧ Gd x ∧ hx.Rel ks Bs Gd)
  | _, _, .unop _ _ ht => ht.Rel ks Bs Gd
  | _, _, .binop _ _ ha hb => ha.Rel ks Bs Gd ∧ hb.Rel ks Bs Gd
  | _, _, .seq hd ha => hd.Rel ks Bs Gd ∧ ha.Rel ks Bs Gd
  | _, _, .orElse ha hb => ha.Rel ks Bs Gd ∧ hb.Rel ks Bs Gd
  | _, _, .kite ha hb ht he => ha.Rel ks Bs Gd ∧ hb.Rel ks Bs Gd ∧ ht.Rel ks Bs Gd ∧ he.Rel ks Bs Gd

end ApfTm

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
theorem ApfTm.eval_rel {Rs : List Name} (g : State C []) (st' : Storage C)
    {f : PrimTy.uint.Denote → PrimTy.uint.Denote} (hS : Surg g st' Rs f) {ks : List Nat}
    {Bs : List Parameter} {Gd : LTm C (.val .uint) → Prop} {ν μ' μ : AEnv}
    (hGd : ∀ x, Gd x → ∀ v, (x.eval g ν : Option PrimTy.uint.Denote) = some v → f v = v)
    (hμ : ∀ q, q ∉ ksP ks → q.read μ' = q.read μ)
    (hk : ∀ k ∈ ks, μ.get .uint k = f (μ'.get .uint k))
    (hν : ∀ q, q ∉ Bs → q.read μ = q.read ν) {s : Srt} {t : LTm C s} (ht : ApfTm Rs t)
    (hr : ht.Rel ks Bs Gd) : t.eval { g with storage := st' } μ' = t.eval g μ := by
  induction ht with
  | @var p k => exact congrArg some (hμ ⟨p, k⟩ hr)
  | lit | env | root | err => rfl
  | field h hq ih => rw [LTm.eval_app1, LTm.eval_app1, ih hr]; rfl
  | index hq hi ihq ihi => rw [LTm.eval_index, LTm.eval_index, ihq hr.1, ihi hr.2]
  | @word p q hq ih =>
    rw [LTm.eval_obsW, LTm.eval_obsW, ih hr]
    have hroot := ApfTm.rootsOut g μ hq
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
    (Bs : List Parameter) : Bool → {a : LTm C (.val .uint)} → ApfTm Rs a → Prop where
  | var (k : Nat) (hk : k ∈ ks) (hv : ApfTm Rs (LTm.var (p := .uint) k)) : IdxP Gd Lo ks Bs true hv
  | gnd {a : LTm C (.val .uint)} (ha : ApfTm Rs a) (hr : ha.Rel ks Bs Gd)
      (hb : ∀ q ∈ a.parameters, q ∉ Bs) (ht : a.totalB = true) (hs : Gd a) (hl : Lo a) :
      IdxP Gd Lo ks Bs false ha

/-- **A guard**: `&&` and `||` of comparisons of operands (`IdxP`), never a
strict one of two block variables. -/
inductive GuardP {Rs : List Name} (Gd Lo : LTm C (.val .uint) → Prop) (ks : List Nat)
    (Bs : List Parameter) : {p : PrimTy} → {t : LTm C (.val p)} → ApfTm Rs t → Prop where
  | and (h : BinOp.and.accepts .bool = true) {a b : LTm C (.val .bool)} {ha : ApfTm Rs a} {hb : ApfTm Rs b} :
      GuardP Gd Lo ks Bs ha → GuardP Gd Lo ks Bs hb → GuardP Gd Lo ks Bs (.binop .and h ha hb)
  | or (h : BinOp.or.accepts .bool = true) {a b : LTm C (.val .bool)} {ha : ApfTm Rs a} {hb : ApfTm Rs b} :
      GuardP Gd Lo ks Bs ha → GuardP Gd Lo ks Bs hb → GuardP Gd Lo ks Bs (.binop .or h ha hb)
  | cmp (op : BinOp) (h : op.accepts .uint = true) (hop : op.isGuardOp = true) {va vb : Bool}
      {a b : LTm C (.val .uint)} {ha : ApfTm Rs a} {hb : ApfTm Rs b} :
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
  hμ : ∀ q, q ∉ ApfTm.ksP ks → q.read μ' = q.read μ
  hk : ∀ k ∈ ks, μ.get .uint k = floorU S (μ'.get .uint k)
  hν : ∀ q, q ∉ Bs → q.read μ = q.read ν

section Setting

variable {g : State C []} {st' : Storage C} {Rs : List Name} {S : List Int}
  {Gd Lo : LTm C (.val .uint) → Prop} {ks : List Nat} {Bs : List Parameter} {ν μ' μ : AEnv}

theorem Setting.gd (hs : Setting g st' Rs S Gd Lo ks Bs ν μ' μ) :
    ∀ x, Gd x → ∀ v, (x.eval g ν : Option PrimTy.uint.Denote) = some v → floorU S v = v :=
  fun _ hx v hv => Subtype.ext (floorIn_fix S (hs.gdS _ hx v hv) (uintVal_bounds v).1)

theorem Setting.eval (hs : Setting g st' Rs S Gd Lo ks Bs ν μ' μ) {s : Srt}
    {t : LTm C s} (ht : ApfTm Rs t) (hr : ht.Rel ks Bs Gd) :
    t.eval { g with storage := st' } μ' = t.eval g μ :=
  ApfTm.eval_rel g st' hs.surg hs.gd hs.hμ hs.hk hs.hν ht hr

theorem IdxP.values (hs : Setting g st' Rs S Gd Lo ks Bs ν μ' μ) {v : Bool}
    {a : LTm C (.val .uint)} {ha : ApfTm Rs a} (hi : IdxP Gd Lo ks Bs v ha) :
    ∃ x' x : PrimTy.uint.Denote, (a.eval { g with storage := st' } μ' : Option _) = some x' ∧
      (a.eval g μ : Option _) = some x ∧ FRel S v x'.1 x.1 := by
  cases hi with
  | var k hk _ =>
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
    {t : LTm C (.val p)} {ht : ApfTm Rs t} (hg : GuardP Gd Lo ks Bs ht) :
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

/-- The term reads a root of `Rs` at a variable of `ks`. -/
def LTm.readsAtVar (Rs : List Name) (ks : List Nat) : {s : Srt} → LTm C s → Bool
  | _, .obsW (.index (k := .uint) (V := .prim _) .map (.app0 (.root r _)) (.var j)) =>
    decide (r ∈ Rs) && decide (j ∈ ks)
  | _, .app1 _ a | _, .obsW a | _, .obsL a | _, .obsH a => a.readsAtVar Rs ks
  | _, .app2 _ a b | _, .index _ a b | _, .seq a b | _, .orElse a b => a.readsAtVar Rs ks || b.readsAtVar Rs ks
  | _, .app3 _ a b c => a.readsAtVar Rs ks || b.readsAtVar Rs ks || c.readsAtVar Rs ks
  | _, .kite a b t e => a.readsAtVar Rs ks || b.readsAtVar Rs ks || t.readsAtVar Rs ks || e.readsAtVar Rs ks
  | _, _ => false

/-- The roots the term reads at a variable of `ks`. -/
def LTm.rootsAtVar (ks : List Nat) : {s : Srt} → LTm C s → List Name
  | _, .obsW (.index (k := .uint) (V := .prim _) .map (.app0 (.root r _)) (.var j)) =>
    if j ∈ ks then [r] else []
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
  | eq {p : PrimTy} {a b : LTm C (.val p)} (ha : ApfTm Rs a) (hb : ApfTm Rs b) : ApfFml Rs (.eq a b)
  | not {φ : LFml C} (h : ApfFml Rs φ) : ApfFml Rs (.not φ)
  | and {φ ψ : LFml C} (h₁ : ApfFml Rs φ) (h₂ : ApfFml Rs ψ) : ApfFml Rs (.and φ ψ)
  | imp {φ ψ : LFml C} (h₁ : ApfFml Rs φ) (h₂ : ApfFml Rs ψ) : ApfFml Rs (.imp φ ψ)
  | all (k : Nat) (p : PrimTy) {φ : LFml C} (h : ApfFml Rs φ) : ApfFml Rs (.all k p φ)

def ApfFml.ofFormula? (Rs : List Name) : (φ : LFml C) → Option (ApfFml Rs φ)
  | .tt => some .tt
  | .eq a b => do return .eq (← ApfTm.ofTerm? Rs a) (← ApfTm.ofTerm? Rs b)
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

variable {g : State C []} {st' : Storage C} {S : List Int} {ks : List Nat} {ν μ' μ : AEnv}

/-- The setting under a binder of `Bs` that is no block variable. -/
theorem Setting.set (hs : Setting g st' Rs S Gd Lo ks Bs ν μ' μ) (p : PrimTy) (k : Nat) (v : p.Denote)
    (hB : (⟨p, k⟩ : Parameter) ∈ Bs) (hk : (⟨p, k⟩ : Parameter) ∉ ApfTm.ksP ks) :
    Setting g st' Rs S Gd Lo ks Bs ν (μ'.set p k v) (μ.set p k v) where
  surg := hs.surg
  gdS := hs.gdS
  loS := hs.loS
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
    {p : PrimTy} → {a b : LTm C (.val p)} → ApfTm Rs a → ApfTm Rs b → Prop where
  | tt {G : LTm C (.val .bool)} {hG : ApfTm Rs G} {hT : ApfTm Rs (LTm.app0 (.lit (p := .bool) true))} :
      GuardP Gd Lo ks Bs hG → GAtom Gd Lo ks Bs hG hT
  | idx {a b : LTm C (.val .uint)} {ha : ApfTm Rs a} {hb : ApfTm Rs b} {va vb : Bool} :
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
    {ha : ApfTm Rs a} {hb : ApfTm Rs b} (hg : GAtom Gd Lo ks Bs ha hb) :
    (LFml.eq a b).holds { g with storage := st' } μ' → (LFml.eq a b).holds g μ := by
  cases hg with
  | tt hG =>
    obtain ⟨x', x, hx', hx, ht⟩ := hG.mono hs
    intro h
    simp only [LFml.holds, hx', hx] at h ⊢
    exact ht h
  | idx ia ib =>
    obtain ⟨x', x, hx', hx, hfx⟩ := ia.values hs
    obtain ⟨y', y, hy', hy, hfy⟩ := ib.values hs
    intro h
    simp only [LFml.holds, hx', hx, hy', hy] at h ⊢
    exact Subtype.ext (eq_mono S (uintVal_bounds x').1 hfx hfy (congrArg Subtype.val h))

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
    Setting g st' Rs S Gd Lo (ks ++ [k]) Bs ν (μ'.set .uint k i) (μ.set .uint k (floorU S i)) where
  surg := hs.surg
  gdS := hs.gdS
  loS := hs.loS
  hμ q hq := by
    have hne : q ≠ ⟨.uint, k⟩ := fun e => hq (by
      rw [e]; exact List.mem_map.2 ⟨k, List.mem_append_right _ List.mem_cons_self, rfl⟩)
    exact (Parameter.read_set_ne q _ hne μ' i).trans ((hs.hμ q fun h => hq (by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
      exact List.mem_map.2 ⟨j, List.mem_append_left _ hj, rfl⟩)).trans
        (Parameter.read_set_ne q _ hne μ (floorU S i)).symm)
  hk j hj := by
    by_cases he : j = k
    · subst he; rw [AEnv.get_set_self, AEnv.get_set_self]
    · rw [AEnv.get_set_ne μ .uint .uint _ he, AEnv.get_set_ne μ' .uint .uint _ he]
      exact hs.hk j ((List.mem_append.1 hj).resolve_right fun h => he (List.mem_singleton.1 h))
  hν q hq := by
    have hne : q ≠ ⟨.uint, k⟩ := fun e => hq (e ▸ hB)
    exact (Parameter.read_set_ne q _ hne μ (floorU S i)).trans (hs.hν q hq)

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
    have hfS : (floorU S i).1 ∈ S := by
      rcases floorIn_mem S i.1 with h | h
      · show floorIn S i.1 ∈ S
        rw [h]; exact h0
      · exact h
    obtain ⟨u, hu, v, hv, hvs⟩ := hcover _ hfS
    have hv' : v = floorU S i := Subtype.ext hvs
    subst hv'
    have huμ : (u.eval g μ : Option PrimTy.uint.Denote) = some (floorU S i) := by
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

/-- A variable of `ks`. -/
def LTm.isBVar (ks : List Nat) : {s : Srt} → LTm C s → Bool
  | _, .var k => decide (k ∈ ks)
  | _, _ => false

theorem LTm.isBVar_spec {ks : List Nat} {x : LTm C (.val .uint)} (h : x.isBVar ks = true) :
    ∃ k ∈ ks, x = .var k := by
  cases x with
  | var k => exact ⟨k, by simpa only [LTm.isBVar, decide_eq_true_eq] using h, rfl⟩
  | _ => simp only [LTm.isBVar, Bool.false_eq_true] at h

namespace ApfTm

variable {Rs : List Name}

/-- `ApfTm.Rel`, computed: its ground keys are `gkeys`. -/
def relB (ks : List Nat) (Bs : List Parameter) : {s : Srt} → {t : LTm C s} → ApfTm Rs t → Bool
  | _, _, @ApfTm.var _ _ p k => decide ((⟨p, k⟩ : Parameter) ∉ ksP ks)
  | _, _, .lit _ | _, _, .env _ | _, _, .root .. | _, _, .err => true
  | _, _, .field _ hq => hq.relB ks Bs
  | _, _, .index hq hi => hq.relB ks Bs && hi.relB ks Bs
  | _, _, .word hq => hq.relB ks Bs
  | _, _, @ApfTm.rread _ _ _ _ x hx =>
    x.isBVar ks || (x.parameters.all (fun q => decide (q ∉ Bs)) && hx.relB ks Bs)
  | _, _, .unop _ _ ht => ht.relB ks Bs
  | _, _, .binop _ _ ha hb => ha.relB ks Bs && hb.relB ks Bs
  | _, _, .seq hd ha => hd.relB ks Bs && ha.relB ks Bs
  | _, _, .orElse ha hb => ha.relB ks Bs && hb.relB ks Bs
  | _, _, .kite ha hb ht he => ha.relB ks Bs && hb.relB ks Bs && ht.relB ks Bs && he.relB ks Bs

/-- The ground keys of the roots of `Rs`. -/
def gkeys (ks : List Nat) : {s : Srt} → {t : LTm C s} → ApfTm Rs t → List (IdxKey C)
  | _, _, .var _ | _, _, .lit _ | _, _, .env _ | _, _, .root .. | _, _, .err => []
  | _, _, .field _ hq | _, _, .word hq | _, _, .unop _ _ hq => hq.gkeys ks
  | _, _, .index hq hi => hq.gkeys ks ++ hi.gkeys ks
  | _, _, @ApfTm.rread _ _ _ _ x hx => if x.isBVar ks then [] else ⟨x, hx.toRead⟩ :: hx.gkeys ks
  | _, _, .binop _ _ ha hb | _, _, .seq ha hb | _, _, .orElse ha hb => ha.gkeys ks ++ hb.gkeys ks
  | _, _, .kite ha hb ht he => ha.gkeys ks ++ hb.gkeys ks ++ ht.gkeys ks ++ he.gkeys ks

theorem relB_sound {ks : List Nat} {Bs : List Parameter} {Gd : LTm C (.val .uint) → Prop} :
    ∀ {s : Srt} {t : LTm C s} (ht : ApfTm Rs t), ht.relB ks Bs = true →
      (∀ e ∈ ht.gkeys ks, Gd e.1) → ht.Rel ks Bs Gd
  | _, _, .var _, h, _ => by simpa only [relB, decide_eq_true_eq] using h
  | _, _, .lit _, _, _ | _, _, .env _, _, _ | _, _, .root .., _, _ | _, _, .err, _, _ => trivial
  | _, _, .field _ hq, h, hg | _, _, .word hq, h, hg | _, _, .unop _ _ hq, h, hg => relB_sound hq h hg
  | _, _, .index hq hi, h, hg | _, _, .binop _ _ hq hi, h, hg | _, _, .seq hq hi, h, hg
  | _, _, .orElse hq hi, h, hg => by
    simp only [relB, Bool.and_eq_true] at h
    exact ⟨relB_sound hq h.1 fun e he => hg e (List.mem_append_left _ he),
      relB_sound hi h.2 fun e he => hg e (List.mem_append_right _ he)⟩
  | _, _, .kite ha hb ht he, h, hg => by
    simp only [relB, Bool.and_eq_true] at h
    simp only [gkeys, List.append_assoc] at hg
    exact ⟨relB_sound ha h.1.1.1 fun e h' => hg e (List.mem_append_left _ h'),
      relB_sound hb h.1.1.2 fun e h' => hg e (List.mem_append_right _ (List.mem_append_left _ h')),
      relB_sound ht h.1.2 fun e h' => hg e (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _ h'))),
      relB_sound he h.2 fun e h' => hg e (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ h')))⟩
  | _, _, @ApfTm.rread _ _ _ _ x hx, h, hg => by
    unfold gkeys at hg
    by_cases hv : x.isBVar ks = true
    · exact .inl (LTm.isBVar_spec hv)
    · rw [if_neg hv] at hg
      simp only [relB, hv, Bool.false_or, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
      exact .inr ⟨h.1, hg _ List.mem_cons_self, relB_sound hx h.2 fun e he => hg e (List.mem_cons_of_mem _ he)⟩

/-- An operand of a guard comparison, computed. -/
def idxB (ks : List Nat) (Bs : List Parameter) {s : Srt} {a : LTm C s} (ha : ApfTm Rs a) : Bool :=
  a.isBVar ks || (ha.relB ks Bs && a.parameters.all (fun q => decide (q ∉ Bs)) && a.totalB)

/-- An operand's terms in the index set: itself and its keys. -/
def idxGd (ks : List Nat) : (s : Srt) → {a : LTm C s} → ApfTm Rs a → List (IdxKey C)
  | .val .uint, a, ha => if a.isBVar ks then [] else ⟨a, ha.toRead⟩ :: ha.gkeys ks
  | _, _, _ => []

/-- An operand whose successor is in the index set. -/
def idxLo (ks : List Nat) : (s : Srt) → {a : LTm C s} → ApfTm Rs a → List (IdxKey C)
  | .val .uint, a, ha => if a.isBVar ks then [] else [⟨a, ha.toRead⟩]
  | _, _, _ => []

theorem idxB_sound {ks : List Nat} {Bs : List Parameter} {Gd Lo : LTm C (.val .uint) → Prop}
    {a : LTm C (.val .uint)} (ha : ApfTm Rs a) (h : ha.idxB ks Bs = true)
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
    exact .gnd ha (relB_sound ha h.1.1 fun e he => hg e (List.mem_cons_of_mem _ he)) h.1.2 h.2
      (hg _ List.mem_cons_self) (hl _ List.mem_cons_self)

/-- A guard, computed. -/
def guardB (ks : List Nat) (Bs : List Parameter) : {s : Srt} → {t : LTm C s} → ApfTm Rs t → Bool
  | _, _, @ApfTm.binop _ _ op p _ a b ha hb =>
    ((op == .and || op == .or) && p == .bool && ha.guardB ks Bs && hb.guardB ks Bs) ||
      (op.isGuardOp && p == .uint && ha.idxB ks Bs && hb.idxB ks Bs &&
        (!op.isStrict || !(a.isBVar ks && b.isBVar ks)))
  | _, _, .var _ | _, _, .lit _ | _, _, .env _ | _, _, .root .. | _, _, .field .. | _, _, .index ..
  | _, _, .word _ | _, _, .rread .. | _, _, .unop .. | _, _, .seq .. | _, _, .orElse ..
  | _, _, .kite .. | _, _, .err => false

/-- A guard's terms in the index set. -/
def guardGd (ks : List Nat) : {s : Srt} → {t : LTm C s} → ApfTm Rs t → List (IdxKey C)
  | _, _, @ApfTm.binop _ _ _ p _ _ _ ha hb =>
    ha.guardGd ks ++ hb.guardGd ks ++ idxGd ks (.val p) ha ++ idxGd ks (.val p) hb
  | _, _, .var _ | _, _, .lit _ | _, _, .env _ | _, _, .root .. | _, _, .field .. | _, _, .index ..
  | _, _, .word _ | _, _, .rread .. | _, _, .unop .. | _, _, .seq .. | _, _, .orElse ..
  | _, _, .kite .. | _, _, .err => []

/-- A guard's terms whose successors are in the index set. -/
def guardLo (ks : List Nat) : {s : Srt} → {t : LTm C s} → ApfTm Rs t → List (IdxKey C)
  | _, _, @ApfTm.binop _ _ _ p _ _ _ ha hb =>
    ha.guardLo ks ++ hb.guardLo ks ++ idxLo ks (.val p) ha ++ idxLo ks (.val p) hb
  | _, _, .var _ | _, _, .lit _ | _, _, .env _ | _, _, .root .. | _, _, .field .. | _, _, .index ..
  | _, _, .word _ | _, _, .rread .. | _, _, .unop .. | _, _, .seq .. | _, _, .orElse ..
  | _, _, .kite .. | _, _, .err => []

theorem guardB_sound {ks : List Nat} {Bs : List Parameter} {Gd Lo : LTm C (.val .uint) → Prop} :
    ∀ {p : PrimTy} {t : LTm C (.val p)} (ht : ApfTm Rs t), ht.guardB ks Bs = true →
      (∀ e ∈ ht.guardGd ks, Gd e.1) → (∀ e ∈ ht.guardLo ks, Lo e.1) → GuardP Gd Lo ks Bs ht
  | _, _, @ApfTm.binop _ _ op p h a b ha hb, hg, hd, hl => by
    have iha : ha.guardB ks Bs = true → (∀ e ∈ ha.guardGd ks, Gd e.1) → (∀ e ∈ ha.guardLo ks, Lo e.1) →
        GuardP Gd Lo ks Bs ha := guardB_sound ha
    have ihb : hb.guardB ks Bs = true → (∀ e ∈ hb.guardGd ks, Gd e.1) → (∀ e ∈ hb.guardLo ks, Lo e.1) →
        GuardP Gd Lo ks Bs hb := guardB_sound hb
    simp only [guardGd, guardLo, List.mem_append] at hd hl
    simp only [guardB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hg
    rcases hg with ⟨⟨⟨hop, rfl⟩, h1⟩, h2⟩ | ⟨⟨⟨⟨hop, rfl⟩, h1⟩, h2⟩, h3⟩
    · rcases hop with rfl | rfl
      · exact .and h (iha h1 (fun e he => hd e (.inl (.inl (.inl he))))
            (fun e he => hl e (.inl (.inl (.inl he)))))
          (ihb h2 (fun e he => hd e (.inl (.inl (.inr he)))) (fun e he => hl e (.inl (.inl (.inr he)))))
      · exact .or h (iha h1 (fun e he => hd e (.inl (.inl (.inl he))))
            (fun e he => hl e (.inl (.inl (.inl he)))))
          (ihb h2 (fun e he => hd e (.inl (.inl (.inr he)))) (fun e he => hl e (.inl (.inl (.inr he)))))
    · refine .cmp op h hop (idxB_sound ha h1 (fun e he => hd e (.inl (.inr he))) (fun e he => hl e (.inl (.inr he))))
        (idxB_sound hb h2 (fun e he => hd e (.inr he)) (fun e he => hl e (.inr he))) fun hs => ?_
      rw [hs] at h3
      simpa only [Bool.not_true, Bool.false_eq_true, false_or, Bool.not_eq_true'] using h3
  | _, _, .var _, hg, _, _ | _, _, .lit _, hg, _, _ | _, _, .env _, hg, _, _ | _, _, .word _, hg, _, _
  | _, _, .rread .., hg, _, _ | _, _, .unop .., hg, _, _ | _, _, .seq .., hg, _, _
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
    (ha : ApfTm Rs a) (hb : ApfTm Rs b) : Bool :=
  (b.isTrueAt && ha.guardB ks Bs) || (p == .uint && ha.idxB ks Bs && hb.idxB ks Bs)

theorem eqGuardB_sound {ks : List Nat} {Bs : List Parameter} {Gd Lo : LTm C (.val .uint) → Prop}
    {p : PrimTy} {a b : LTm C (.val p)} (ha : ApfTm Rs a) (hb : ApfTm Rs b) (h : eqGuardB ks Bs ha hb = true)
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

/-- The mapping root a name holds, if any. -/
def MRoot.of? (r : Name) : Option (MRoot C) :=
  match h : C.rootType r with
  | some (.ref (.mapping .uint (.prim p))) => some ⟨r, p, h⟩
  | _ => none

theorem MRoot.of?_name {r : Name} {R : MRoot C} (h : MRoot.of? r = some R) : R.name = r := by
  unfold MRoot.of? at h
  split at h
  · cases h; rfl
  · cases h

theorem MRoot.of?_self (R : MRoot C) : MRoot.of? R.name = some R := by
  unfold MRoot.of?
  split
  · rename_i p h
    exact congrArg some (MRoot.eq_of_name rfl)
  · rename_i hn
    exact absurd R.h (hn R.p)

theorem nodup_roots : ∀ (Rs : List Name), Rs.Nodup → ((Rs.filterMap (MRoot.of? (C := C))).map (·.name)).Nodup
  | [], _ => List.nodup_nil
  | r :: Rs, h => by
    rw [List.nodup_cons] at h
    rw [List.filterMap_cons]
    cases hr : MRoot.of? (C := C) r with
    | none => exact nodup_roots Rs h.2
    | some R =>
      rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => h.1 ?_, nodup_roots Rs h.2⟩
      obtain ⟨R', hR', he⟩ := List.mem_map.1 hm
      obtain ⟨r', hr', hR''⟩ := List.mem_filterMap.1 hR'
      rw [← MRoot.of?_name hr, ← he, MRoot.of?_name hR'']
      exact hr'

/-- **Array property instantiation as a preparation** (`Prep`): the
negative blocks over the roots they read at their variables, instantiated
at the index set; the body itself where there is none, or where the body
is outside the fragment. -/
def apfPrep (B : LFml C) : Prep B :=
  let Rs := (B.blockRoots true).eraseDups
  if hn : Rs.Nodup ∧ Rs ≠ [] then
    match ApfFml.ofFormula? Rs B with
    | none => Prep.id B
    | some h =>
      let us := IdxKey.zero :: (h.topGd B.binders true ++ (h.topLo B.binders true).map IdxKey.succ)
      if hc : h.topB B.binders true = true ∧
          us.all (fun e => e.1.parameters.all fun q => decide (q ∉ B.binders)) = true then
        { body := B.apfInst Rs (us.map (·.1)) true
          sound := fun hv g ν => (LFml.apfInst_sound g Rs _ B true ν).1 rfl (hv g ν)
          refute := fun g ν hneg =>
            let S := apfValues us g ν
            let roots := Rs.filterMap MRoot.of?
            ⟨{ g with storage := surgeryAll (floorU S) (floorTop S) roots g.storage }, by
              have hS : ∀ s ∈ S, s < ((2 ^ 256 : Nat) : Int) := fun s hs => by
                obtain ⟨_, _, v, _, rfl⟩ := mem_apfValues.1 hs
                exact (uintVal_bounds v).2
              have hsurg : Surg g (surgeryAll (floorU S) (floorTop S) roots g.storage) Rs (floorU S) :=
                ⟨fun r hr => surgeryAll_other _ _ _ r roots fun hm => hr (by
                    obtain ⟨R, hR, he⟩ := List.mem_map.1 hm
                    obtain ⟨r', hr', hR'⟩ := List.mem_filterMap.1 hR
                    rw [← he, MRoot.of?_name hR']; exact hr'),
                  fun R hR k => surgeryAll_at _ _ _ (floorU_top S hS) roots (nodup_roots Rs hn.1) R
                    (List.mem_filterMap.2 ⟨R.name, hR, MRoot.of?_self R⟩) k⟩
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
              have hset : Setting g (surgeryAll (floorU S) (floorTop S) roots g.storage) Rs S
                  (fun x => x ∈ us.map (·.1)) (fun x => x.succU ∈ us.map (·.1)) [] B.binders ν ν ν :=
                { surg := hsurg
                  gdS := fun x hx v hv => by
                    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
                    exact mem_apfValues.2 ⟨e, he, v, hv, rfl⟩
                  loS := fun x hx v hv hb => by
                    obtain ⟨w, hw, hw1⟩ := LTm.eval_succU g ν x hv hb
                    obtain ⟨e, he, he1⟩ := List.mem_map.1 hx
                    exact mem_apfValues.2 ⟨e, he, w, by rw [he1]; exact hw, hw1⟩
                  hμ := fun _ _ => rfl
                  hk := fun _ h => nomatch h
                  hν := fun _ _ => rfl }
              have htop := ApfFml.topB_sound (Gd := fun x => x ∈ us.map (·.1))
                (Lo := fun x => x.succU ∈ us.map (·.1)) true h hc.1
                (fun e he => List.mem_map.2 ⟨e, List.mem_cons_of_mem _ (List.mem_append_left _ he), rfl⟩)
                (fun e he => List.mem_map.2 ⟨e.succ, List.mem_cons_of_mem _
                  (List.mem_append_right _ (List.mem_map.2 ⟨e, he, rfl⟩)), rfl⟩)
              exact fun hB => hneg ((ApfFml.apfInst_refute (us.map (·.1)) hus hcover h0 hset true h htop).1
                rfl hB)⟩ }
      else Prep.id B
  else Prep.id B

end Solidity.Decide
