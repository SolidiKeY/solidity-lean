import Solidity.Signature

/-!
# Floors and regions over an ordered key type (M7, features 18 and 20)

The array property fragment's refutation (`Calculus/ArrayProperty.lean`)
rebuilds a mapping, or the ledger, so that each key reads what its floor in
the index set held.  The keys are `uint`s or `int`s (`OrdK`), each value an
integer in `[lo, hi)`: the floor of a key is the largest value of the index
set at most it, the type's least value `lo` where there is none (`floorIn`),
or the set's largest value past the second largest where that bounds no
strict guard (`lastIn`, `ApfSet`).

A rebuilt mapping cannot list its keys one at a time: an `int`-keyed one has
`2^255` keys on either side of `0`, and one default.  So it is listed region
by region (`regionList`): the floor is constant between consecutive
breakpoints (`ApfSet.breaks`: `lo`, `lo + 1`, the index set's values and
their successors; `lastIn_breaks`), and each region is one symbolic run of
keys `[b, next b)` (`regionKeys`), skipped where its value is the default.
A read finds the region of its key's last breakpoint and nothing else
(`lookupBy_regionList`), so a refutation's reads are proved by region
reasoning: no entry is evaluated.  Evaluating a refutation lists only the
regions whose value is not the default.
-/

namespace Solidity.Decide

open Semantics

/-! ## Ordered key types -/

/-- **A key type the floors order**: `uint` or `int`, each value an integer
in `[lo, hi)`. -/
inductive OrdK : PrimTy → Type where
  | uint : OrdK .uint
  | int : OrdK .int

/-- `a ⊲ b` read on the integers. -/
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

/-- `true`, at `bool`. -/
def IsTrue : (p : PrimTy) → p.Denote → Prop
  | .bool, b => b = true
  | _, _ => False

namespace OrdK

variable {K : PrimTy}

/-- The least value. -/
def lo : OrdK K → Int
  | .uint => 0
  | .int => -((2 ^ 255 : Nat) : Int)

/-- Past the largest value. -/
def hi : OrdK K → Int
  | .uint => ((2 ^ 256 : Nat) : Int)
  | .int => ((2 ^ 255 : Nat) : Int)

/-- A value's integer. -/
def val : OrdK K → K.Denote → Int
  | .uint, v => v.1
  | .int, v => v.1

/-- An integer as a value, `0` out of range. -/
def ofInt : OrdK K → Int → K.Denote
  | .uint, x => if h : PrimTy.uint.inRange x = true then ⟨x, h⟩ else ⟨0, rfl⟩
  | .int, x => if h : PrimTy.int.inRange x = true then ⟨x, h⟩ else ⟨0, rfl⟩

theorem bounds : (ok : OrdK K) → ∀ v : K.Denote, ok.lo ≤ ok.val v ∧ ok.val v < ok.hi
  | .uint, v => by
    have := v.2
    simp only [PrimTy.inRange, decide_eq_true_eq] at this
    exact this
  | .int, v => by
    have := v.2
    simp only [PrimTy.inRange, decide_eq_true_eq] at this
    exact this

theorem ext : (ok : OrdK K) → ∀ {v w : K.Denote}, ok.val v = ok.val w → v = w
  | .uint, _, _, h => Subtype.ext h
  | .int, _, _, h => Subtype.ext h

theorem val_ofInt : (ok : OrdK K) → ∀ {x : Int}, ok.lo ≤ x → x < ok.hi → ok.val (ok.ofInt x) = x
  | .uint, x, h1, h2 => by
    have h : PrimTy.uint.inRange x = true := by
      simp only [PrimTy.inRange, decide_eq_true_eq]; exact ⟨h1, h2⟩
    simp only [ofInt, dif_pos h, val]
  | .int, x, h1, h2 => by
    have h : PrimTy.int.inRange x = true := by
      simp only [PrimTy.inRange, decide_eq_true_eq]; exact ⟨h1, h2⟩
    simp only [ofInt, dif_pos h, val]

theorem ofInt_val (ok : OrdK K) (v : K.Denote) : ok.ofInt (ok.val v) = v :=
  ok.ext (ok.val_ofInt (ok.bounds v).1 (ok.bounds v).2)

theorem lo_lt : (ok : OrdK K) → ok.lo + 1 < ok.hi
  | .uint => by decide
  | .int => by decide

theorem addOk : (ok : OrdK K) → BinOp.add.accepts K = true
  | .uint => rfl
  | .int => rfl

/-- **A comparison of two values reads their integers.** -/
theorem cmp_some : (ok : OrdK K) → ∀ (op : BinOp) (h : op.accepts K = true), op.isGuardOp = true →
    ∀ x y : K.Denote, ∃ c, binopT op h x (some y) = some c ∧
      (IsTrue (op.ret K) c ↔ cmpOf op (ok.val x) (ok.val y) = true)
  | .uint, op, h, hop, x, y => by
    cases op <;> simp only [BinOp.isGuardOp, Bool.false_eq_true] at hop <;> exact ⟨_, rfl, Iff.rfl⟩
  | .int, op, h, hop, x, y => by
    cases op <;> simp only [BinOp.isGuardOp, Bool.false_eq_true] at hop <;> exact ⟨_, rfl, Iff.rfl⟩

theorem cmp_none : (ok : OrdK K) → ∀ (op : BinOp) (h : op.accepts K = true), op.isGuardOp = true →
    ∀ x : K.Denote, binopT op h x none = none
  | .uint, op, h, hop, x => by
    cases op <;> simp only [BinOp.isGuardOp, Bool.false_eq_true] at hop <;> rfl
  | .int, op, h, hop, x => by
    cases op <;> simp only [BinOp.isGuardOp, Bool.false_eq_true] at hop <;> rfl

/-- **The successor, checked.** -/
theorem add_one : (ok : OrdK K) → ∀ (x : K.Denote), ok.val x + 1 < ok.hi →
    binopT .add ok.addOk x (some (ok.ofInt 1)) = some (ok.ofInt (ok.val x + 1))
  | .uint, x, hb => by
    have hx := OrdK.uint.bounds x
    have h1 : PrimTy.uint.inRange 1 = true := by decide
    have hr : PrimTy.uint.inRange (x.1 + 1) = true := by
      simp only [lo, hi, val] at hx hb
      simp only [PrimTy.inRange, decide_eq_true_eq]
      omega
    simp only [binopT, BinOp.shortT, Option.bind_some, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, ofInt,
      dif_pos h1, PrimTy.ofInt?, dif_pos hr, val]
  | .int, x, hb => by
    have hx := OrdK.int.bounds x
    have h1 : PrimTy.int.inRange 1 = true := by decide
    have hr : PrimTy.int.inRange (x.1 + 1) = true := by
      simp only [lo, hi, val] at hx hb
      simp only [PrimTy.inRange, decide_eq_true_eq]
      omega
    simp only [binopT, BinOp.shortT, Option.bind_some, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, ofInt,
      dif_pos h1, PrimTy.ofInt?, dif_pos hr, val]

/-- The largest value. -/
def top (ok : OrdK K) : K.Denote := ok.ofInt (ok.hi - 1)

end OrdK

/-! ## The floor in a list -/

/-- The largest value of `S` at most `x`, `b` where none is above `b`. -/
def floorIn (b : Int) (S : List Int) (x : Int) : Int := S.foldl (fun a s => if s ≤ x ∧ a < s then s else a) b

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

section FloorIn

variable (b : Int) (S : List Int)

theorem floorIn_le {x : Int} (hx : b ≤ x) : floorIn b S x ≤ x := (floorIn_spec S x b).2.1 hx
theorem floorIn_ge_base (x : Int) : b ≤ floorIn b S x := (floorIn_spec S x b).1
theorem floorIn_mem (x : Int) : floorIn b S x = b ∨ floorIn b S x ∈ S := (floorIn_spec S x b).2.2.1
theorem floorIn_ge (x : Int) {s : Int} (hs : s ∈ S) (h : s ≤ x) : s ≤ floorIn b S x :=
  (floorIn_spec S x b).2.2.2 s hs h

theorem floorIn_fix {s : Int} (hs : s ∈ S) (h0 : b ≤ s) : floorIn b S s = s :=
  Int.le_antisymm (floorIn_le b S h0) (floorIn_ge b S s hs (Int.le_refl _))

theorem floorIn_mono {x y : Int} (hx : b ≤ x) (h : x ≤ y) : floorIn b S x ≤ floorIn b S y := by
  rcases floorIn_mem b S x with h0 | hm
  · rw [h0]; exact floorIn_ge_base b S y
  · exact floorIn_ge b S y hm (Int.le_trans (floorIn_le b S hx) h)

end FloorIn

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
theorem floorIn_top (b : Int) (S : List Int) {x : Int} (h : ∀ s ∈ S, s ≤ x) :
    floorIn b S x = S.foldl max b := by
  obtain ⟨h0, hmax, hmem⟩ := foldl_max_spec S b
  apply Int.le_antisymm
  · rcases floorIn_mem b S x with he | hm
    · rw [he]; exact h0
    · exact hmax _ hm
  · rcases hmem with he | hm
    · rw [he]; exact floorIn_ge_base b S x
    · exact floorIn_ge b S x hm (h _ hm)

/-! ## The floor, its last interval read at the top

A refutation lists the rebuilt mapping region by region, and its default
is what the largest key reads.  Where the index set's largest value bounds
no strict guard from above (`ApfSet.strict`), the keys of the interval
below it, past the second largest value, read the largest value
(`lastIn`): a guard true there is true at it, and those keys then read the
default. -/

/-- The index set's values, those of the strict guards' ground operands
(`k < t`: `t` bounds the keys strictly from above), and the key type's
range `[lo, hi)`. -/
structure ApfSet where
  vals : List Int
  strict : List Int
  lo : Int
  hi : Int

instance : Membership Int ApfSet := ⟨fun S s => s ∈ S.vals⟩

theorem ApfSet.mem_def {S : ApfSet} {s : Int} : s ∈ S ↔ s ∈ S.vals := Iff.rfl

/-- The largest value, `lo` where none is above it. -/
def apfTop (S : ApfSet) : Int := S.vals.foldl max S.lo

/-- The second largest: the largest value below `apfTop`, `lo` where none is. -/
def apfSecond (S : ApfSet) : Int := (S.vals.filter (· < apfTop S)).foldl max S.lo

/-- The keys of the last interval below the largest value read it. -/
def ApfSet.region (S : ApfSet) (x : Int) : Prop :=
  apfSecond S < x ∧ x < apfTop S ∧ apfTop S ∉ S.strict ∧ apfTop S < S.hi

instance (S : ApfSet) (x : Int) : Decidable (S.region x) := by unfold ApfSet.region; infer_instance

/-- **The key a key reads in the rebuilt mapping**: its floor, the largest
value in its last interval below it. -/
def lastIn (S : ApfSet) (x : Int) : Int := if S.region x then apfTop S else floorIn S.lo S.vals x

section LastIn

variable (S : ApfSet)

theorem apfTop_ge {s : Int} (hs : s ∈ S.vals) : s ≤ apfTop S := (foldl_max_spec S.vals S.lo).2.1 s hs

theorem apfTop_ge_lo : S.lo ≤ apfTop S := (foldl_max_spec S.vals S.lo).1

theorem apfTop_mem (h : S.lo < apfTop S) : apfTop S ∈ S.vals :=
  ((foldl_max_spec S.vals S.lo).2.2).resolve_left (by unfold apfTop at h; omega)

theorem apfTop_mem' : apfTop S = S.lo ∨ apfTop S ∈ S.vals := (foldl_max_spec S.vals S.lo).2.2

theorem apfSecond_ge {s : Int} (hs : s ∈ S.vals) (h : s < apfTop S) : s ≤ apfSecond S :=
  (foldl_max_spec _ S.lo).2.1 s (List.mem_filter.2 ⟨hs, by simpa only [decide_eq_true_eq] using h⟩)

theorem apfSecond_ge_lo : S.lo ≤ apfSecond S := (foldl_max_spec _ S.lo).1

theorem apfSecond_mem : apfSecond S = S.lo ∨ apfSecond S ∈ S.vals := by
  rcases (foldl_max_spec (S.vals.filter (· < apfTop S)) S.lo).2.2 with h | h
  · exact .inl h
  · exact .inr (List.mem_filter.1 h).1

/-- Past the second largest value, a value is the largest. -/
theorem eq_top_of_second {s : Int} (hs : s ∈ S.vals) (h : apfSecond S < s) : s = apfTop S := by
  have := apfTop_ge S hs
  by_cases hl : s < apfTop S
  · have := apfSecond_ge S hs hl; omega
  · omega

theorem floorIn_le_top (x : Int) : floorIn S.lo S.vals x ≤ apfTop S := by
  rcases floorIn_mem S.lo S.vals x with h | h
  · rw [h]; exact apfTop_ge_lo S
  · exact apfTop_ge S h

theorem lastIn_fix {s : Int} (hs : s ∈ S) (h0 : S.lo ≤ s) : lastIn S s = s := by
  unfold lastIn
  split
  · rename_i hr
    have := eq_top_of_second S hs hr.1
    omega
  · exact floorIn_fix S.lo S.vals hs h0

theorem lastIn_ge (x : Int) {s : Int} (hs : s ∈ S) (h : s ≤ x) : s ≤ lastIn S x := by
  unfold lastIn
  split
  · exact apfTop_ge S hs
  · exact floorIn_ge S.lo S.vals x hs h

theorem lastIn_le {x s : Int} (hx : S.lo ≤ x) (hs : s ∈ S) (h : x ≤ s) : lastIn S x ≤ s := by
  unfold lastIn
  split
  · rename_i hr
    have := eq_top_of_second S hs (by have := hr.1; omega)
    omega
  · have := floorIn_le S.lo S.vals hx; omega

theorem lastIn_lt {x t : Int} (hx : S.lo ≤ x) (ht : t ∈ S) (hts : t ∈ S.strict) (h : x < t) :
    lastIn S x < t := by
  unfold lastIn
  split
  · rename_i hr
    have he := eq_top_of_second S ht (by have := hr.1; omega)
    exact absurd (he ▸ hts) hr.2.2.1
  · have := floorIn_le S.lo S.vals hx; omega

theorem floorIn_le_lastIn (x : Int) : floorIn S.lo S.vals x ≤ lastIn S x := by
  unfold lastIn
  split
  · exact floorIn_le_top S x
  · exact Int.le_refl _

theorem lastIn_mono {x y : Int} (hx : S.lo ≤ x) (h : x ≤ y) : lastIn S x ≤ lastIn S y := by
  by_cases hr : S.region x
  · have hpos : S.lo < apfTop S := by have := apfSecond_ge_lo S; have := hr.1; have := hr.2.1; omega
    have hmem := apfTop_mem S hpos
    have e : lastIn S x = apfTop S := by unfold lastIn; rw [if_pos hr]
    rw [e]
    by_cases hy : y < apfTop S
    · have hry : S.region y := ⟨by have := hr.1; omega, hy, hr.2.2⟩
      unfold lastIn; rw [if_pos hry]; exact Int.le_refl _
    · exact lastIn_ge S y hmem (by omega)
  · have e : lastIn S x = floorIn S.lo S.vals x := by unfold lastIn; rw [if_neg hr]
    rw [e]
    exact Int.le_trans (floorIn_mono S.lo S.vals hx h) (floorIn_le_lastIn S y)

theorem lastIn_mem (x : Int) : lastIn S x = S.lo ∨ lastIn S x ∈ S.vals := by
  unfold lastIn
  split
  · rename_i hr
    exact .inr (apfTop_mem S (by have := apfSecond_ge_lo S; have := hr.1; have := hr.2.1; omega))
  · exact floorIn_mem S.lo S.vals x

theorem lastIn_ge_lo (x : Int) : S.lo ≤ lastIn S x := by
  unfold lastIn
  split
  · exact apfTop_ge_lo S
  · exact floorIn_ge_base S.lo S.vals x

theorem lastIn_bound {x : Int} (hx : S.lo ≤ x) (hx' : x < S.hi) : lastIn S x < S.hi := by
  unfold lastIn
  split
  · rename_i hr; exact hr.2.2.2
  · have := floorIn_le S.lo S.vals hx; omega

/-! ### Breakpoints -/

/-- A list with each value once, the last copy kept. -/
def dedupInt : List Int → List Int
  | [] => []
  | x :: l => if x ∈ dedupInt l then dedupInt l else x :: dedupInt l

theorem mem_dedupInt {x : Int} : ∀ {l : List Int}, x ∈ dedupInt l ↔ x ∈ l
  | [] => Iff.rfl
  | y :: l => by
    unfold dedupInt
    split
    · rename_i hy
      rw [mem_dedupInt, List.mem_cons]
      exact ⟨Or.inr, fun h => h.elim (fun e => e ▸ mem_dedupInt.1 hy) id⟩
    · rw [List.mem_cons, List.mem_cons, mem_dedupInt]

/-- **Where `lastIn` may change**: `lo`, `lo + 1`, the values and their
successors, within `[lo, hi)`, each once. -/
def ApfSet.breaks (S : ApfSet) : List Int :=
  dedupInt ((S.lo :: (S.lo + 1) :: (S.vals ++ S.vals.map (· + 1))).filter
    fun b => decide (S.lo ≤ b ∧ b < S.hi))

theorem ApfSet.breaks_range {b : Int} (hb : b ∈ S.breaks) : S.lo ≤ b ∧ b < S.hi := by
  have := (List.mem_filter.1 (mem_dedupInt.1 hb)).2
  simpa only [decide_eq_true_eq] using this

theorem ApfSet.mem_breaks {b : Int} (h : b = S.lo ∨ b = S.lo + 1 ∨ b ∈ S.vals ∨ b - 1 ∈ S.vals)
    (h1 : S.lo ≤ b) (h2 : b < S.hi) : b ∈ S.breaks := by
  refine mem_dedupInt.2 (List.mem_filter.2 ⟨?_, by simp only [decide_eq_true_eq]; exact ⟨h1, h2⟩⟩)
  rcases h with rfl | rfl | h | h
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ h))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_map.2 ⟨b - 1, h, by omega⟩)))

/-- **`lastIn` is constant between breakpoints.** -/
theorem lastIn_breaks {x : Int} (hx : S.lo ≤ x)
    (hx' : x < S.hi) : lastIn S (floorIn S.lo S.breaks x) = lastIn S x := by
  have hB : ∀ b, (b = S.lo ∨ b = S.lo + 1 ∨ b ∈ S.vals ∨ b - 1 ∈ S.vals) → S.lo ≤ b → b ≤ x →
      b ≤ floorIn S.lo S.breaks x := fun b hb h1 h2 =>
    floorIn_ge S.lo S.breaks x (S.mem_breaks hb h1 (by omega)) h2
  have hp1 := floorIn_le S.lo S.breaks hx
  have hp0 := floorIn_ge_base S.lo S.breaks x
  -- the floor in the values is the same at `x` and at its breakpoint
  have hfl : floorIn S.lo S.vals (floorIn S.lo S.breaks x) = floorIn S.lo S.vals x := by
    apply Int.le_antisymm
    · exact floorIn_mono S.lo S.vals hp0 hp1
    · rcases floorIn_mem S.lo S.vals x with h | h
      · rw [h]; exact floorIn_ge_base _ _ _
      · have hle := floorIn_le S.lo S.vals hx
        have hlo := floorIn_ge_base S.lo S.vals x
        exact floorIn_ge S.lo S.vals _ h (hB _ (.inr (.inr (.inl h))) hlo hle)
  have hsec : apfSecond S < floorIn S.lo S.breaks x ↔ apfSecond S < x := by
    constructor
    · intro h; omega
    · intro h
      have := hB (apfSecond S + 1) (by
        rcases apfSecond_mem S with h' | h'
        · exact .inr (.inl (by omega))
        · exact .inr (.inr (.inr (by simpa only [Int.add_sub_cancel] using h')))) (by
          have := apfSecond_ge_lo S; omega) (by omega)
      omega
  have htop : floorIn S.lo S.breaks x < apfTop S ↔ x < apfTop S := by
    constructor
    · intro h
      apply Classical.byContradiction
      intro hn
      have := hB (apfTop S) (by
        rcases apfTop_mem' S with h' | h'
        · exact .inl h'
        · exact .inr (.inr (.inl h'))) (apfTop_ge_lo S) (by omega)
      omega
    · intro h; omega
  unfold lastIn ApfSet.region
  rw [hfl]
  by_cases hr : apfSecond S < x ∧ x < apfTop S ∧ apfTop S ∉ S.strict ∧ apfTop S < S.hi
  · rw [if_pos hr, if_pos ⟨hsec.2 hr.1, htop.2 hr.2.1, hr.2.2⟩]
  · rw [if_neg hr, if_neg fun h => hr ⟨hsec.1 h.1, htop.1 h.2.1, h.2.2⟩]

end LastIn

/-- `lastIn` at a key type. -/
def lastK {K : PrimTy} (ok : OrdK K) (S : ApfSet) (k : K.Denote) : K.Denote :=
  ok.ofInt (lastIn S (ok.val k))

theorem lastK_val {K : PrimTy} (ok : OrdK K) (S : ApfSet) (hlo : S.lo = ok.lo) (hhi : S.hi = ok.hi)
    (k : K.Denote) : ok.val (lastK ok S k) = lastIn S (ok.val k) := by
  have hk := ok.bounds k
  exact ok.val_ofInt (by rw [← hlo]; exact lastIn_ge_lo S _)
    (by rw [← hhi]; exact lastIn_bound S (by omega) (by omega))

/-! ## Regions -/

/-- The smallest value of `B` above `b`, `hi` where none is below `hi`. -/
def nextIn (hi : Int) (B : List Int) (b : Int) : Int := B.foldl (fun a s => if b < s ∧ s < a then s else a) hi

theorem nextIn_spec (B : List Int) (b : Int) : ∀ (a : Int),
    B.foldl (fun a s => if b < s ∧ s < a then s else a) a ≤ a ∧
      (b < a → b < B.foldl (fun a s => if b < s ∧ s < a then s else a) a) ∧
      (∀ s ∈ B, b < s → B.foldl (fun a s => if b < s ∧ s < a then s else a) a ≤ s) ∧
      (B.foldl (fun a s => if b < s ∧ s < a then s else a) a = a ∨
        B.foldl (fun a s => if b < s ∧ s < a then s else a) a ∈ B) := by
  induction B with
  | nil => intro a; exact ⟨Int.le_refl _, id, (fun _ h _ => nomatch h), .inl rfl⟩
  | cons s B ih =>
    intro a
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3, h4⟩ := ih (if b < s ∧ s < a then s else a)
    by_cases hc : b < s ∧ s < a
    · rw [if_pos hc] at h1 h2 h3 h4 ⊢
      refine ⟨by omega, fun _ => h2 hc.1, fun s' hs' hbs => ?_, h4.elim
        (fun h => .inr (by rw [h]; exact List.mem_cons_self)) (fun h => .inr (List.mem_cons_of_mem _ h))⟩
      rcases List.mem_cons.1 hs' with rfl | hs'
      · exact h1
      · exact h3 s' hs' hbs
    · rw [if_neg hc] at h1 h2 h3 h4 ⊢
      refine ⟨h1, h2, fun s' hs' hbs => ?_, h4.elim .inl (fun h => .inr (List.mem_cons_of_mem _ h))⟩
      rcases List.mem_cons.1 hs' with rfl | hs'
      · omega
      · exact h3 s' hs' hbs

section NextIn

variable (hi : Int) (B : List Int) (b : Int)

theorem nextIn_le : nextIn hi B b ≤ hi := (nextIn_spec B b hi).1
theorem nextIn_gt (h : b < hi) : b < nextIn hi B b := (nextIn_spec B b hi).2.1 h
theorem nextIn_le_mem {s : Int} (hs : s ∈ B) (h : b < s) : nextIn hi B b ≤ s := (nextIn_spec B b hi).2.2.1 s hs h
theorem nextIn_mem : nextIn hi B b = hi ∨ nextIn hi B b ∈ B := (nextIn_spec B b hi).2.2.2

end NextIn

/-- The keys `[b, e)`. -/
def regionKeys {K : PrimTy} (ok : OrdK K) (b e : Int) : List K.Denote :=
  (List.range (e - b).toNat).map fun (i : Nat) => ok.ofInt (b + i)

/-- **A run of entries, region by region**: for each breakpoint `b` of `B`,
the keys `[b, next b)` holding `w b`, the region left out where `skip`
says its value is the default. -/
def regionList {K : PrimTy} (ok : OrdK K) (B : List Int) {W : Type} (w : Int → W) (skip : W → Bool) :
    List (K.Denote × W) :=
  B.flatMap fun b => if skip (w b) then [] else (regionKeys ok b (nextIn ok.hi B b)).map (·, w b)

theorem lookupBy_append {κ V : Type} [DecidableEq κ] (k : κ) :
    ∀ (l₁ l₂ : List (κ × V)), lookupBy k (l₁ ++ l₂) = (lookupBy k l₁).or (lookupBy k l₂)
  | [], _ => rfl
  | (k', v) :: l₁, l₂ => by
    rw [List.cons_append, lookupBy, lookupBy]
    by_cases e : k = k'
    · rw [if_pos e, if_pos e]; rfl
    · rw [if_neg e, if_neg e]; exact lookupBy_append k l₁ l₂

/-- A run of keys holding one value: found exactly in its range. -/
theorem lookupBy_regionKeys {K : PrimTy} (ok : OrdK K) {V : Type} (v : V) (b e : Int) (k : K.Denote)
    (hb : ok.lo ≤ b) (he : e ≤ ok.hi) :
    lookupBy k ((regionKeys ok b e).map (·, v)) = if b ≤ ok.val k ∧ ok.val k < e then some v else none := by
  have key : ∀ (l : List Nat), (∀ i ∈ l, b + i < e) →
      lookupBy k ((l.map fun (i : Nat) => ok.ofInt (b + i)).map (·, v)) =
        if ∃ i ∈ l, ok.val k = b + i then some v else none := by
    intro l
    induction l with
    | nil => intro _; simp only [List.map_nil, lookupBy, List.not_mem_nil, false_and, exists_false,
        if_false]
    | cons i l ih =>
      intro hl
      have hi := hl i List.mem_cons_self
      rw [List.map_cons, List.map_cons, lookupBy, ih fun j hj => hl j (List.mem_cons_of_mem _ hj)]
      have hv : ok.val (ok.ofInt (b + (i : Int))) = b + i := ok.val_ofInt (by omega) (by omega)
      by_cases h : k = ok.ofInt (b + i)
      · rw [if_pos h, if_pos ⟨i, List.mem_cons_self, by rw [h, hv]⟩]
      · rw [if_neg h]
        have hn : ok.val k ≠ b + i := fun e' => h (ok.ext (by rw [e', hv]))
        congr 1
        apply propext
        constructor
        · rintro ⟨j, hj, e'⟩; exact ⟨j, List.mem_cons_of_mem _ hj, e'⟩
        · rintro ⟨j, hj, e'⟩
          rcases List.mem_cons.1 hj with rfl | hj
          · exact absurd e' hn
          · exact ⟨j, hj, e'⟩
  unfold regionKeys
  rw [key _ fun i hi => by have := List.mem_range.1 hi; omega]
  congr 1
  apply propext
  constructor
  · rintro ⟨i, hi, e'⟩
    have := List.mem_range.1 hi
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨(ok.val k - b).toNat, List.mem_range.2 (by omega), by omega⟩

/-- **A read in a region list finds its key's last breakpoint's region**, and
nothing where that region is skipped. -/
theorem lookupBy_regionList {K : PrimTy} (ok : OrdK K) (B : List Int) {W : Type} (w : Int → W)
    (skip : W → Bool) (hB : ∀ b ∈ B, ok.lo ≤ b ∧ b < ok.hi) (hlo : ok.lo ∈ B) (k : K.Denote) :
    lookupBy k (regionList ok B w skip) =
      if skip (w (floorIn ok.lo B (ok.val k))) then none else some (w (floorIn ok.lo B (ok.val k))) := by
  have hk := ok.bounds k
  have hp := floorIn_le ok.lo B hk.1
  have hp0 := floorIn_ge_base ok.lo B (ok.val k)
  -- the regions of the other breakpoints miss the key
  have hmiss : ∀ b ∈ B, b ≠ floorIn ok.lo B (ok.val k) → ¬ (b ≤ ok.val k ∧ ok.val k < nextIn ok.hi B b) := by
    intro b hb hne ⟨h1, h2⟩
    have hle := floorIn_ge ok.lo B (ok.val k) hb h1
    have hlt : b < floorIn ok.lo B (ok.val k) := by omega
    rcases floorIn_mem ok.lo B (ok.val k) with he | hm
    · have := (hB b hb).1; omega
    · have := nextIn_le_mem ok.hi B b hm hlt
      omega
  -- the key's own region holds it
  have hhit : ∀ b ∈ B, b = floorIn ok.lo B (ok.val k) → b ≤ ok.val k ∧ ok.val k < nextIn ok.hi B b := by
    intro b hbB he
    refine ⟨he ▸ hp, ?_⟩
    have h1 : b < nextIn ok.hi B b := nextIn_gt ok.hi B b (hB b hbB).2
    rcases nextIn_mem ok.hi B b with hn | hn
    · rw [hn]; exact hk.2
    · apply Classical.byContradiction
      intro hc
      have := floorIn_ge ok.lo B (ok.val k) hn (by omega)
      omega
  have go : ∀ (l : List Int), (∀ b ∈ l, b ∈ B) →
      lookupBy k (l.flatMap fun b => if skip (w b) then [] else
          (regionKeys ok b (nextIn ok.hi B b)).map (·, w b)) =
        if floorIn ok.lo B (ok.val k) ∈ l ∧ skip (w (floorIn ok.lo B (ok.val k))) = false then
          some (w (floorIn ok.lo B (ok.val k))) else none := by
    intro l
    induction l with
    | nil => intro _; simp only [List.flatMap_nil, lookupBy, List.not_mem_nil, false_and, if_false]
    | cons b l ih =>
      intro hl
      have hbB := hl b List.mem_cons_self
      rw [List.flatMap_cons, lookupBy_append, ih fun c hc => hl c (List.mem_cons_of_mem _ hc)]
      have hnext : nextIn ok.hi B b ≤ ok.hi := nextIn_le ok.hi B b
      by_cases he : b = floorIn ok.lo B (ok.val k)
      · subst he
        by_cases hs : skip (w (floorIn ok.lo B (ok.val k))) = true
        · rw [if_pos hs]
          simp only [lookupBy, hs, Bool.true_eq_false, and_false, if_false, Option.none_or]
        · rw [if_neg hs, lookupBy_regionKeys ok _ _ _ k (hB _ hbB).1 hnext,
            if_pos (hhit _ hbB rfl)]
          rw [Option.some_or, if_pos ⟨List.mem_cons_self, by simpa only [Bool.not_eq_true] using hs⟩]
      · have hr : lookupBy k (if skip (w b) = true then [] else
            (regionKeys ok b (nextIn ok.hi B b)).map (·, w b)) = none := by
          split
          · rfl
          · rw [lookupBy_regionKeys ok _ _ _ k (hB _ hbB).1 hnext, if_neg (hmiss b hbB he)]
        rw [hr, Option.none_or]
        congr 1
        apply propext
        constructor
        · rintro ⟨hm, hs⟩; exact ⟨List.mem_cons_of_mem _ hm, hs⟩
        · rintro ⟨hm, hs⟩
          rcases List.mem_cons.1 hm with h' | hm
          · exact absurd h'.symm he
          · exact ⟨hm, hs⟩
  unfold regionList
  rw [go B fun b hb => hb]
  by_cases hs : skip (w (floorIn ok.lo B (ok.val k))) = true
  · rw [if_pos hs, if_neg fun h => by rw [hs] at h; exact Bool.noConfusion h.2]
  · rw [if_neg hs]
    have hmem : floorIn ok.lo B (ok.val k) ∈ B := by
      rcases floorIn_mem ok.lo B (ok.val k) with h | h
      · rw [h]; exact hlo
      · exact h
    rw [if_pos ⟨hmem, by simpa only [Bool.not_eq_true] using hs⟩]

end Solidity.Decide
