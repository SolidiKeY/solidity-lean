import Solidity.Calculus.Closer.Normal

/-!
# The closer's normal forms: bytes reassembled

Normal forms, continued: bytes reassembled into words (Lean only), and the
rest of the section.

A piece of `Calculus/Closer.lean`, whose docstring describes the whole.
-/

namespace Solidity

namespace Decide

variable {C : Contract}

section Normal

variable {g : State C []} {ν : AEnv}

/-! ### Bytes reassembled (Lean only)

An ABI encoding writes a word byte by byte, `(x >> 8k) % 256`; reading
the bytes back by Horner's rule, `r * 256 + b`, reassembles the word:
`hornerU?` reads `((q >> k) % 2^w) * 2^k + q % 2^k` as `q % 2^(w+k)`,
`shrZeroU?` reads `x >> 0` as `x`, and `modModU?` reads `(t % m) % n` as
`t % n` where `n` divides `m` (a `uint8(…)` of a byte).  No solkey taclet
reads bytes (KeY has no byte layout). -/

theorem Int.emod_mul_split (x a b : Int) (ha : 0 < a) :
    x % (a * b) = x % a + a * (x / a % b) := by
  have h1 := Int.mul_ediv_add_emod x a
  have h2 := Int.mul_ediv_add_emod (x / a) b
  have h3 : x / (a * b) = x / a / b := (Int.ediv_ediv (by omega)).symm
  have h4 := Int.mul_ediv_add_emod x (a * b)
  rw [h3] at h4
  grind

theorem emod_pow_ediv (a : Int) (m k w : Nat) (hm : k + w ≤ m) :
    a % 2 ^ m / 2 ^ k % 2 ^ w = a / 2 ^ k % 2 ^ w := by
  have h2k : (2 : Int) ^ k ≠ 0 := Int.ne_of_gt (Int.pow_pos (by decide))
  have hsplit : (2 : Int) ^ m = 2 ^ k * (2 ^ w * 2 ^ (m - k - w)) := by
    rw [← Int.pow_add, ← Int.pow_add]; congr 1; omega
  have ha := Int.emod_add_mul_ediv a (2 ^ m)
  conv => rhs; rw [← ha]
  rw [hsplit, Int.mul_assoc, Int.add_mul_ediv_left _ _ h2k, Int.mul_assoc, Int.add_mul_emod_self_left]

/-- The operands of `op` at `uint`. -/
def Op2.uArgs (op : BinOp) {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) :
    Option (LTm C (.val .uint) × LTm C (.val .uint)) :=
  match o, x, y with
  | @Op2.binop _ op' p _, x, y =>
    if op' == op then
      match p with
      | .uint => some (x, y)
      | _ => none
    else none
  | _, _, _ => none

/-- The operands of `t`, an `op` at `uint`. -/
def LTm.uArgs? (op : BinOp) {s : Srt} (t : LTm C s) :
    Option (LTm C (.val .uint) × LTm C (.val .uint)) :=
  match t with
  | .app2 o x y => Op2.uArgs op o x y
  | _ => none

theorem LTm.uArgs?_eq {op : BinOp} {s : Srt} {t : LTm C s} {l r : LTm C (.val .uint)}
    (h : t.uArgs? op = some (l, r)) :
    ∃ hp : op.accepts .uint = true,
      (⟨s, t⟩ : (s : Srt) × LTm C s) = ⟨.val (op.ret .uint), .app2 (.binop op hp) l r⟩ := by
  cases t with
  | app2 o x y =>
    cases o with
    | @binop op' p hp =>
      simp only [LTm.uArgs?, Op2.uArgs] at h
      split at h
      · rename_i he
        have := eq_of_beq he
        subst this
        cases p <;> simp only [reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hp, rfl⟩
      · cases h
    | _ => simp only [LTm.uArgs?, Op2.uArgs, reduceCtorEq] at h
  | _ => simp only [LTm.uArgs?, reduceCtorEq] at h

/-- A `uint` literal's integer. -/
def LTm.uLit? (t : LTm C (.val .uint)) : Option Int := t.litV?.map (·.1)

theorem LTm.eq_of_uLit? {t : LTm C (.val .uint)} {n : Int} (h : t.uLit? = some n) :
    ∃ v : PrimTy.uint.Denote, v.1 = n ∧ t = .lit v := by
  unfold LTm.uLit? at h
  cases hv : t.litV? with
  | none => rw [hv] at h; cases h
  | some v =>
    rw [hv] at h
    cases h
    exact ⟨v, rfl, LTm.eq_of_litV? hv⟩

/-- The exponent `k` of `n = pw * 2 ^ j` with `k = i + j`, searched from
`i` with `pw = 2 ^ i`, within `f` doublings (structural, for the kernel). -/
def log2Go (n : Int) : Nat → Nat → Int → Option Nat
  | 0, _, _ => none
  | f + 1, i, pw => if n = pw then some i else if n < pw then none else log2Go n f (i + 1) (pw * 2)

theorem log2Go_eq {n : Int} : ∀ {f i : Nat} {pw : Int} {k : Nat}, pw = 2 ^ i →
    log2Go n f i pw = some k → n = 2 ^ k
  | 0, _, _, _, _, h => by cases h
  | f + 1, i, pw, k, hpw, h => by
    unfold log2Go at h
    split at h
    · rename_i he; cases h; rw [he, hpw]
    · split at h
      · cases h
      · exact log2Go_eq (f := f) (i := i + 1) (by rw [hpw, Int.pow_succ]) h

/-- The exponent `k` with `2 ^ k = n`, for a power of two below `2 ^ 256`. -/
def log2Exact (n : Int) : Option Nat :=
  match log2Go n 257 0 1 with
  | some k => if k ≤ 256 then some k else none
  | none => none

theorem log2Exact_eq {n : Int} {k : Nat} (h : log2Exact n = some k) : n = 2 ^ k ∧ k ≤ 256 := by
  unfold log2Exact at h
  split at h
  · rename_i k' hk
    split at h
    · cases h; exact ⟨log2Go_eq (by rfl) hk, by assumption⟩
    · cases h
  · cases h

theorem eval_uop (op : BinOp) (hp : op.accepts .uint = true) (hs : ∀ a : PrimTy.uint.Denote, op.shortT a = none)
    (x y : LTm C (.val .uint)) :
    (LTm.app2 (.binop op hp) x y).eval g ν =
      (x.eval g ν).bind fun a => (y.eval g ν).bind fun b => BinOp.evalT op hp a b := by
  rw [LTm.eval_app2, Op2.eval_eq_evalM]
  cases x.eval g ν with
  | none => rfl
  | some a =>
    simp only [Op2.evalM, Option.bind_some]
    unfold binopT
    rw [hs a]

theorem uint_ofInt?_ival (v : PrimTy.uint.Denote) : PrimTy.uint.ofInt? v.1 = some v :=
  ofInt?_ival_self rfl v

theorem uint_nonneg (v : PrimTy.uint.Denote) : 0 ≤ v.1 := by
  have h := v.2
  simp only [PrimTy.inRange, decide_eq_true_eq] at h
  exact h.1

theorem uint_lt (v : PrimTy.uint.Denote) : v.1 < 2 ^ 256 := by
  have h := v.2
  simp only [PrimTy.inRange, decide_eq_true_eq] at h
  exact_mod_cast h.2

/-- `x >> 0` is `x`. -/
theorem eval_shr_zero (hp : BinOp.shr.accepts .uint = true) (x : LTm C (.val .uint))
    (c : PrimTy.uint.Denote) (hc : c.1 = 0) :
    ((LTm.app2 (.binop .shr hp) x (.lit c)).eval g ν : Option PrimTy.uint.Denote) = x.eval g ν := by
  rw [eval_uop .shr hp (fun _ => rfl)]
  cases x.eval g ν with
  | none => rfl
  | some a =>
    show (BinOp.arithInt .shr a.1 c.1).bind PrimTy.uint.ofInt? = some a
    simp only [BinOp.arithInt, hc, Int.toNat_zero, Int.pow_zero, Int.ediv_one]
    simp only [show (0 : Int) < 256 from by decide, if_true, Option.bind_some]
    exact uint_ofInt?_ival a

/-- `(t % m) % n` is `t % n` where `n` divides `m`. -/
theorem eval_mod_mod (hp : BinOp.mod.accepts .uint = true) (hp' : BinOp.mod.accepts .uint = true)
    (t : LTm C (.val .uint)) (m n : PrimTy.uint.Denote) (hn : 0 < n.1) (hm : 0 < m.1)
    (hd : m.1 % n.1 = 0) :
    ((LTm.app2 (.binop .mod hp') (LTm.app2 (.binop .mod hp) t (.lit m)) (.lit n)).eval g ν :
      Option PrimTy.uint.Denote) = (LTm.app2 (.binop .mod hp) t (.lit n)).eval g ν := by
  rw [eval_uop .mod hp' (fun _ => rfl), eval_uop .mod hp (fun _ => rfl),
    eval_uop .mod hp (fun _ => rfl)]
  cases ht : t.eval g ν with
  | none => rfl
  | some a =>
    have ha := uint_nonneg a
    show ((BinOp.arithInt .mod a.1 m.1).bind PrimTy.uint.ofInt?).bind
        (fun b => (BinOp.arithInt .mod b.1 n.1).bind PrimTy.uint.ofInt?) =
      (BinOp.arithInt .mod a.1 n.1).bind PrimTy.uint.ofInt?
    simp only [BinOp.arithInt, if_neg (Int.ne_of_gt hm), if_neg (Int.ne_of_gt hn), Option.bind_some]
    cases hw : PrimTy.uint.ofInt? (Int.tmod a.1 m.1) with
    | none =>
      exfalso
      rw [Int.tmod_eq_emod_of_nonneg ha] at hw
      have h1 := Int.emod_nonneg a.1 (Int.ne_of_gt hm)
      have h2 := Int.emod_lt_of_pos a.1 hm
      have h3 := uint_lt m
      simp only [PrimTy.ofInt?, PrimTy.inRange] at hw
      split at hw
      · cases hw
      · rename_i hh; apply hh; simp only [decide_eq_true_eq]; constructor <;> omega
    | some w =>
      simp only [Option.bind_some]
      have hw1 := ofInt?_ival hw
      simp only [PrimTy.ival] at hw1
      congr 1
      rw [hw1, Int.tmod_eq_emod_of_nonneg ha, Int.tmod_eq_emod_of_nonneg (Int.emod_nonneg _ (Int.ne_of_gt hm)),
        Int.tmod_eq_emod_of_nonneg ha]
      exact Int.emod_emod_of_dvd _ (Int.dvd_of_emod_eq_zero hd)

theorem uint_ofInt?_some {n : Int} (h0 : 0 ≤ n) (h1 : n < 2 ^ 256) :
    ∃ v : PrimTy.uint.Denote, PrimTy.uint.ofInt? n = some v ∧ v.1 = n := by
  have hr : PrimTy.uint.inRange n = true := by
    simp only [PrimTy.inRange, decide_eq_true_eq]; exact ⟨h0, by exact_mod_cast h1⟩
  refine ⟨⟨n, hr⟩, ?_, rfl⟩
  simp only [PrimTy.ofInt?, dif_pos hr]

/-- **Horner's step on bytes**: `((q >> k) % 2^w) * 2^k + q % 2^k` is
`q % 2^(w+k)`, `S` a term reading `q >> k` modulo `2^w` (`hS`). -/
theorem eval_horner (hm : BinOp.mod.accepts .uint = true) (hm' : BinOp.mod.accepts .uint = true)
    (hmul : BinOp.mul.accepts .uint = true) (ha : BinOp.add.accepts .uint = true)
    (S s : LTm C (.val .uint)) (W K K' L : PrimTy.uint.Denote) (w k : Nat)
    (hW : W.1 = 2 ^ w) (hK : K.1 = 2 ^ k) (hK' : K'.1 = 2 ^ k) (hL : L.1 = 2 ^ (w + k))
    (hwk : w + k < 256)
    (hS : (S.eval g ν).map (fun v => v.1 % 2 ^ w) = (s.eval g ν).map (fun q => q.1 / 2 ^ k % 2 ^ w)) :
    ((LTm.app2 (.binop .add ha) (LTm.app2 (.binop .mul hmul) (LTm.app2 (.binop .mod hm) S (.lit W))
        (.lit K)) (LTm.app2 (.binop .mod hm') s (.lit K'))).eval g ν : Option PrimTy.uint.Denote) =
      (LTm.app2 (.binop .mod hm') s (.lit L)).eval g ν := by
  rw [eval_uop .add ha (fun _ => rfl), eval_uop .mul hmul (fun _ => rfl),
    eval_uop .mod hm (fun _ => rfl), eval_uop .mod hm' (fun _ => rfl),
    eval_uop .mod hm' (fun _ => rfl)]
  have h2k : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
  have h2w : (0 : Int) < 2 ^ w := Int.pow_pos (by decide)
  have hwk' : (2 : Int) ^ (w + k) = 2 ^ k * 2 ^ w := by rw [Int.pow_add, Int.mul_comm]
  have hbig : (2 : Int) ^ k * 2 ^ w < 2 ^ 256 := by
    rw [← hwk']
    have : (2 : Nat) ^ (w + k) < 2 ^ 256 := Nat.pow_lt_pow_right (by decide) hwk
    exact_mod_cast this
  have hw1 : (1 : Int) ≤ 2 ^ w := h2w
  have e7 : (2 : Int) ^ k ≤ 2 ^ k * 2 ^ w := by
    have := Int.mul_le_mul_of_nonneg_left hw1 (Int.le_of_lt h2k)
    rwa [Int.mul_one] at this
  have e8 : (2 : Int) ^ w ≤ 2 ^ k * 2 ^ w := by
    have := Int.mul_le_mul_of_nonneg_right (show (1 : Int) ≤ 2 ^ k from h2k) (Int.le_of_lt h2w)
    rwa [Int.one_mul] at this
  cases hs : s.eval g ν with
  | none =>
    rw [hs, Option.map_none] at hS
    cases hS' : S.eval g ν with
    | none => rfl
    | some v => rw [hS', Option.map_some] at hS; cases hS
  | some q =>
    rw [hs, Option.map_some] at hS
    cases hS' : S.eval g ν with
    | none => rw [hS', Option.map_none] at hS; cases hS
    | some v =>
      rw [hS', Option.map_some, Option.some.injEq] at hS
      have hq := uint_nonneg q
      have hv := uint_nonneg v
      simp only [Option.bind_some]
      show (((BinOp.arithInt .mod v.1 W.1).bind PrimTy.uint.ofInt?).bind fun a =>
          (BinOp.arithInt .mul a.1 K.1).bind PrimTy.uint.ofInt?).bind (fun a =>
          ((BinOp.arithInt .mod q.1 K'.1).bind PrimTy.uint.ofInt?).bind fun b =>
            (BinOp.arithInt .add a.1 b.1).bind PrimTy.uint.ofInt?) =
        (BinOp.arithInt .mod q.1 L.1).bind PrimTy.uint.ofInt?
      simp only [BinOp.arithInt, hW, hK, hK', hL, if_neg (Int.ne_of_gt h2w), if_neg (Int.ne_of_gt h2k),
        if_neg (Int.ne_of_gt (Int.pow_pos (by decide) : (0 : Int) < 2 ^ (w + k))), Option.bind_some]
      rw [Int.tmod_eq_emod_of_nonneg hv, Int.tmod_eq_emod_of_nonneg hq, Int.tmod_eq_emod_of_nonneg hq]
      have e1 := Int.emod_nonneg v.1 (Int.ne_of_gt h2w)
      have e2 := Int.emod_lt_of_pos v.1 h2w
      obtain ⟨a1, ha1, ha1v⟩ := uint_ofInt?_some (n := v.1 % 2 ^ w) e1 (by omega)
      rw [ha1, Option.bind_some, ha1v]
      have e3 : v.1 % 2 ^ w * 2 ^ k < 2 ^ k * 2 ^ w := by
        rw [Int.mul_comm]; exact Int.mul_lt_mul_of_pos_left e2 h2k
      have e4 : 0 ≤ v.1 % 2 ^ w * 2 ^ k := Int.mul_nonneg e1 (Int.le_of_lt h2k)
      obtain ⟨a2, ha2, ha2v⟩ := uint_ofInt?_some (n := v.1 % 2 ^ w * 2 ^ k) e4 (by omega)
      rw [ha2, Option.bind_some]
      have e5 := Int.emod_nonneg q.1 (Int.ne_of_gt h2k)
      have e6 := Int.emod_lt_of_pos q.1 h2k
      obtain ⟨a3, ha3, ha3v⟩ := uint_ofInt?_some (n := q.1 % 2 ^ k) e5 (by omega)
      rw [ha3, Option.bind_some, ha2v, ha3v]
      congr 1
      rw [hwk', Int.emod_mul_split q.1 _ _ h2k, ← hS]
      rw [Int.mul_comm (v.1 % 2 ^ w), Int.add_comm]

/-- `x >> c` at `uint`, `c` a literal below 256: `x` divided by `2^c`. -/
theorem eval_shr_lit (hp : BinOp.shr.accepts .uint = true) (x : LTm C (.val .uint))
    (c : PrimTy.uint.Denote) (hc : c.1 < 256) :
    ((LTm.app2 (.binop .shr hp) x (.lit c)).eval g ν : Option PrimTy.uint.Denote).map (·.1) =
      (x.eval g ν).map (fun a => a.1 / 2 ^ c.1.toNat) := by
  rw [eval_uop .shr hp (fun _ => rfl)]
  cases x.eval g ν with
  | none => rfl
  | some a =>
    show ((BinOp.arithInt .shr a.1 c.1).bind PrimTy.uint.ofInt?).map (·.1) = some (a.1 / 2 ^ c.1.toNat)
    simp only [BinOp.arithInt, if_pos hc, Option.bind_some]
    have ha := uint_nonneg a
    have h2 : (0 : Int) < 2 ^ c.1.toNat := Int.pow_pos (by decide)
    have h1 : a.1 / 2 ^ c.1.toNat ≤ a.1 := Int.ediv_le_self _ ha
    obtain ⟨v, hv, hvv⟩ := uint_ofInt?_some (n := a.1 / 2 ^ c.1.toNat)
      (Int.ediv_nonneg ha (Int.le_of_lt h2)) (by have := uint_lt a; omega)
    rw [hv, Option.map_some, hvv]

/-- `S` reads `s >> k`: `S` is `s >> k`, or `t >> (j + k)` where `s` is `t >> j`. -/
def shrMatchAB (S s : LTm C (.val .uint)) (k : Nat) : Bool :=
  match S.uArgs? .shr with
  | some (u, jl) =>
    match jl.uLit? with
    | some J =>
      (u.beqR s && J == (k : Int)) ||
      (match s.uArgs? .shr with
        | some (t, jl') =>
          match jl'.uLit? with
          | some j => u.beqR t && J == j + k && decide (0 ≤ j) && decide (J < 256)
          | none => false
        | none => false)
    | none => false
  | none => false

theorem shrMatchAB_sound {S s : LTm C (.val .uint)} {k : Nat} (h : shrMatchAB S s k = true)
    (hk : k < 256) :
    (S.eval g ν).map (·.1) = (s.eval g ν).map (fun q => q.1 / 2 ^ k) := by
  unfold shrMatchAB at h
  split at h
  · rename_i u jl hS
    obtain ⟨hp, hSe⟩ := LTm.uArgs?_eq hS
    cases hSe
    split at h
    · rename_i J hJ
      obtain ⟨Jv, hJv, rfl⟩ := LTm.eq_of_uLit? hJ
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨hu, hk'⟩ | h
      · cases LTm.eq_of_beqR hu
        refine (eval_shr_lit hp _ Jv (by omega)).trans ?_
        simp only [hJv, hk', Int.toNat_natCast]
      · split at h
        · rename_i t jl' hs
          obtain ⟨hp', hse⟩ := LTm.uArgs?_eq hs
          cases hse
          split at h
          · rename_i j hj
            obtain ⟨jv, hjv, rfl⟩ := LTm.eq_of_uLit? hj
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
            obtain ⟨⟨⟨hu, hJ'⟩, hj0⟩, hJ256⟩ := h
            cases LTm.eq_of_beqR hu
            refine (eval_shr_lit hp _ Jv (by omega)).trans ?_
            rw [hJv]
            have hjl : jv.1 < 256 := by omega
            have e := eval_shr_lit (g := g) (ν := ν) hp' u jv hjl
            cases ht : u.eval g ν with
            | none =>
              rw [ht, Option.map_none] at e
              cases hs' : (LTm.app2 (.binop .shr hp') u (.lit jv)).eval g ν with
              | none => rfl
              | some _ => rw [hs', Option.map_some] at e; cases e
            | some a =>
              rw [ht, Option.map_some] at e
              cases hs' : ((LTm.app2 (.binop .shr hp') u (.lit jv)).eval g ν : Option PrimTy.uint.Denote) with
              | none => rw [hs', Option.map_none] at e; cases e
              | some b =>
                rw [hs', Option.map_some, Option.some.injEq] at e
                simp only [Option.map_some, e, hJ']
                have h2j : (0 : Int) ≤ 2 ^ jv.1.toNat := Int.le_of_lt (Int.pow_pos (by decide))
                rw [Int.ediv_ediv h2j, ← Int.pow_add]
                congr 3
                omega
          · cases h
        · cases h
    · cases h
  · cases h

/-- `x % c` at `uint`, `c` a positive literal. -/
theorem eval_mod_lit (hp : BinOp.mod.accepts .uint = true) (x : LTm C (.val .uint))
    (c : PrimTy.uint.Denote) (hc : 0 < c.1) :
    ((LTm.app2 (.binop .mod hp) x (.lit c)).eval g ν : Option PrimTy.uint.Denote).map (·.1) =
      (x.eval g ν).map (fun a => a.1 % c.1) := by
  rw [eval_uop .mod hp (fun _ => rfl)]
  cases x.eval g ν with
  | none => rfl
  | some a =>
    show ((BinOp.arithInt .mod a.1 c.1).bind PrimTy.uint.ofInt?).map (·.1) = some (a.1 % c.1)
    have ha := uint_nonneg a
    simp only [BinOp.arithInt, if_neg (Int.ne_of_gt hc), Option.bind_some,
      Int.tmod_eq_emod_of_nonneg ha]
    obtain ⟨v, hv, hvv⟩ := uint_ofInt?_some (n := a.1 % c.1) (Int.emod_nonneg _ (Int.ne_of_gt hc))
      (by have := Int.emod_lt_of_pos a.1 hc; have := uint_lt c; omega)
    rw [hv, Option.map_some, hvv]

/-- `S` reads `s >> k` modulo `2^w`: by `shrMatchAB`, or `S` is
`(s % 2^m) >> k` with `k + w <= m` (a narrowed word). -/
def shrMatch (S s : LTm C (.val .uint)) (k w : Nat) : Bool :=
  shrMatchAB S s k ||
  (match S.uArgs? .shr with
    | some (u, jl) =>
      match jl.uLit?, u.uArgs? .mod with
      | some J, some (s', ml) =>
        match ml.uLit? with
        | some M =>
          match log2Exact M with
          | some m => s'.beqR s && J == (k : Int) && decide (k + w ≤ m)
          | none => false
        | none => false
      | _, _ => false
    | none => false)

theorem shrMatch_sound {S s : LTm C (.val .uint)} {k w : Nat} (h : shrMatch S s k w = true)
    (hk : k < 256) :
    (S.eval g ν).map (fun v => v.1 % 2 ^ w) = (s.eval g ν).map (fun q => q.1 / 2 ^ k % 2 ^ w) := by
  unfold shrMatch at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · have e := congrArg (Option.map (· % (2 : Int) ^ w)) (shrMatchAB_sound (g := g) (ν := ν) h hk)
    simp only [Option.map_map] at e
    exact e
  · split at h
    · rename_i u jl hS
      obtain ⟨hp, hSe⟩ := LTm.uArgs?_eq hS
      cases hSe
      split at h
      · rename_i J s' ml hJ hu
        obtain ⟨Jv, hJv, rfl⟩ := LTm.eq_of_uLit? hJ
        obtain ⟨hm, hue⟩ := LTm.uArgs?_eq hu
        cases hue
        split at h
        · rename_i M hM
          obtain ⟨Mv, hMv, rfl⟩ := LTm.eq_of_uLit? hM
          split at h
          · rename_i m hm'
            obtain ⟨hm1, -⟩ := log2Exact_eq hm'
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
            obtain ⟨⟨hb, hJk⟩, hkw⟩ := h
            cases LTm.eq_of_beqR hb
            have e1 := eval_shr_lit (g := g) (ν := ν) hp (LTm.app2 (.binop .mod hm) s (.lit Mv)) Jv
              (by omega)
            have hM0 : 0 < Mv.1 := by rw [hMv, hm1]; exact Int.pow_pos (by decide)
            have e2 := eval_mod_lit (g := g) (ν := ν) hm s Mv hM0
            have e1' := congrArg (Option.map (· % (2 : Int) ^ w)) e1
            simp only [Option.map_map] at e1'
            refine e1'.trans ?_
            cases hs : s.eval g ν with
            | none =>
              rw [hs, Option.map_none] at e2
              cases hu' : ((LTm.app2 (.binop .mod hm) s (.lit Mv)).eval g ν : Option PrimTy.uint.Denote) with
              | none => rfl
              | some _ => rw [hu', Option.map_some] at e2; cases e2
            | some a =>
              rw [hs, Option.map_some] at e2
              cases hu' : ((LTm.app2 (.binop .mod hm) s (.lit Mv)).eval g ν : Option PrimTy.uint.Denote) with
              | none => rw [hu', Option.map_none] at e2; cases e2
              | some b =>
                rw [hu', Option.map_some, Option.some.injEq] at e2
                simp only [Option.map_some, Function.comp, e2, hJv, hJk, Int.toNat_natCast, hMv, hm1]
                exact congrArg some (emod_pow_ediv a.1 m k w hkw)
          · cases h
        · cases h
      · cases h
    · cases h

/-- `x >> 0` read as `x`, at `uint` (Lean only). -/
def shrZeroU? (x y : LTm C (.val .uint)) : Option (LTm C (.val .uint)) :=
  match y.uLit? with
  | some n => if n == 0 then some x else none
  | none => none

theorem shrZeroU?_eval (hp : BinOp.shr.accepts .uint = true) {x y a : LTm C (.val .uint)}
    (h : shrZeroU? x y = some a) :
    (a.eval g ν : Option PrimTy.uint.Denote) = (LTm.app2 (.binop .shr hp) x y).eval g ν := by
  unfold shrZeroU? at h
  split at h
  · rename_i n hn
    obtain ⟨v, hv, rfl⟩ := LTm.eq_of_uLit? hn
    split at h
    · rename_i h0
      cases h
      exact (eval_shr_zero hp x v (hv.trans (eq_of_beq h0))).symm
    · cases h
  · cases h

/-- `(t % m) % n` read as `t % n` where `n` divides `m`, at `uint` (Lean only). -/
def modModU? (x y : LTm C (.val .uint)) : Option (LTm C (.val .uint)) :=
  match x.uArgs? .mod, y.uLit? with
  | some (t, ml), some n =>
    match ml.uLit? with
    | some m => if decide (0 < n) && decide (0 < m) && m % n == 0 then
        some (.app2 (.binop .mod rfl) t y) else none
    | none => none
  | _, _ => none

theorem modModU?_eval (hp : BinOp.mod.accepts .uint = true) {x y a : LTm C (.val .uint)}
    (h : modModU? x y = some a) :
    (a.eval g ν : Option PrimTy.uint.Denote) = (LTm.app2 (.binop .mod hp) x y).eval g ν := by
  unfold modModU? at h
  split at h
  · rename_i t ml n hx hn
    obtain ⟨hp', hxe⟩ := LTm.uArgs?_eq hx
    cases hxe
    obtain ⟨nv, hnv, rfl⟩ := LTm.eq_of_uLit? hn
    split at h
    · rename_i m hm
      obtain ⟨mv, hmv, rfl⟩ := LTm.eq_of_uLit? hm
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
        obtain ⟨⟨hn0, hm0⟩, hd⟩ := hc
        exact (eval_mod_mod hp' hp t mv nv (by omega) (by omega) (by rw [hmv, hnv]; exact hd)).symm
      · cases h
    · cases h
  · cases h

/-- **Horner's step on bytes** (Lean only): `((q >> k) % 2^w) * 2^k + q % 2^k`
read as `q % 2^(w+k)`, at `uint`, `w + k < 256`. -/
def hornerU? (x y : LTm C (.val .uint)) : Option (LTm C (.val .uint)) :=
  match x.uArgs? .mul, y.uArgs? .mod with
  | some (xm, kl), some (s, kl') =>
    match xm.uArgs? .mod with
    | some (S, wl) =>
      match kl.uLit?, kl'.uLit?, wl.uLit? with
      | some K, some K', some W =>
        match log2Exact K, log2Exact W with
        | some k, some w =>
          if K' == K && decide (w + k < 256) && shrMatch S s k w then
            match PrimTy.uint.ofInt? (W * K) with
            | some L =>
              match modModU? s (.lit L) with
              | some t => some t
              | none => some (.app2 (.binop .mod rfl) s (.lit L))
            | none => none
          else none
        | _, _ => none
      | _, _, _ => none
    | none => none
  | _, _ => none

theorem hornerU?_eval (ha : BinOp.add.accepts .uint = true) {x y a : LTm C (.val .uint)}
    (h : hornerU? x y = some a) :
    (a.eval g ν : Option PrimTy.uint.Denote) = (LTm.app2 (.binop .add ha) x y).eval g ν := by
  unfold hornerU? at h
  split at h
  · rename_i xm kl s kl' hx hy
    obtain ⟨hmul, hxe⟩ := LTm.uArgs?_eq hx
    cases hxe
    obtain ⟨hm', hye⟩ := LTm.uArgs?_eq hy
    cases hye
    split at h
    · rename_i S wl hxm
      obtain ⟨hm, hxme⟩ := LTm.uArgs?_eq hxm
      cases hxme
      split at h
      · rename_i K K' W hK hK' hW
        obtain ⟨Kv, hKv, rfl⟩ := LTm.eq_of_uLit? hK
        obtain ⟨K'v, hK'v, rfl⟩ := LTm.eq_of_uLit? hK'
        obtain ⟨Wv, hWv, rfl⟩ := LTm.eq_of_uLit? hW
        split at h
        · rename_i k w hk hw
          obtain ⟨hk1, -⟩ := log2Exact_eq hk
          obtain ⟨hw1, -⟩ := log2Exact_eq hw
          split at h
          · rename_i hc
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
            obtain ⟨⟨hKK, hwk⟩, hsm⟩ := hc
            split at h
            · rename_i L hL
              have hLv := ofInt?_ival hL
              simp only [PrimTy.ival] at hLv
              have e := (eval_horner (g := g) (ν := ν) hm hm' hmul ha S s Wv Kv K'v L w k
                (by rw [hWv, hw1]) (by rw [hKv, hk1]) (by rw [hK'v, hKK, hk1])
                (by rw [hLv, hw1, hk1, Int.pow_add]) hwk (shrMatch_sound hsm (by omega))).symm
              split at h
              · rename_i t ht
                cases h
                exact (modModU?_eval hm' ht).trans e
              · cases h
                exact e
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

theorem uint_opt_ext {a b : Option PrimTy.uint.Denote}
    (h : a.map (·.1) = b.map (·.1)) : a = b := by
  cases a <;> cases b <;> simp only [Option.map_none, Option.map_some, reduceCtorEq,
    Option.some.injEq] at h ⊢
  exact Subtype.ext h

/-- `((t % 2^m) >> j) % 2^w` read as `(t >> j) % 2^w` where `j + w <= m`, at
`uint` (Lean only): a byte of a narrowed word. -/
def modShrModU? (x y : LTm C (.val .uint)) : Option (LTm C (.val .uint)) :=
  match x.uArgs? .shr, y.uLit? with
  | some (u, jl), some W =>
    match u.uArgs? .mod, jl.uLit? with
    | some (t, ml), some j =>
      match ml.uLit? with
      | some M =>
        match log2Exact M, log2Exact W with
        | some m, some w =>
          if decide (0 ≤ j) && decide (j < 256) && decide (j + w ≤ m) then
            some (.app2 (.binop .mod rfl) (.app2 (.binop .shr rfl) t jl) y)
          else none
        | _, _ => none
      | none => none
    | _, _ => none
  | _, _ => none

theorem modShrModU?_eval (hp : BinOp.mod.accepts .uint = true) {x y a : LTm C (.val .uint)}
    (h : modShrModU? x y = some a) :
    (a.eval g ν : Option PrimTy.uint.Denote) = (LTm.app2 (.binop .mod hp) x y).eval g ν := by
  unfold modShrModU? at h
  split at h
  · rename_i u jl W hx hW
    obtain ⟨hs, hxe⟩ := LTm.uArgs?_eq hx
    cases hxe
    obtain ⟨Wv, hWv, rfl⟩ := LTm.eq_of_uLit? hW
    split at h
    · rename_i t ml j hu hj
      obtain ⟨hm, hue⟩ := LTm.uArgs?_eq hu
      cases hue
      obtain ⟨jv, hjv, rfl⟩ := LTm.eq_of_uLit? hj
      split at h
      · rename_i M hM
        obtain ⟨Mv, hMv, rfl⟩ := LTm.eq_of_uLit? hM
        split at h
        · rename_i m w hm' hw'
          obtain ⟨hm1, -⟩ := log2Exact_eq hm'
          obtain ⟨hw1, -⟩ := log2Exact_eq hw'
          split at h
          · rename_i hc
            cases h
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
            obtain ⟨⟨hj0, hj256'⟩, hjw⟩ := hc
            have hW0 : 0 < Wv.1 := by rw [hWv, hw1]; exact Int.pow_pos (by decide)
            have hM0 : 0 < Mv.1 := by rw [hMv, hm1]; exact Int.pow_pos (by decide)
            have hj256 : jv.1 < 256 := by omega
            apply uint_opt_ext
            refine (eval_mod_lit rfl _ Wv hW0).trans (Eq.trans ?_ (eval_mod_lit hp _ Wv hW0).symm)
            have e1 := eval_shr_lit (g := g) (ν := ν) (rfl : BinOp.shr.accepts .uint = true) t jv hj256
            have e2 := eval_shr_lit (g := g) (ν := ν) hs (LTm.app2 (.binop .mod hm) t (.lit Mv)) jv hj256
            have e3 := eval_mod_lit (g := g) (ν := ν) hm t Mv hM0
            have f1 := congrArg (Option.map (· % Wv.1)) e1
            have f2 := congrArg (Option.map (· % Wv.1)) e2
            simp only [Option.map_map] at f1 f2
            refine f1.trans (Eq.trans ?_ f2.symm)
            cases ht : t.eval g ν with
            | none =>
              rw [ht, Option.map_none] at e3
              cases hu' : ((LTm.app2 (.binop .mod hm) t (.lit Mv)).eval g ν : Option PrimTy.uint.Denote) with
              | none => rfl
              | some _ => rw [hu', Option.map_some] at e3; cases e3
            | some a =>
              rw [ht, Option.map_some] at e3
              cases hu' : ((LTm.app2 (.binop .mod hm) t (.lit Mv)).eval g ν : Option PrimTy.uint.Denote) with
              | none => rw [hu', Option.map_none] at e3; cases e3
              | some b =>
                rw [hu', Option.map_some, Option.some.injEq] at e3
                simp only [Option.map_some, Function.comp, e3, hMv, hm1, hWv, hw1]
                have hjn : (jv.1.toNat : Int) = jv.1 := Int.toNat_of_nonneg (by omega)
                exact congrArg some (emod_pow_ediv a.1 m jv.1.toNat w (by omega)).symm
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- `x % c` read as `x` at `uint` where `x`'s range lies below the
positive literal `c` (Lean only): a word reassembled from its bytes, of a
type narrower than its modulus. -/
def Facts.modSmall (F : Facts C) {p : PrimTy} (x y : LTm C (.val p)) : Option (LTm C (.val p)) :=
  match y.litV? with
  | some c =>
    if p == .uint && decide (0 < PrimTy.ival c) && decide (0 ≤ (F.range x).1) &&
        decide ((F.range x).2 < PrimTy.ival c) then some x else none
  | none => none

theorem Facts.modSmall_eval {F : Facts C} (hF : F.Ok g ν) {p : PrimTy}
    (hs : BinOp.mod.accepts p = true) {x y a : LTm C (.val p)} (h : F.modSmall x y = some a) :
    (a.eval g ν : Option p.Denote) = (LTm.app2 (.binop .mod hs) x y).eval g ν := by
  unfold Facts.modSmall at h
  split at h
  · rename_i c hc
    split at h
    · rename_i hb
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
      obtain ⟨⟨⟨hpu, hc0⟩, hlo⟩, hhi⟩ := hb
      subst hpu
      obtain rfl := LTm.eq_of_litV? hc
      rw [eval_uop .mod hs (fun _ => rfl)]
      cases hx : (x.eval g ν : Option PrimTy.uint.Denote) with
      | none => rfl
      | some u =>
        have hr := F.range_sound hF x hx
        unfold InR at hr
        simp only [PrimTy.ival] at hr hc0 hhi
        show some u = (BinOp.arithInt .mod u.1 c.1).bind PrimTy.uint.ofInt?
        simp only [BinOp.arithInt, if_neg (Int.ne_of_gt hc0), Option.bind_some,
          Int.tmod_eq_emod_of_nonneg (by omega : 0 ≤ u.1)]
        rw [Int.emod_eq_of_lt (by omega : 0 ≤ u.1) (by omega : u.1 < c.1)]
        exact (uint_ofInt?_ival u).symm
    · cases h
  · cases h

/-- A remainder `a % c` read again by `Facts.modSmall`. -/
def Facts.reMod (F : Facts C) (t : LTm C (.val .uint)) : LTm C (.val .uint) :=
  match t.uArgs? .mod with
  | some (a, b) =>
    match F.modSmall a b with
    | some r => r
    | none => t
  | none => t

theorem Facts.reMod_eval {F : Facts C} (hF : F.Ok g ν) (t : LTm C (.val .uint)) :
    ((F.reMod t).eval g ν : Option PrimTy.uint.Denote) = t.eval g ν := by
  unfold Facts.reMod
  split
  · rename_i a b ht
    obtain ⟨hp, hte⟩ := LTm.uArgs?_eq ht
    cases hte
    split
    · rename_i r hr
      exact Facts.modSmall_eval hF hp hr
    · rfl
  · rfl

/-- The bit clauses at a numeric type: only `uint` is read. -/
def bitsAdd {p : PrimTy} (x y : LTm C (.val p)) : Option (LTm C (.val p)) :=
  match p, x, y with
  | .uint, x, y => hornerU? x y
  | _, _, _ => none

def bitsMod {p : PrimTy} (x y : LTm C (.val p)) : Option (LTm C (.val p)) :=
  match p, x, y with
  | .uint, x, y =>
    match modModU? x y with
    | some t => some t
    | none => modShrModU? x y
  | _, _, _ => none

def bitsShr {p : PrimTy} (x y : LTm C (.val p)) : Option (LTm C (.val p)) :=
  match p, x, y with
  | .uint, x, y => shrZeroU? x y
  | _, _, _ => none

theorem bitsAdd_eval {p : PrimTy} (h : BinOp.add.accepts p = true) {x y a : LTm C (.val p)}
    (ha : bitsAdd x y = some a) :
    (a.eval g ν : Option p.Denote) = (LTm.app2 (.binop .add h) x y).eval g ν := by
  cases p with
  | uint => exact hornerU?_eval h ha
  | _ => cases ha

theorem bitsMod_eval {p : PrimTy} (h : BinOp.mod.accepts p = true) {x y a : LTm C (.val p)}
    (ha : bitsMod x y = some a) :
    (a.eval g ν : Option p.Denote) = (LTm.app2 (.binop .mod h) x y).eval g ν := by
  cases p with
  | uint =>
    simp only [bitsMod] at ha
    split at ha
    · rename_i t ht; cases ha; exact modModU?_eval h ht
    · exact modShrModU?_eval h ha
  | _ => cases ha

theorem bitsShr_eval {p : PrimTy} (h : BinOp.shr.accepts p = true) {x y a : LTm C (.val p)}
    (ha : bitsShr x y = some a) :
    (a.eval g ν : Option p.Denote) = (LTm.app2 (.binop .shr h) x y).eval g ν := by
  cases p with
  | uint => exact shrZeroU?_eval h ha
  | _ => cases ha

/-- `Facts.reMod` at a numeric type: only `uint` is read. -/
def Facts.reModP (F : Facts C) {p : PrimTy} (t : LTm C (.val p)) : LTm C (.val p) :=
  match p, t with
  | .uint, t => F.reMod t
  | _, t => t

theorem Facts.reModP_eval {F : Facts C} (hF : F.Ok g ν) {p : PrimTy} (t : LTm C (.val p)) :
    ((F.reModP t).eval g ν : Option p.Denote) = t.eval g ν := by
  cases p with
  | uint => exact Facts.reMod_eval hF t
  | _ => rfl

/-- A binary symbol folded: on literals, `a == a`, `a != a` on a term that
returns, `a == b`/`a != b` on terms apart (`Facts.apart`), `x == true`/
`x == false` as `x`/`!x` (`eqBoolLit`), `x < x + c` (`Facts.ltSucc`), a
comparison of terms whose ranges decide it, `(a + b) - b` and
`(a - b) + b` (`Facts.cancel`, `Facts.cancelAdd`), `(a * k + c) / k`
(`Facts.cancelDiv`), `2 * y` as `y + y` (`isTwo`), and bytes reassembled
(`bitsAdd`, `bitsMod`, `bitsShr`). -/
def Facts.fold2 (F : Facts C) {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) :
    LTm C s :=
  match o, x, y with
  | .binop .eqB h, x, y =>
    if x.beqR y && F.returns x then .lit (p := .bool) true
    else if F.apart x y then .lit (p := .bool) false
    else
      match eqBoolLit x y with
      | some t => t
      | none => Decide.fold2 (.binop .eqB h) x y
  | .binop .neB h, x, y =>
    if x.beqR y && F.returns x then .lit (p := .bool) false
    else if F.apart x y then .lit (p := .bool) true
    else Decide.fold2 (.binop .neB h) x y
  | .binop .lt h, x, y =>
    if F.ltSucc x y then .lit (p := .bool) true else
    match F.cmpFold ltDec x y with
    | some c => .lit (p := .bool) c
    | none => Decide.fold2 (.binop .lt h) x y
  | .binop .gt h, x, y =>
    match F.cmpFold ltDec y x with
    | some c => .lit (p := .bool) c
    | none => Decide.fold2 (.binop .gt h) x y
  | .binop .le h, x, y =>
    match F.cmpFold leDec x y with
    | some c => .lit (p := .bool) c
    | none => Decide.fold2 (.binop .le h) x y
  | .binop .ge h, x, y =>
    match F.cmpFold leDec y x with
    | some c => .lit (p := .bool) c
    | none => Decide.fold2 (.binop .ge h) x y
  | .binop .sub h, x, y =>
    match F.cancel x y with
    | some t => t
    | none => Decide.fold2 (.binop .sub h) x y
  | .binop .add h, x, y =>
    match F.cancelAdd x y with
    | some t => t
    | none =>
      match bitsAdd x y with
      | some t => F.reModP t
      | none => Decide.fold2 (.binop .add h) x y
  | .binop .mul h, x, y =>
    if isTwo x then Decide.fold2 (.binop .add h) y y else Decide.fold2 (.binop .mul h) x y
  | .binop .div h, x, y =>
    match F.cancelDiv x y with
    | some t => t
    | none => Decide.fold2 (.binop .div h) x y
  | .binop .mod h, x, y =>
    match bitsMod x y with
    | some t => t
    | none =>
      match F.modSmall x y with
      | some t => t
      | none => Decide.fold2 (.binop .mod h) x y
  | .binop .shr h, x, y =>
    match bitsShr x y with
    | some t => t
    | none => Decide.fold2 (.binop .shr h) x y
  | o, x, y => Decide.fold2 o x y

theorem Facts.cmpFold_sound {F : Facts C} (hF : F.Ok g ν) {p : PrimTy}
    {dec : Int × Int → Int × Int → Option Bool} {x y : LTm C (.val p)} {c : Bool}
    (h : F.cmpFold dec x y = some c) : ∃ u w, (x.eval g ν : Option p.Denote) = some u ∧
      (y.eval g ν : Option p.Denote) = some w ∧ InR (F.range x) (PrimTy.ival u) ∧
      InR (F.range y) (PrimTy.ival w) ∧ dec (F.range x) (F.range y) = some c := by
  unfold Facts.cmpFold at h
  split at h
  · rename_i hr
    simp only [Bool.and_eq_true] at hr
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF _ hr.1)
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF _ hr.2)
    exact ⟨u, w, hu, hw, F.range_sound hF _ hu, F.range_sound hF _ hw, h⟩
  · cases h

theorem Facts.fold2_eval {F : Facts C} (hF : F.Ok g ν) {a b s : Srt} (o : Op2 C a b s)
    (x : LTm C a) (y : LTm C b) : (F.fold2 o x y).eval g ν = (LTm.app2 o x y).eval g ν := by
  cases o
  case binop op p h =>
    cases op
    case eqB | neB =>
      simp only [Facts.fold2]
      split
      · rename_i hb
        simp only [Bool.and_eq_true] at hb
        cases LTm.eq_of_beqR hb.1
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF x hb.2)
        rw [LTm.eval_app2, hv]
        refine Eq.trans (b := some _) rfl ?_
        show _ = binopT _ _ v (some v)
        cases p <;> simp only [binopT, BinOp.shortT, Option.bind_some, BinOp.evalT,
          BinOp.evalNum, BinOp.evalBool, decide_true, Bool.not_true]
      split
      · rename_i hb
        obtain ⟨u, v, hu, hv, hne⟩ := F.apart_sound hF hb
        rw [LTm.eval_app2, hu, hv]
        refine Eq.trans (b := some _) rfl ?_
        show _ = binopT _ _ u (some v)
        cases p with
        | bool =>
          simp only [binopT, BinOp.shortT, Option.bind_some, BinOp.evalT, BinOp.evalBool,
            decide_eq_false hne, Bool.not_false]
        | uint | int =>
          have hne' : ¬ u.1 = v.1 := fun e => hne (Subtype.ext e)
          simp only [binopT, BinOp.shortT, Option.bind_some, BinOp.evalT, BinOp.evalNum,
            decide_eq_false hne', Bool.not_false]
      · first
          | (split
             · rename_i t ht
               exact eqBoolLit_eval ht h
             · exact Decide.fold2_eval g ν _ x y)
          | exact Decide.fold2_eval g ν _ x y
    case lt =>
      have hnum : p.isNumeric = true := by
        cases p <;> first | rfl | cases h
      simp only [Facts.fold2]
      split
      · rename_i hs
        obtain ⟨u, w, hu, hw, hlt⟩ := F.ltSucc_sound hF hs
        simp only [LTm.eval_app2, hu, hw]
        rw [Op2.eval_eq_evalM]
        simp only [Op2.evalM, Option.bind_some]
        unfold binopT
        cases p with
        | bool => cases hnum
        | uint | int =>
          simp only [BinOp.shortT, Option.bind_some, BinOp.evalT, BinOp.evalNum]
          exact congrArg some (decide_eq_true hlt).symm
      · split
        · rename_i c hc
          obtain ⟨u, w, hu, hw, ru, rw', hd⟩ := F.cmpFold_sound hF hc
          simp only [LTm.eval_app2, hu, hw]
          rw [Op2.eval_eq_evalM]
          simp only [Op2.evalM, Option.bind_some]
          unfold binopT
          cases p with
          | bool => cases hnum
          | uint | int =>
            simp only [BinOp.shortT, Option.bind_some, BinOp.evalT, BinOp.evalNum]
            first
              | exact congrArg some (ltDec_sound ru rw' hd).symm
              | exact congrArg some (leDec_sound ru rw' hd).symm
        · exact Decide.fold2_eval g ν _ x y
    case gt | le | ge =>
      have hnum : p.isNumeric = true := by
        cases p <;> first | rfl | cases h
      simp only [Facts.fold2]
      split
      · rename_i c hc
        obtain ⟨u, w, hu, hw, ru, rw', hd⟩ := F.cmpFold_sound hF hc
        simp only [LTm.eval_app2, hu, hw]
        rw [Op2.eval_eq_evalM]
        simp only [Op2.evalM, Option.bind_some]
        unfold binopT
        cases p with
        | bool => cases hnum
        | uint | int =>
          simp only [BinOp.shortT, Option.bind_some, BinOp.evalT, BinOp.evalNum]
          first
            | exact congrArg some (ltDec_sound ru rw' hd).symm
            | exact congrArg some (leDec_sound ru rw' hd).symm
      · exact Decide.fold2_eval g ν _ x y
    case sub =>
      simp only [Facts.fold2]
      split
      · rename_i t ht
        exact Facts.cancel_eval hF h ht
      · exact Decide.fold2_eval g ν _ x y
    case add =>
      simp only [Facts.fold2]
      split
      · rename_i t ht
        exact Facts.cancelAdd_eval hF h ht
      · split
        · rename_i t ht
          exact (Facts.reModP_eval hF t).trans (bitsAdd_eval h ht)
        · exact Decide.fold2_eval g ν _ x y
    case mul =>
      simp only [Facts.fold2]
      split
      · rename_i hx
        rw [Decide.fold2_eval]
        exact evalT_two_mul hx h y
      · exact Decide.fold2_eval g ν _ x y
    case div =>
      simp only [Facts.fold2]
      split
      · rename_i t ht
        exact Facts.cancelDiv_eval hF h ht
      · exact Decide.fold2_eval g ν _ x y
    case mod =>
      simp only [Facts.fold2]
      split
      · rename_i t ht
        exact bitsMod_eval h ht
      · split
        · rename_i t ht
          exact Facts.modSmall_eval hF h ht
        · exact Decide.fold2_eval g ν _ x y
    case shr =>
      simp only [Facts.fold2]
      split
      · rename_i t ht
        exact bitsShr_eval h ht
      · exact Decide.fold2_eval g ν _ x y
    all_goals simp only [Facts.fold2]; exact Decide.fold2_eval g ν _ x y
  all_goals simp only [Facts.fold2]; exact Decide.fold2_eval g ν _ x y

/-- A ternary symbol folded: a conditional on a literal, or with one
branch twice. -/
def Facts.fold3 (F : Facts C) {a b c s : Srt} (o : Op3 C a b c s) (x : LTm C a) (y : LTm C b)
    (z : LTm C c) : LTm C s :=
  match o, x, y, z with
  | .ite, x, y, z =>
    match x.litV? with
    | some v => cond (v : Bool) y z
    | none =>
      if y.beqR z && F.returns x then y
      else if y.beqR x && z.beqR (LTm.tt : LTm C (.val .bool)) && F.returns x then
        match (LTm.tt : LTm C (.val .bool)).castTo? with
        | some t => t
        | none => .app3 .ite x y z
      else .app3 .ite x y z
  | o, x, y, z => .app3 o x y z

theorem Facts.fold3_eval {F : Facts C} (hF : F.Ok g ν) {a b c s : Srt} (o : Op3 C a b c s)
    (x : LTm C a) (y : LTm C b) (z : LTm C c) :
    (F.fold3 o x y z).eval g ν = (LTm.app3 o x y z).eval g ν := by
  cases o
  case ite p =>
    simp only [Facts.fold3]
    split
    · rename_i v hv
      obtain rfl := LTm.eq_of_litV? hv
      show _ = cond (v : Bool) _ _
      cases (v : Bool) <;> rfl
    · split
      · rename_i hb
        simp only [Bool.and_eq_true] at hb
        cases LTm.eq_of_beqR hb.1
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF x hb.2)
        rw [LTm.eval_app3, hv]
        show _ = cond (v : Bool) _ _
        cases (v : Bool) <;> rfl
      · split
        · rename_i hb
          simp only [Bool.and_eq_true] at hb
          obtain ⟨⟨h1, h2⟩, h3⟩ := hb
          cases LTm.sigma_eq_of_beqR h1
          cases LTm.sigma_eq_of_beqR h2
          split
          · rename_i t ht
            cases LTm.castTo?_eq ht
            obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF x h3)
            rw [LTm.eval_app3, hv]
            show some true = cond (v : Bool) _ _
            cases (v : Bool) <;> rfl
          · rfl
        · rfl
  all_goals rfl

/-- `Facts.nf`'s compiled twin. -/
def Facts.nfM (F : Facts C) : {s : Srt} → LTm C s → LTm C s
  | _, .var k => F.rw (.var k)
  | _, .app0 o => F.rw (.app0 o)
  | _, .app1 o x => F.rw (F.fold1 o (F.nfM x))
  | _, .app2 o x y => F.rw (F.fold2 o (F.nfM x) (F.nfM y))
  | _, .app3 o x y z => F.rw (F.fold3 o (F.nfM x) (F.nfM y) (F.nfM z))
  | _, .index it q i => .index it (F.nfM q) (F.nfM i)
  | _, .obsW q => F.rw (.obsW (F.nfM q))
  | _, .obsL q => F.rw (.obsL (F.nfM q))
  | _, .obsH q => F.rw (F.hasRange (hasN (.obsH (F.nfM q))))
  | _, .seq d a => F.seqN (F.nfM d) (F.nfM a)
  | _, .orElse a b => F.orElseN (F.nfM a) (F.nfM b)
  | _, .kite a b t e => F.rw (F.kiteN (F.nfM a) (F.nfM b) (F.nfM t) (F.nfM e))
  | _, .err => .err

/-- **A term's normal form under the facts**, bottom-up: symbols folded,
guards that return dropped, keys compared, what a premise rewrites
rewritten.  By the recursor. -/
@[implemented_by Facts.nfM]
def Facts.nf (F : Facts C) {s : Srt} (t : LTm C s) : LTm C s :=
  @LTm.rec C (fun s _ => LTm C s)
    (@fun _ k => F.rw (.var k))
    (@fun _ o => F.rw (.app0 o))
    (@fun _ _ o _ ihx => F.rw (F.fold1 o ihx))
    (@fun _ _ _ o _ _ ihx ihy => F.rw (F.fold2 o ihx ihy))
    (@fun _ _ _ _ o _ _ _ ihx ihy ihz => F.rw (F.fold3 o ihx ihy ihz))
    (@fun _ _ _ it _ _ ihq ihi => .index it ihq ihi)
    (@fun _ _ ih => F.rw (.obsW ih))
    (@fun _ _ ih => F.rw (.obsL ih))
    (@fun _ _ ih => F.rw (F.hasRange (hasN (.obsH ih))))
    (@fun _ _ _ _ ihd iha => F.seqN ihd iha)
    (@fun _ _ _ iha ihb => F.orElseN iha ihb)
    (@fun _ _ _ _ _ _ iha ihb iht ihe => F.rw (F.kiteN iha ihb iht ihe))
    (@fun _ => .err) s t

theorem Facts.nf_eq_nfM (F : Facts C) {s : Srt} (t : LTm C s) : F.nf t = F.nfM t := by
  induction t with
  | var | app0 | err => rfl
  | app1 o x ih => simp only [Facts.nfM, ← ih]; rfl
  | app2 o x y ihx ihy => simp only [Facts.nfM, ← ihx, ← ihy]; rfl
  | app3 o x y z ihx ihy ihz => simp only [Facts.nfM, ← ihx, ← ihy, ← ihz]; rfl
  | index it q i ihq ihi => simp only [Facts.nfM, ← ihq, ← ihi]; rfl
  | obsW q ih | obsL q ih | obsH q ih => simp only [Facts.nfM, ← ih]; rfl
  | seq d a ihd iha => simp only [Facts.nfM, ← ihd, ← iha]; rfl
  | orElse a b iha ihb => simp only [Facts.nfM, ← iha, ← ihb]; rfl
  | kite a b t e iha ihb iht ihe => simp only [Facts.nfM, ← iha, ← ihb, ← iht, ← ihe]; rfl

/-- **The normal form reads what the term reads.** -/
theorem Facts.nf_eval {F : Facts C} (hF : F.Ok g ν) {s : Srt} (t : LTm C s) :
    (F.nf t).eval g ν = t.eval g ν := by
  induction t with
  | var k => exact F.rw_eval hF _
  | app0 o => exact F.rw_eval hF _
  | err => rfl
  | app1 o x ih =>
    show (F.rw (F.fold1 o (F.nf x))).eval g ν = _
    rw [F.rw_eval hF, F.fold1_eval hF, LTm.eval_app1, LTm.eval_app1, ih]
  | app2 o x y ihx ihy =>
    show (F.rw (F.fold2 o (F.nf x) (F.nf y))).eval g ν = _
    rw [F.rw_eval hF, F.fold2_eval hF, LTm.eval_app2, LTm.eval_app2, ihx, ihy]
  | app3 o x y z ihx ihy ihz =>
    show (F.rw (F.fold3 o (F.nf x) (F.nf y) (F.nf z))).eval g ν = _
    rw [F.rw_eval hF, F.fold3_eval hF, LTm.eval_app3, LTm.eval_app3, ihx, ihy, ihz]
  | index it q i ihq ihi =>
    show (LTm.index it (F.nf q) (F.nf i)).eval g ν = _
    rw [LTm.eval_index, LTm.eval_index, ihq, ihi]
  | obsW q ih =>
    show (F.rw (.obsW (F.nf q))).eval g ν = _
    rw [F.rw_eval hF, LTm.eval_obsW, LTm.eval_obsW, ih]
  | obsL q ih =>
    show (F.rw (.obsL (F.nf q))).eval g ν = _
    rw [F.rw_eval hF, LTm.eval_obsL, LTm.eval_obsL, ih]
  | obsH q ih =>
    show (F.rw (F.hasRange (hasN (.obsH (F.nf q))))).eval g ν = _
    rw [F.rw_eval hF, F.hasRange_eval hF, hasN_eval, LTm.eval_obsH, LTm.eval_obsH, ih]
  | seq d a ihd iha =>
    show (F.seqN (F.nf d) (F.nf a)).eval g ν = _
    rw [F.seqN_eval hF, LTm.eval_seq, LTm.eval_seq, ihd, iha]
  | orElse a b iha ihb =>
    show (F.orElseN (F.nf a) (F.nf b)).eval g ν = _
    rw [F.orElseN_eval hF, LTm.eval_orElse, LTm.eval_orElse, iha, ihb]
  | kite a b t e iha ihb iht ihe =>
    show (F.rw (F.kiteN (F.nf a) (F.nf b) (F.nf t) (F.nf e))).eval g ν = _
    rw [F.rw_eval hF, F.kiteN_eval hF, LTm.eval_kite, LTm.eval_kite, iha, ihb, iht, ihe]

end Normal

end Decide

end Solidity
