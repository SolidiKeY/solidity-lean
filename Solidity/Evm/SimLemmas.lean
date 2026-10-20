import Solidity.Evm.Repr
import Solidity.Evm.Signed
import Solidity.Evm.Exp
import Solidity.Semantics.Run

/-!
# The machine lemmas of the simulation

What `Evm/Sim.lean`, `Evm/Expr.lean` and `Evm/Stmt.lean` build
the simulation from, none of it about the syntax: the guard sequences of
`Evm/Layout.lean` computed on the machine (`add_tail`/`sub_tail`/`mul_tail`
are solc's overflow checks, exact on words below `2^256`; `mul_ok_iff` is the
arithmetic fact behind the `*` check; the signed ones are `Evm/Signed.lean`'s,
`**` is `Evm/Exp.lean`'s), a value's word (`ReprV`, `ValOutT`: a value
pushed, or both revert), the slot sequences (`boundsCheck_run`,
`elemSlot_run`, …), the machine's environment (`EnvSim`), and the store
sequences of `delete`, `pop`, a copy and a `push` (`zeroCode_run`,
`popCode_run`, `storeLeaves_run`, `pushSlotCode_run`).

**The operators.**  The tails are proved on the typed operators directly
(`BinOp.evalT`, `UnOp.evalT`, `compoundT`, `bumpT`, `Semantics/Ops.lean`):
an operator's integer result and `PrimTy.ofInt?`'s range check against the
word its guard pushes (`utail_simT`, its signed half `stail_simT`, then
`tail_simT`, `neg_simT`, `bnot_simT`, `compound_simT`, `bump_simT`).
-/

namespace Solidity
namespace Evm

/-! ## Values, typed -/

/-- A `uint` is represented by itself, a word below `2^256`: `total` read as `7` pushes `7`. -/
theorem ReprV.uint_inv {v : PrimTy.uint.Denote} {w : Word} (h : ReprV .uint v w) :
    ∃ a : Nat, ∃ ha : a < W, v.1 = a ∧ w = .val ⟨a, ha⟩ := by
  obtain ⟨a, rfl, hv⟩ := h
  exact ⟨a.1, a.2, hv, rfl⟩

/-- A `bool` is represented by `1` or `0`: `flags[3]` read as `true` pushes `1`. -/
theorem ReprV.bool_inv {b : PrimTy.bool.Denote} {w : Word} (h : ReprV .bool b w) :
    w = .val (bword b) := h

/-- A word below `2^256` represents itself as a `uint`: `total = 7;` pushes `7`. -/
theorem ReprV.uint_of {v : PrimTy.uint.Denote} {a : Fin W} (h : v.1 = a.1) :
    ReprV .uint v (.val a) :=
  ⟨a, rfl, h⟩

/-- A value's outcome, typed run and machine together: a value and the word
representing it pushed, or both revert. -/
def ValOutT (p : PrimTy) (res : TRes p.Denote) (out : Out) (m : Machine) : Prop :=
  (∃ v w, res = .ok v ∧ ReprV p v w ∧ out = .ok (m.push w) 0) ∨
    (res = .error .revert ∧ out = .revert)

/-- An outcome read off a typed `Option`. -/
theorem ValOutT.opt_cases {p : PrimTy} {o : Option p.Denote} {out : Out} {m : Machine}
    (h : ValOutT p (TRes.ofOpt o) out m) :
    (∃ v w, o = some v ∧ ReprV p v w ∧ out = .ok (m.push w) 0) ∨ (o = none ∧ out = .revert) := by
  cases o with
  | none =>
    rcases h with ⟨_, _, h, _⟩ | ⟨_, h⟩
    · cases h
    · exact .inr ⟨rfl, h⟩
  | some v =>
    rcases h with ⟨v', w, h, hr, hout⟩ | ⟨h, _⟩
    · cases h; exact .inl ⟨v, w, rfl, hr, hout⟩
    · cases h

section Words

/-! ## Results on words

What a typed operator's `PrimTy.ofInt?` is on the machine: the range check
of `uint` and `int` against the words a guard pushes, or the revert. -/

/-- An integer in `uint`'s range is a `uint`. -/
private theorem ofInt_uint {n : Int} (h : 0 ≤ n ∧ n < W) :
    PrimTy.uint.ofInt? n = some ⟨n, by simp only [PrimTy.inRange, decide_eq_true_eq]; exact h⟩ :=
  dif_pos (by simp only [PrimTy.inRange, decide_eq_true_eq]; exact h)

/-- An integer out of `uint`'s range reverts. -/
private theorem ofInt_uint_none {n : Int} (h : ¬(0 ≤ n ∧ n < W)) : PrimTy.uint.ofInt? n = none :=
  dif_neg (by simp only [PrimTy.inRange, decide_eq_true_eq]; exact h)

/-- An integer in `int`'s range is an `int`. -/
private theorem ofInt_int {n : Int} (h : -(H : Int) ≤ n ∧ n < H) :
    PrimTy.int.ofInt? n = some ⟨n, by simp only [PrimTy.inRange, decide_eq_true_eq]; exact h⟩ :=
  dif_pos (by simp only [PrimTy.inRange, decide_eq_true_eq]; exact h)

/-- An integer out of `int`'s range reverts. -/
private theorem ofInt_int_none {n : Int} (h : ¬(-(H : Int) ≤ n ∧ n < H)) :
    PrimTy.int.ofInt? n = none :=
  dif_neg (by simp only [PrimTy.inRange, decide_eq_true_eq]; exact h)

/-- `Option.bind` on a result: the range check of a computed integer.  Not
a `rfl` lemma on purpose: `simp` then rewrites with a proof, and the kernel
does not check `(some n).bind ofInt? ≡ ofInt? n` by unfolding `ofInt?` (its
range test on `2^256` is a deep recursion there). -/
private theorem some_bind' {α β : Type} (a : α) (f : α → Option β) : (some a).bind f = f a := by
  rw [Option.bind]

/-- A typed `none` and a machine revert. -/
private theorem out_revert {p : PrimTy} {m : Machine} : ValOutT p (TRes.ofOpt none) .revert m :=
  .inr ⟨rfl, rfl⟩

/-- A `uint` in range, its word pushed: `3 + 4` pushes `7`. -/
private theorem out_uint_ok {n : Int} {r : Nat} (hr : n = r) (hrW : r < W) {out : Out}
    {m : Machine} (hrun : out = .ok (m.push (.val ⟨r, hrW⟩)) 0) :
    ValOutT .uint (TRes.ofOpt (PrimTy.uint.ofInt? n)) out m := by
  rw [ofInt_uint ⟨by omega, by omega⟩]
  exact .inl ⟨_, _, rfl, ReprV.uint_of hr, hrun⟩

/-- A `uint` guard: the word pushed when the result is in range, else a
revert (`add_tail`'s shape). -/
private theorem out_uint_if {n : Int} {r : Nat} {c : Prop} [Decidable c]
    (hc : c ↔ 0 ≤ n ∧ n < W) (hr : c → n = r) (m : Machine) :
    ValOutT .uint (TRes.ofOpt (PrimTy.uint.ofInt? n))
      (if h : c then .ok { m with stack := .val ⟨r, by have := hc.1 h; have := hr h; omega⟩ ::
        m.stack } 0 else .revert) m := by
  by_cases h : c
  · have := hc.1 h
    rw [dif_pos h]
    exact out_uint_ok (hr h) _ rfl
  · rw [dif_neg h, ofInt_uint_none (fun h' => h (hc.2 h'))]
    exact out_revert

/-- An `int` in range, its two's complement pushed: `x = -1` pushes `2^256 - 1`. -/
private theorem out_int_ok {n : Int} (h : -(H : Int) ≤ n ∧ n < H) {out : Out} {m : Machine}
    (hrun : out = .ok (m.push (.val (sword n))) 0) :
    ValOutT .int (TRes.ofOpt (PrimTy.int.ofInt? n)) out m := by
  rw [ofInt_int h]
  exact .inl ⟨_, _, rfl,
    ⟨_, rfl, by
      rw [sword_val (by have := W_eq; omega) (by have := W_eq; omega)]
      exact (sgn_toWord h.1 h.2).symm⟩,
    hrun⟩

/-- An `int` guard: the word pushed when the result is in range, else a
revert (`sadd_tail`'s shape). -/
private theorem out_int_if {n : Int} (m : Machine) :
    ValOutT .int (TRes.ofOpt (PrimTy.int.ofInt? n))
      (if -(H : Int) ≤ n ∧ n < H then .ok { m with stack := .val (sword n) :: m.stack } 0
        else .revert) m := by
  by_cases h : -(H : Int) ≤ n ∧ n < H
  · rw [if_pos h]; exact out_int_ok h rfl
  · rw [if_neg h, ofInt_int_none h]; exact out_revert

/-- A comparison's `bool`, its word pushed: `3 < 4` pushes `1`. -/
private theorem out_bool {b c : Bool} (hc : c = b) {out : Out} {m : Machine}
    (h : out = .ok { m with stack := .val (bword c) :: m.stack } 0) :
    ValOutT .bool (TRes.ofOpt (some b)) out m :=
  .inl ⟨b, _, rfl, rfl, hc ▸ h⟩

/-- An `int` out of range and a machine revert. -/
private theorem out_int_none {n : Int} (h : ¬(-(H : Int) ≤ n ∧ n < H)) {m : Machine} :
    ValOutT .int (TRes.ofOpt (PrimTy.int.ofInt? n)) .revert m := by
  rw [ofInt_int_none h]; exact out_revert

/-! ## The guard sequences -/

/-- A sum of two words that wraps loses exactly `2^256`: `(2^256 - 1) + 1` wraps to `0`. -/
theorem mod_W_of_ge {x : Nat} (h₁ : W ≤ x) (h₂ : x < W + W) : x % W = x - W := by
  rw [Nat.mod_eq_sub_mod h₁, Nat.mod_eq_of_lt (by omega)]

/-- `OR` of two comparison words is `0` exactly when both are false (the `*` guard). -/
@[simp] theorem bword_or_eq_zero (x y : Bool) :
    ((bword x).1 ||| (bword y).1) = 0 ↔ x = false ∧ y = false := by
  cases x <;> cases y <;> decide

/-- `a + b` with solc's overflow check: the sum wraps exactly when it is below
`a`.  With `a = 2^256 - 1` and `b = 1` the word is `0`, below `a`, and the code
reverts; with `a = 3`, `b = 4` it is `7`. -/
theorem add_tail (m : Machine) (st : List Word) {a b : Nat} (ha : a < W) (hb : b < W) :
    run (uTail .add) { m with stack := w[b] :: w[a] :: st } =
      if _ : a + b < W then .ok { m with stack := w[a + b] :: st } 0 else .revert := by
  simp [run, uTail, assertTop, Instr.step, Machine.next]
  by_cases h : a + b < W
  · simp only [Nat.mod_eq_of_lt h]; simp [h, show ¬ a + b < a by omega, Instr.step, Machine.next]
  · simp only [mod_W_of_ge (show W ≤ a + b by omega) (by omega)]
    simp [h, Instr.step, show a + b - W < a by omega]

/-- `a - b` with solc's underflow check: revert when `b > a`.  `3 - 4`
reverts, `4 - 3` is `1`. -/
theorem sub_tail (m : Machine) (st : List Word) {a b : Nat} (ha : a < W) (hb : b < W) :
    run (uTail .sub) { m with stack := w[b] :: w[a] :: st } =
      if _ : b ≤ a then .ok { m with stack := w[a - b] :: st } 0 else .revert := by
  simp [run, uTail, assertTop, Instr.step, Machine.next]
  by_cases h : b ≤ a
  · have e : (a + (W - b)) % W = a - b := by
      rw [show a + (W - b) = (a - b) + W by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    simp [h, show ¬ a < b by omega, Instr.step, Machine.next, e]
  · simp [show a < b by omega, Instr.step]

/-- The arithmetic behind solc's multiplication check: on words, `a = 0` or
the wrapped product divided by `a` gives back `b` exactly when the product does
not wrap.  `2^128 · 2^128` wraps to `0`, and `0 / 2^128 = 0 ≠ 2^128`. -/
theorem mul_ok_iff {a b : Nat} :
    (a = 0 ∨ a * b % W / a = b) ↔ a * b < W := by
  constructor
  · rintro (rfl | h)
    · simpa using W_pos
    · refine Decidable.byContradiction fun hlt => ?_
      have hge : W ≤ a * b := by omega
      have h1 : a * b % W < W := Nat.mod_lt _ W_pos
      have h2 : a * (a * b % W / a) ≤ a * b % W := Nat.mul_div_le _ _
      rw [h] at h2
      omega
  · intro h
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · exact .inl rfl
    · right; rw [Nat.mod_eq_of_lt h, Nat.mul_div_cancel_left _ hpos]

/-- `a * b` with solc's overflow check. -/
theorem mul_tail (m : Machine) (st : List Word) {a b : Nat} (ha : a < W) (hb : b < W) :
    run (uTail .mul) { m with stack := w[b] :: w[a] :: st } =
      if _ : a * b < W then .ok { m with stack := w[a * b] :: st } 0 else .revert := by
  simp [run, uTail, assertTop, Instr.step, Machine.next]
  have key := mul_ok_iff (a := a) (b := b)
  by_cases h : a * b < W
  · simp only [h, if_true]
    have e : b * a % W = a * b := by rw [Nat.mul_comm, Nat.mod_eq_of_lt h]
    by_cases h0 : a = 0
    · subst h0; simp [Instr.step, Machine.next]
    · have h2 : a * b / a = b := Nat.mul_div_cancel_left b (Nat.pos_of_ne_zero h0)
      simp [h0, h2, Instr.step, Machine.next, e]
  · simp only [h, if_false]
    have h0 : a ≠ 0 := fun h0 => h (by subst h0; simpa using W_pos)
    have h1 : b ≠ b * a % W / a := fun h1 =>
      h (key.1 (.inr (by rw [Nat.mul_comm]; exact h1.symm)))
    simp [h0, h1, Instr.step]

/-- `a / b`, reverting on `b = 0` (solc's `Panic(0x12)`). -/
theorem div_tail (m : Machine) (st : List Word) {a b : Nat} (ha : a < W) (hb : b < W) :
    run (uTail .div) { m with stack := w[b] :: w[a] :: st } =
      if b = 0 then .revert else .ok { m with stack := w[a / b] :: st } 0 := by
  by_cases h : b = 0
  · subst h; rfl
  · simp [run, uTail, assertTop, Instr.step, Machine.next, h]

/-- `a % b`, reverting on `b = 0`. -/
theorem mod_tail (m : Machine) (st : List Word) {a b : Nat} (ha : a < W) (hb : b < W) :
    run (uTail .mod) { m with stack := w[b] :: w[a] :: st } =
      if b = 0 then .revert else .ok { m with stack := w[a % b] :: st } 0 := by
  by_cases h : b = 0
  · subst h; rfl
  · simp [run, uTail, assertTop, Instr.step, Machine.next, h]

/-- A comparison or an equality: one or two instructions and no guard. -/
theorem cmp_tail (m : Machine) (st : List Word) {a b : Nat} (ha : a < W) (hb : b < W) :
    run (uTail .lt) { m with stack := w[b] :: w[a] :: st } =
        .ok { m with stack := .val (bword (decide (a < b))) :: st } 0 ∧
    run (uTail .gt) { m with stack := w[b] :: w[a] :: st } =
        .ok { m with stack := .val (bword (decide (b < a))) :: st } 0 ∧
    run (uTail .le) { m with stack := w[b] :: w[a] :: st } =
        .ok { m with stack := .val (bword (decide (a ≤ b))) :: st } 0 ∧
    run (uTail .ge) { m with stack := w[b] :: w[a] :: st } =
        .ok { m with stack := .val (bword (decide (b ≤ a))) :: st } 0 ∧
    run (uTail .eqB) { m with stack := w[b] :: w[a] :: st } =
        .ok { m with stack := .val (bword (decide (a = b))) :: st } 0 ∧
    run (uTail .neB) { m with stack := w[b] :: w[a] :: st } =
        .ok { m with stack := .val (bword (!decide (a = b))) :: st } 0 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [run, uTail, Instr.step, Machine.next, bword]
  · simp [run, uTail, Instr.step, Machine.next, bword]
  · simp [run, uTail, Instr.step, Machine.next, bword]
    by_cases h : a = b <;> simp [h, eq_comm]
  · simp [run, uTail, Instr.step, Machine.next, bword]
    by_cases h : a = b <;> simp [h, eq_comm]

/-! ## The operators, typed -/

/-- `x - y` modulo `2^256` is `x + (2^256 - y)` modulo `2^256`: `SUB`. -/
private theorem subW_eq {a b : Nat} (hb : b < W) :
    ((a + (W - b)) % W : Nat) = ((a : Int) - b) % (W : Int) := by
  rw [Int.natCast_emod, show ((a + (W - b) : Nat) : Int) = ((a : Int) - b) + W by omega,
    Int.add_emod_right]

/-- **The operators agree at `uint`**: on two words below `2^256`, an
operator's tail computes the word of the typed result, or reverts exactly when
the typed operator does.

Example: `a + b` with `a = 2^256 - 1`, `b = 1`: `ofInt?` reverts (the sum is
not a `uint256`), and so does `add_tail`'s guard. -/
private theorem utail_simT {op : BinOp} (hop : binInFrag op .uint = true) (hand : op ≠ .and)
    (hor : op ≠ .or) (hacc : op.accepts .uint = true) {a b : Nat} (ha : a < W) (hb : b < W)
    (m : Machine) :
    ValOutT (op.ret .uint) (TRes.ofOpt (BinOp.evalNum .uint rfl a b op hacc))
      (run (uTail op) { m with stack := w[b] :: w[a] :: m.stack }) m := by
  cases op <;> first | exact absurd hop (by decide) | exact absurd rfl hand | exact absurd rfl hor | skip
  all_goals simp only [BinOp.evalNum, BinOp.arithInt, some_bind']
  · -- `+`
    rw [add_tail m m.stack ha hb]
    exact out_uint_if (n := (a : Int) + b) (r := a + b) (by omega) (fun _ => by omega) m
  · -- `-`
    rw [sub_tail m m.stack ha hb]
    exact out_uint_if (n := (a : Int) - b) (r := a - b) (by omega) (fun _ => by omega) m
  · -- `*`
    rw [mul_tail m m.stack ha hb, ← Int.natCast_mul]
    exact out_uint_if (n := ((a * b : Nat) : Int)) (r := a * b) (by omega) (fun _ => rfl) m
  · -- `**`
    rw [if_neg (by omega), some_bind', Int.toNat_natCast, ← Int.natCast_pow,
      exp_tail m m.stack ha hb]
    exact out_uint_if (n := ((a ^ b : Nat) : Int)) (r := a ^ b) (by omega) (fun _ => rfl) m
  · -- `/`
    rw [div_tail m m.stack ha hb]
    by_cases h : b = 0
    · rw [if_pos (by omega), if_pos h]; exact out_revert
    · rw [if_neg (by omega), if_neg h, some_bind']
      exact out_uint_ok (n := Int.tdiv a b) (r := a / b) rfl
        (Nat.lt_of_le_of_lt (Nat.div_le_self a b) ha) rfl
  · -- `%`
    rw [mod_tail m m.stack ha hb]
    by_cases h : b = 0
    · rw [if_pos (by omega), if_pos h]; exact out_revert
    · rw [if_neg (by omega), if_neg h, some_bind']
      exact out_uint_ok (n := Int.tmod a b) (r := a % b) rfl
        (Nat.lt_of_le_of_lt (Nat.mod_le a b) ha) rfl
  · exact out_bool (by simp only [Int.ofNat_lt]) (cmp_tail m m.stack ha hb).1
  · exact out_bool (by simp only [Int.ofNat_lt]) (cmp_tail m m.stack ha hb).2.1
  · exact out_bool (by simp only [Int.ofNat_le]) (cmp_tail m m.stack ha hb).2.2.1
  · exact out_bool (by simp only [Int.ofNat_le]) (cmp_tail m m.stack ha hb).2.2.2.1
  · exact out_bool (by simp only [Int.ofNat_inj]) (cmp_tail m m.stack ha hb).2.2.2.2.1
  · exact out_bool (by simp only [Int.ofNat_inj]) (cmp_tail m m.stack ha hb).2.2.2.2.2
  · -- `&`
    exact out_uint_ok (r := b &&& a) (by show ((a &&& b : Nat) : Int) = _; rw [Nat.and_comm])
      (Nat.and_lt_two_pow b ha) rfl
  · -- `|`
    exact out_uint_ok (r := b ||| a) (by show ((a ||| b : Nat) : Int) = _; rw [Nat.or_comm])
      (Nat.or_lt_two_pow hb ha) rfl
  · -- `^`
    exact out_uint_ok (r := b ^^^ a) (by show ((a ^^^ b : Nat) : Int) = _; rw [Nat.xor_comm])
      (Nat.xor_lt_two_pow hb ha) rfl
  · -- `<<`
    by_cases h : b < 256
    · refine out_uint_ok (r := a * 2 ^ b % W) ?_ (Nat.mod_lt _ W_pos)
        (by simp [run, uTail, Instr.step, Machine.next, Machine.push, h])
      rw [if_pos (by omega), Int.toNat_natCast]
      show (a : Int) * 2 ^ b % (W : Int) = _
      rw [Int.natCast_emod, Int.natCast_mul, Int.natCast_pow]; rfl
    · refine out_uint_ok (r := 0) ?_ W_pos (by simp [run, uTail, Instr.step, Machine.next, Machine.push, h])
      rw [if_neg (by omega)]; rfl
  · -- `>>`
    by_cases h : b < 256
    · refine out_uint_ok (r := a / 2 ^ b) ?_ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)
        (by simp [run, uTail, Instr.step, Machine.next, Machine.push, h])
      rw [if_pos (by omega), Int.toNat_natCast, Int.natCast_ediv, Int.natCast_pow]; rfl
    · refine out_uint_ok (r := 0) ?_ W_pos (by simp [run, uTail, Instr.step, Machine.next, Machine.push, h])
      rw [if_neg (by omega)]; rfl
  · -- `+%`
    refine out_uint_ok (r := (b + a) % W) ?_ (Nat.mod_lt _ W_pos) rfl
    show ((a : Int) + b) % (W : Int) = _
    rw [Int.natCast_emod, Int.natCast_add, Int.add_comm]
  · -- `-%`
    exact out_uint_ok (r := (a + (W - b)) % W) (subW_eq hb).symm (Nat.mod_lt _ W_pos) rfl
  · -- `*%`
    refine out_uint_ok (r := (b * a) % W) ?_ (Nat.mod_lt _ W_pos) rfl
    show ((a : Int) * b) % (W : Int) = _
    rw [Int.natCast_emod, Int.natCast_mul, Int.mul_comm]
  · -- `**%`
    rw [if_neg (by omega), some_bind', Int.toNat_natCast]
    refine out_uint_ok (r := a ^ b % W) ?_ (Nat.mod_lt _ W_pos) rfl
    show (a : Int) ^ b % (W : Int) = _
    rw [Int.natCast_emod, Int.natCast_pow]

/-- **The operators agree at `int`**: `utail_simT`'s signed half, on the
integers two words read as (`sgn`). -/
private theorem stail_simT {op : BinOp} (hop : binInFrag op .int = true) (hand : op ≠ .and)
    (hor : op ≠ .or) (hacc : op.accepts .int = true) {a b : Nat} (ha : a < W) (hb : b < W)
    (m : Machine) :
    ValOutT (op.ret .int) (TRes.ofOpt (BinOp.evalNum .int rfl (sgn a) (sgn b) op hacc))
      (run (sTail op) { m with stack := w[b] :: w[a] :: m.stack }) m := by
  have hb0 : (sgn b = 0) ↔ b = 0 := sgn_eq_zero hb
  have heq : decide (a = b) = decide (sgn a = sgn b) :=
    decide_eq_decide.2 ⟨fun h => h ▸ rfl, sgn_inj ha hb⟩
  cases op <;> first | exact absurd hop (by decide) | exact absurd rfl hand | exact absurd rfl hor | skip
  all_goals simp only [BinOp.evalNum, BinOp.arithInt, some_bind']
  · rw [sadd_tail m m.stack ha hb]; exact out_int_if m
  · rw [ssub_tail m m.stack ha hb]; exact out_int_if m
  · rw [smul_tail m m.stack ha hb]; exact out_int_if m
  · -- `/`
    rw [sdiv_tail m m.stack ha hb]
    by_cases h0 : b = 0
    · rw [if_pos h0, if_pos (hb0.2 h0)]; exact out_revert
    · rw [if_neg h0, if_neg (fun h => h0 (hb0.1 h)), some_bind']
      have hr := tdiv_range (sgn_range ha) (y := sgn b) (fun h => h0 (hb0.1 h))
      have e1 : a = H ↔ sgn a = -(H : Int) := by
        have := W_eq; unfold sgn; constructor <;> intro h <;> split at * <;> omega
      have e2 : b = W - 1 ↔ sgn b = -1 := by
        have := W_eq; have := H_pos; unfold sgn; constructor <;> intro h <;> split at * <;> omega
      by_cases hs : a = H ∧ b = W - 1
      · rw [if_pos hs]
        exact out_int_none fun h => (hr.1 h) ⟨e1.1 hs.1, e2.1 hs.2⟩
      · rw [if_neg hs]
        exact out_int_ok (hr.2 fun h => hs ⟨e1.2 h.1, e2.2 h.2⟩) rfl
  · -- `%`
    rw [smod_tail m m.stack ha hb]
    by_cases h0 : b = 0
    · rw [if_pos h0, if_pos (hb0.2 h0)]; exact out_revert
    · rw [if_neg h0, if_neg (fun h => h0 (hb0.1 h)), some_bind']
      exact out_int_ok (tmod_range (x := sgn a) (sgn_range hb) (fun h => h0 (hb0.1 h))) rfl
  · exact out_bool rfl (scmp_tail m m.stack ha hb).1
  · exact out_bool rfl (scmp_tail m m.stack ha hb).2.1
  · exact out_bool rfl (scmp_tail m m.stack ha hb).2.2.1
  · exact out_bool rfl (scmp_tail m m.stack ha hb).2.2.2.1
  · exact out_bool heq (scmp_tail m m.stack ha hb).2.2.2.2.1
  · exact out_bool (by rw [heq]) (scmp_tail m m.stack ha hb).2.2.2.2.2

/-- **The operators agree**, typed: on words representing its operands, an
operator's tail computes the word of the typed result, or reverts exactly
when the typed operator does. -/
theorem tail_simT {op : BinOp} {p : PrimTy} (hop : binInFrag op p = true) (hand : op ≠ .and)
    (hor : op ≠ .or) (hacc : op.accepts p = true) {a b : p.Denote} {wa wb : Word}
    (ha : ReprV p a wa) (hb : ReprV p b wb) (m : Machine) :
    ValOutT (op.ret p) (TRes.ofOpt (op.evalT hacc a b))
      (run (binTail p op) { m with stack := wb :: wa :: m.stack }) m := by
  cases p with
  | uint =>
    obtain ⟨x, hx, hxa, rfl⟩ := ha.uint_inv
    obtain ⟨y, hy, hyb, rfl⟩ := hb.uint_inv
    show ValOutT _ (TRes.ofOpt (BinOp.evalNum .uint rfl a.1 b.1 op hacc)) (run (uTail op) _) m
    rw [hxa, hyb]
    exact utail_simT hop hand hor hacc hx hy m
  | int =>
    obtain ⟨⟨x, hx⟩, rfl, hxa⟩ := ha
    obtain ⟨⟨y, hy⟩, rfl, hyb⟩ := hb
    show ValOutT _ (TRes.ofOpt (BinOp.evalNum .int rfl a.1 b.1 op hacc)) (run (sTail op) _) m
    rw [hxa, hyb]
    exact stail_simT hop hand hor hacc hx hy m
  | bool =>
    obtain rfl : wa = .val (bword a) := ha
    obtain rfl : wb = .val (bword b) := hb
    show ValOutT _ (TRes.ofOpt (BinOp.evalBool a b op hacc)) (run (uTail op) _) m
    have cmp := cmp_tail m m.stack (bword a).2 (bword b).2
    have e : decide ((bword a).1 = (bword b).1) = decide (a = b) := by
      cases a <;> cases b <;> rfl
    cases op <;> first | exact absurd hop (by decide) | exact absurd rfl hand | exact absurd rfl hor | skip
    · exact out_bool e cmp.2.2.2.2.1
    · exact out_bool (by rw [e]) cmp.2.2.2.2.2

/-- An `int` is represented by its two's complement word: `-1` is `2^256 - 1`. -/
theorem ReprV.int_word (v : PrimTy.int.Denote) : ReprV .int v (.val (sword v.1)) := by
  obtain ⟨n, hn⟩ := v
  simp only [PrimTy.inRange, decide_eq_true_eq] at hn
  have h1 : -(H : Int) ≤ n := hn.1
  have h2 : n < (H : Int) := hn.2
  refine ⟨_, rfl, ?_⟩
  rw [sword_val (n := n) (by have := W_eq; omega) (by have := W_eq; omega)]
  exact (sgn_toWord h1 h2).symm

/-- `-x` at `int`: the negation, or a revert at `-2^255`. -/
theorem neg_simT {a : PrimTy.int.Denote} {wa : Word} (ha : ReprV .int a wa) (m : Machine) :
    ValOutT .int (TRes.ofOpt (UnOp.neg.evalT rfl a)) (run negCode (m.push wa)) m := by
  obtain ⟨⟨x, hx⟩, rfl, hax⟩ := ha
  show ValOutT .int (TRes.ofOpt (PrimTy.int.ofInt? (-a.1)))
    (run negCode { m with stack := w[x] :: m.stack }) m
  rw [neg_run m m.stack hx, hax]
  exact out_int_if m

/-- `~x` at `uint`: `NOT`. -/
theorem bnot_simT {a : PrimTy.uint.Denote} {wa : Word} (ha : ReprV .uint a wa) (m : Machine) :
    ValOutT .uint (TRes.ofOpt (UnOp.bnot.evalT rfl a)) (run [.not] (m.push wa)) m := by
  obtain ⟨x, hx, hxa, rfl⟩ := ha.uint_inv
  show ValOutT .uint (TRes.ofOpt (PrimTy.uint.ofInt? (Semantics.uintBound - 1 - a.1))) _ m
  have := W_pos
  refine out_uint_ok (r := W - 1 - x) ?_ (by omega) ?_
  · rw [hxa]
    show ((W : Nat) : Int) - 1 - (x : Int) = ((W - 1 - x : Nat) : Int)
    omega
  · simp only [run, Machine.push, exec_cons_zero, Instr.step, Machine.next, exec_nil]; rfl

/-- `int(u)`: no code, the word read signed (`2^256 - 1` is `-1`). -/
theorem toInt_simT {a : PrimTy.uint.Denote} {wa : Word} (ha : ReprV .uint a wa) (m : Machine) :
    ValOutT .int (TRes.ofOpt (UnOp.toInt.evalT rfl a)) (run [] (m.push wa)) m := by
  obtain ⟨x, hx, hxa, rfl⟩ := ha.uint_inv
  have e1 : Semantics.intBound = (H : Int) := rfl
  have e2 : Semantics.uintBound = (W : Int) := rfl
  have hs : (if a.1 < Semantics.intBound then a.1 else a.1 - Semantics.uintBound) = sgn x := by
    rw [hxa, e1, e2]; unfold sgn
    by_cases h : x < H
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]
  show ValOutT .int (TRes.ofOpt (PrimTy.int.ofInt?
    (if a.1 < Semantics.intBound then a.1 else a.1 - Semantics.uintBound))) _ m
  rw [hs, ofInt_int (sgn_range hx)]
  exact .inl ⟨_, _, rfl, ⟨⟨x, hx⟩, rfl, rfl⟩, by simp only [run, exec_nil]⟩

/-- `uint(i)`: no code, the two's complement word read unsigned (`-1` is
`2^256 - 1`). -/
theorem toUint_simT {a : PrimTy.int.Denote} {wa : Word} (ha : ReprV .int a wa) (m : Machine) :
    ValOutT .uint (TRes.ofOpt (UnOp.toUint.evalT rfl a)) (run [] (m.push wa)) m := by
  obtain ⟨⟨x, hx⟩, rfl, hxa⟩ := ha
  show ValOutT .uint (TRes.ofOpt (PrimTy.uint.ofInt? (a.1 % Semantics.uintBound))) _ m
  have hW := W_eq
  have e2 : Semantics.uintBound = (W : Int) := rfl
  have hx' : a.1 % Semantics.uintBound = (x : Int) := by
    rw [hxa, e2]; unfold sgn
    by_cases h : x < H
    · rw [if_pos h]; exact Int.emod_eq_of_lt (by omega) (by omega)
    · rw [if_neg h, Int.sub_emod_right]; exact Int.emod_eq_of_lt (by omega) (by omega)
  exact out_uint_ok hx' hx (by simp only [run, exec_nil])

/-- The operators with an `op=` form are compiled with their checks, at `uint`
and at `int`. -/
theorem compound_frag {op : BinOp} {p : PrimTy} (h : op.hasCompoundAssign = true)
    (hp : p ≠ .bool) :
    binInFrag op p = true ∧ op ≠ .and ∧ op ≠ .or ∧ op.ret p = p ∧
      op.retTy (.prim p) = .prim p := by
  cases op <;> cases p <;>
    simp_all [BinOp.hasCompoundAssign, binInFrag, BinOp.ret, BinOp.retTy, BinOp.isArith]

/-- `a ⊕= b`'s operator and its checks, typed: `compoundT` is `evalT` at an
operator with an `op=` form. -/
theorem compound_simT {op : BinOp} (hop : op.hasCompoundAssign = true) {p : PrimTy}
    (hp : p.isNumeric = true) {a b : p.Denote} {wa wb : Word} (ha : ReprV p a wa)
    (hb : ReprV p b wb) (m : Machine) :
    ValOutT p (TRes.ofOpt (Solidity.compoundT op p (PrimTy.key a) (PrimTy.key b)))
      (run (binTail p op) { m with stack := wb :: wa :: m.stack }) m := by
  have hacc : op.accepts p = true := by
    cases op <;> first | exact absurd hop (by decide) | exact hp
  cases p with
  | bool => cases hp
  | uint =>
    obtain ⟨hfrag, hand, hor, -⟩ := compound_frag hop (p := .uint) (by decide)
    have ht := tail_simT hfrag hand hor hacc ha hb m
    cases op <;> first | exact absurd hop (by decide) | exact ht
  | int =>
    obtain ⟨hfrag, hand, hor, -⟩ := compound_frag hop (p := .int) (by decide)
    have ht := tail_simT hfrag hand hor hacc ha hb m
    cases op <;> first | exact absurd hop (by decide) | exact ht

/-- The step of `++`, typed: `PUSH 1` and the operator's tail, `x += 1`. -/
theorem bump_simT {p : PrimTy} (hp : p.isNumeric = true) (op : IncDec) {a : p.Denote} {w : Word}
    (h : ReprV p a w) (m : Machine) :
    ValOutT p (TRes.ofOpt (Solidity.bumpT op p (PrimTy.key a)))
      (run ([.push w[1]] ++ binTail p op.binOp) { m with stack := w :: m.stack }) m := by
  rw [run_append_ok (m' := { m with stack := w[1] :: w :: m.stack }) rfl]
  cases p with
  | bool => cases hp
  | uint =>
    have h1 : ReprV .uint (⟨1, rfl⟩ : PrimTy.uint.Denote) w[1] := ⟨_, rfl, rfl⟩
    have ht := tail_simT (op := op.binOp) (by cases op <;> rfl) (by cases op <;> decide)
      (by cases op <;> decide) (by cases op <;> rfl) h h1 m
    cases op <;> exact ht
  | int =>
    have h1 : ReprV .int (⟨1, rfl⟩ : PrimTy.int.Denote) w[1] :=
      ⟨_, rfl, by show (1 : Int) = sgn 1; unfold sgn; rw [if_pos (by unfold H; decide)]; rfl⟩
    have ht := tail_simT (op := op.binOp) (by cases op <;> rfl) (by cases op <;> decide)
      (by cases op <;> decide) (by cases op <;> rfl) h h1 m
    cases op <;> exact ht

end Words

/-! ## Locations -/

/-- With `… s i` on the stack, the bounds check passes when `i` is below the
word at `s` and reverts otherwise: `values[3]` with three values reverts. -/
theorem boundsCheck_run (m : Machine) (st : List Word) (rest : List Instr) (i : Nat) (s : Slot)
    (hi : i < W) :
    run (boundsCheck ++ rest) { m with stack := w[i] :: .slot s :: st } =
      if i < m.store s then run rest { m with stack := w[i] :: .slot s :: st } else .revert := by
  by_cases h : i < m.store s
  · simp [run, boundsCheck, assertTop, Instr.step, Machine.next, h, bword]
  · simp [run, boundsCheck, assertTop, Instr.step, Machine.next, h, bword]

/-- `z` additions of `i` to a slot add `z·i`: element `i` of `Person[]` is `3·i` past
`keccak(9)`. -/
theorem addRep_run (m : Machine) (st : List Word) (i : Nat) (hi : i < W) :
    ∀ (z : Nat) (t : Slot), run (addRep z) { m with stack := .slot t :: w[i] :: st } =
      .ok { m with stack := .slot (t.add (z * i)) :: w[i] :: st } 0
  | 0, t => by simp [addRep]
  | z + 1, t => by
    rw [addRep, run_append_ok (m' := { m with stack := .slot (t.add i) :: w[i] :: st })
      (by simp [run, Instr.step, Machine.next]), addRep_run m st i hi z (t.add i),
      Slot.add_add, Nat.succ_mul, Nat.add_comm (z * i)]

/-- Element `i` of the array at `s`, whose elements take `z` slots, is at
`keccak(s) + i·z`: `persons[1].age` is `keccak(9) + 3 + 2`. -/
theorem elemSlot_run (m : Machine) (st : List Word) (i z : Nat) (s : Slot) (hi : i < W) :
    run (elemSlot z) { m with stack := w[i] :: .slot s :: st } =
      .ok { m with stack := .slot (.data s (i * z)) :: st } 0 := by
  rw [elemSlot, List.append_assoc,
    run_append_ok (m' := { m with stack := .slot (.data s 0) :: w[i] :: st })
    (by simp [run, Instr.step, Machine.next]), run_append_ok (addRep_run m st i hi z _)]
  simp [run, Instr.step, Machine.next, Slot.add, Nat.mul_comm]

/-- A fixed-size array's bound is its type's, a constant: `fixedValues[k]`
checks `k < 3` and reads no length slot. -/
theorem fixedCheck_run (m : Machine) (st : List Word) (rest : List Instr) (n i : Nat) (s : Slot)
    (hn : n < W) (hi : i < W) :
    run (fixedCheck n ++ rest) { m with stack := w[i] :: .slot s :: st } =
      if i < n then run rest { m with stack := w[i] :: .slot s :: st } else .revert := by
  by_cases h : i < n
  · simp [run, fixedCheck, assertTop, Instr.step, Machine.next, h, bword, Nat.mod_eq_of_lt hn]
  · simp [run, fixedCheck, assertTop, Instr.step, Machine.next, h, bword, Nat.mod_eq_of_lt hn]

/-- Element `i` of the fixed-size array laid out from `s`, whose elements take
`z` slots, is at `s + i·z`: `fixedTokens[1].value` is `fixedTokens`'s slot plus `1`. -/
theorem fixedSlot_run (m : Machine) (st : List Word) (i z : Nat) (s : Slot) (hi : i < W) :
    run (fixedSlot z) { m with stack := w[i] :: .slot s :: st } =
      .ok { m with stack := .slot (s.add (i * z)) :: st } 0 := by
  rw [fixedSlot, List.append_assoc,
    run_append_ok (m' := { m with stack := .slot s :: w[i] :: st })
    (by simp [run, Instr.step, Machine.next]), run_append_ok (addRep_run m st i hi z _)]
  simp [run, Instr.step, Machine.next, Nat.mul_comm]


/-! ## The simulation relation -/

/-- The machine's environment is the transaction's: `CALLER` pushes
`msg.sender`, `ADDRESS` the contract's address, `address(this)`, and each of
them a word by its type. -/
def EnvSim (t : TTx) (m : Machine) : Prop :=
  t.msgSender.1 = m.caller.1 ∧ t.msgValue.1 = m.callvalue.1 ∧ t.timestamp.1 = m.timestamp.1 ∧
    t.selfAddress.1 = m.self.1

/-- `net(a)`: the ledger's entry at `a`, `0` where nothing was booked. -/
def netAt (net : Ledger) (a : Int) : Int := (Semantics.lookupBy a (Ledger.entries net)).getD 0

/-- The ledger after a payment of `y` to `x`: as it was when `x` is the
contract itself, else `x`'s entry down by `y`. -/
theorem netAt_pay {C : Contract} {Γ : Ctx} (τ : State C Γ)
    (x : PrimTy.uint.Denote) (y a : Int) :
    netAt (τ.pay x y).net a =
      if x.1 = τ.tx.selfAddress.1 then netAt τ.net a
      else if a = x.1 then netAt τ.net x.1 - y else netAt τ.net a := by
  by_cases h1 : x.1 = τ.tx.selfAddress.1
  · simp only [State.pay, netAt, h1, if_true]
  · simp only [State.pay, netAt, h1, if_false, Ledger.entries_setBy]
    by_cases h2 : a = x.1
    · subst a
      simp only [Semantics.lookupBy_setBy_self, if_true, Option.getD_some, Ledger.lookup_entries]
    · simp only [Semantics.lookupBy_setBy_ne h2, h2, if_false]

variable {C : Contract} {L : Nat}

/-- A primitive storage value is read as the word at its slot: `alice.age`
pushes slot `13`'s word, an `int` its two's complement. -/
theorem prim_read {st : WordStore} {p : PrimTy} {s : Slot} {sv : SVal (.prim p)}
    (h : ReprAt st L (.prim p) s sv) : ∃ v, sv = .prim v ∧ ReprV p v (.val (st.cells s)) := by
  cases h with
  | prim h => exact ⟨_, rfl, h⟩

/-! ## Statements -/

/-- A write to a primitive leaves every array's length. -/
theorem upd_len {st : WordStore} {a : Bool} {p : PrimTy} {r : SRef C (.prim p)} {s : Slot}
    (hp : PathSlot C a r s) (v : Nat) :
    ∀ x, LenSlot C x → st x ≤ WordStore.write st s v x := fun x hx => by
  rw [WordStore.write_other _ _ fun he => len_prim_disjoint hx (by rw [he]; exact hp.primSlot)]
  exact Nat.le_refl _

/-- `delete`'s writes: `0` at each leaf, the slot kept on the stack; `delete alice;` writes `11`,
`12`, `13`. -/
theorem zeroCode_run (m : Machine) (st : List Word) (s : Slot) : ∀ (os : List Nat),
    (∀ o ∈ os, o < W) →
    run (zeroCode os) { m with stack := .slot s :: st } =
      .ok { m with stack := .slot s :: st, store := zeroAt m.store s os } 0
  | [], _ => rfl
  | o :: os, hos => by
    rw [zeroCode, List.flatMap_cons, ← zeroCode,
      run_append_ok (m' := { m with stack := .slot s :: st, store := WordStore.write m.store (s.add o) 0 })
        (by simp [run, Instr.step, Machine.next, Nat.mod_eq_of_lt (hos o List.mem_cons_self)])]
    exact zeroCode_run { m with store := WordStore.write m.store (s.add o) 0 } st s os
      fun o' h' => hos o' (List.mem_cons_of_mem _ h')

/-- `pop` on the array at `s`: revert on an empty array, else the length
decremented. -/
theorem popCode_run (m : Machine) (st : List Word) (s : Slot) (hW : m.store s < W) :
    run popCode { m with stack := .slot s :: st } =
      if m.store s = 0 then .revert
      else .ok { m with stack := st, store := WordStore.write m.store s (m.store s - 1) } 0 := by
  by_cases h : m.store s = 0
  · simp [run, popCode, assertTop, Instr.step, Machine.next, h]
  · have e : (m.store s + (W - 1)) % W = m.store s - 1 := by
      rw [show m.store s + (W - 1) = (m.store s - 1) + W by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    simp [run, popCode, assertTop, Instr.step, Machine.next, h]
    rw [e]

/-- A value written to a slot is represented there: a `uint` or a `bool` as
itself, an `int` as its word. -/
theorem repr_write {p : PrimTy} {v : p.Denote} {w : Word}
    (hv : ReprV p v w) (st : WordStore) (s : Slot) :
    ∃ a : Fin W, w = .val a ∧ ReprAt (WordStore.write st s a.1) L (.prim p) s (.prim v) := by
  cases p with
  | uint =>
    obtain ⟨a, rfl, ha⟩ := hv
    exact ⟨a, rfl, .prim (by rw [WordStore.write_cells_same]; exact ReprV.uint_of ha)⟩
  | bool =>
    have := hv.bool_inv
    subst this
    exact ⟨_, rfl, .prim (by rw [WordStore.write_cells_same]; rfl)⟩
  | int =>
    obtain ⟨a, rfl, hax⟩ := hv
    exact ⟨a, rfl, .prim ⟨a, by rw [WordStore.write_cells_same], hax⟩⟩

/-- `x++`'s code as an expression: `… old → … new v`, with `v` the new word
for `++x` and the old one for `x++`. -/
theorem bumpCode_simT {p : PrimTy} (hp : p.isNumeric = true) (op : IncDec) {a : p.Denote}
    {w : Word} (h : ReprV p a w) (m : Machine) :
    (∃ vn wn, Solidity.bumpT op p (PrimTy.key a) = some vn ∧ ReprV p vn wn ∧
        run (bumpCode p op) { m with stack := w :: m.stack } =
          .ok { m with stack := wn :: (if op.isPre then wn else w) :: m.stack } 0) ∨
      (Solidity.bumpT op p (PrimTy.key a) = none ∧
        run (bumpCode p op) { m with stack := w :: m.stack } = .revert) := by
  unfold bumpCode
  cases hpre : op.isPre
  · -- `x++`: the old word kept under the new one
    have hv := (bump_simT hp op h { m with stack := w :: m.stack }).opt_cases
    simp only [if_false, Bool.false_eq_true]
    rw [show [Instr.dup 1, .push w[1]] ++ binTail p op.binOp =
      [Instr.dup 1] ++ ([.push w[1]] ++ binTail p op.binOp) from rfl,
      run_append_ok (m' := { m with stack := w :: w :: m.stack }) rfl]
    rcases hv with ⟨vn, wn, h1, h2, h3⟩ | ⟨h1, h3⟩
    · exact .inl ⟨vn, wn, h1, h2, h3⟩
    · exact .inr ⟨h1, h3⟩
  · -- `++x`: the new word twice
    have hv := (bump_simT hp op h m).opt_cases
    simp only [if_true]
    rcases hv with ⟨vn, wn, h1, h2, h3⟩ | ⟨h1, h3⟩
    · exact .inl ⟨vn, wn, h1, h2, by rw [run_append_ok h3]; rfl⟩
    · exact .inr ⟨h1, run_append_revert h3⟩

/-- `st` with `vs` written at `d + o` for the offsets `os`, in order. -/
def storeAt (st : WordStore) (d : Slot) : List Nat → List Nat → WordStore
  | o :: os, v :: vs => storeAt (WordStore.write st (d.add o) v) d os vs
  | _, _ => st

/-- Writing at some offsets leaves the other slots. -/
theorem storeAt_other {d x : Slot} : ∀ {os vs : List Nat} {st : WordStore},
    (∀ o ∈ os, x ≠ d.add o) → storeAt st d os vs x = st x
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | o :: os, v :: vs, st, h => by
    simp only [storeAt]
    rw [storeAt_other fun o' ho' => h o' (List.mem_cons_of_mem _ ho')]
    exact WordStore.write_other _ _ (h o List.mem_cons_self)

/-- Writing `f o` at each `d + o` leaves `f o` there. -/
theorem storeAt_map (f : Nat → Nat) (hf : ∀ o, f o < W) {d : Slot} {o : Nat} : ∀ {os : List Nat} {st : WordStore},
    o ∈ os → storeAt st d os (os.map f) (d.add o) = f o
  | o' :: os, st, h => by
    simp only [List.map_cons, storeAt]
    by_cases ho : o ∈ os
    · exact storeAt_map f hf ho
    · obtain rfl : o = o' := by
        rcases List.mem_cons.1 h with h | h
        · exact h
        · exact absurd h ho
      rw [storeAt_other fun o'' ho'' he => ho (by rw [Slot.add_inj he]; exact ho''), WordStore.write_same_of_lt _ _ _ (hf _)]

/-- A write to a static value's leaves leaves every array's length. -/
theorem storeAt_len {st : WordStore} {a : Bool} {R : RefTy} {r : SRef C (.ref R)}
    {d : Slot} (hp : PathSlot C a r d) (hst : static (.ref R) = true)
    (vs : List Nat) : ∀ x, LenSlot C x → st x ≤ storeAt st d (leaves (.ref R)).reverse vs x :=
  fun x hx => by
    rw [storeAt_other fun o ho he => len_prim_disjoint hx (by
      obtain ⟨T₀, h0, oc⟩ := hp.occAt (leavesF_occAt _ _ d o hst (List.mem_reverse.1 ho))
      exact ⟨r.root, T₀, h0, he ▸ oc⟩)]
    exact Nat.le_refl _

/-- A `push`'s writes: the length one more, and the new element's primitives. -/
theorem push_len {st st' : WordStore} {a : Bool} {E : Ty} {r : SRef C (.ref (.array E))}
    {s : Slot} (hp : PathSlot C a r s) (n : Nat)
    (hs : st' s = st s + 1)
    (hw : ∀ x, x ≠ s → st' x ≠ st x → OccAt true E (.data s (n * size E)) x) :
    ∀ x, LenSlot C x → st x ≤ st' x := fun x hx => by
  by_cases hxs : x = s
  · subst hxs; omega
  · by_cases he : st' x = st x
    · omega
    · exfalso
      obtain ⟨T₀, h0, oc⟩ := hp.occAt (OccAt.elem n (hw x hxs he))
      exact len_prim_disjoint hx ⟨r.root, T₀, h0, oc⟩

/-- `loadLeaves`: the words at `s + o`, pushed in order below the slot. -/
theorem loadLeaves_run (m : Machine) (s : Slot) : ∀ (os : List Nat), (∀ o ∈ os, o < W) →
    ∀ (st : List Word),
    run (loadLeaves os) { m with stack := .slot s :: st } =
      .ok { m with stack := .slot s ::
        ((os.map fun o => m.store.cells (s.add o)).reverse.map Word.val ++ st) } 0
  | [], _, st => rfl
  | o :: os, hos, st => by
    rw [loadLeaves, List.flatMap_cons, ← loadLeaves,
      run_append_ok (m' := { m with stack := .slot s :: .val (m.store.cells (s.add o)) :: st })
        (by simp [run, Instr.step, Machine.next, Nat.mod_eq_of_lt (hos o List.mem_cons_self)]),
      loadLeaves_run m s os fun o' h' => hos o' (List.mem_cons_of_mem _ h')]
    simp

/-- `storeLeaves`: each word stored at `d + o`. -/
theorem storeLeaves_run (m : Machine) (d : Slot) : ∀ (os : List Nat) (vs : List (Fin W))
    (st : List Word) (mst : WordStore), (∀ o ∈ os, o < W) → os.length = vs.length →
    run (storeLeaves os) { m with stack := .slot d :: (vs.map Word.val ++ st), store := mst } =
      .ok { m with stack := .slot d :: st, store := storeAt mst d os (vs.map Fin.val) } 0
  | [], [], st, mst, _, _ => rfl
  | o :: os, v :: vs, st, mst, hos, h => by
    rw [storeLeaves, List.flatMap_cons, ← storeLeaves,
      run_append_ok
        (m' := { m with
          stack := .slot d :: (vs.map Word.val ++ st), store := WordStore.write mst (d.add o) v.1 })
        (by simp [run, Instr.step, Machine.next, Nat.mod_eq_of_lt (hos o List.mem_cons_self)]),
      storeLeaves_run m d os vs st _ (fun o' h' => hos o' (List.mem_cons_of_mem _ h'))
        (by simpa using h)]
    rfl
  | [], _ :: _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h

/-- A copied struct or fixed-size array is laid over what is there. -/
theorem write_ref {R : RefTy} (stor : Solidity.Storage C) (r : SRef C (.ref R))
    (sv : SVal (.ref R)) {old : SVal (.ref R)} (hold : stor.find r = some old) :
    stor.write r sv = stor.save r (old.overlay sv) := by
  simp only [Solidity.Storage.write, SVal.isPrim, Ty.isPrimitive, Bool.false_eq_true,
    ↓reduceIte, hold, bind, Option.bind]

/-- A slot is not one of the slots hashed from it. -/
theorem Slot.ne_data (s : Slot) (n : Nat) : s ≠ .data s n := fun h => by
  have := congrArg Slot.depth h; simp [Slot.depth] at this

/-- The length checked, grown and the new element's slot computed: `… s →
… keccak(s) + len·z`, with `len + 1` stored at `s`. -/
theorem pushSlotCode_run (m : Machine) (st : List Word) (z : Nat) (s : Slot)
    (hl : m.store s < Lmax) :
    run (pushSlotCode z) { m with stack := .slot s :: st } =
      .ok { m with
        stack := .slot (.data s (m.store s * z)) :: st
        store := WordStore.write m.store s (m.store s + 1) } 0 := by
  have hW := Lmax_lt_W
  have e : (m.store s + 1) % W = m.store s + 1 := Nat.mod_eq_of_lt (by omega)
  have h1 : run ([.dup 1, .sload, .push (.val wLmax), .dup 2, .lt] ++ assertTop ++
      [.push w[1], .dup 2, .add, .dup 3, .sstore]) { m with stack := .slot s :: st } =
      .ok { m with
        stack := .val (m.store.cells s) :: .slot s :: st
        store := WordStore.write m.store s (m.store s + 1) } 0 := by
    simp [run, assertTop, Instr.step, Machine.next, hl, e, bword]
  rw [pushSlotCode, run_append_ok h1]
  exact elemSlot_run { m with store := WordStore.write m.store s (m.store s + 1) } st (m.store s) z s
    (m.store.cells s).2

/-- A slot holding `0` represents a primitive type's default. -/
theorem zero_prim_repr {st : WordStore} {p : PrimTy} {x : Slot}
    (h : st x = 0) : ReprAt st L (.prim p) x (SVal.dflt (.prim p)) :=
  .prim (by rw [show st.cells x = ⟨0, W_pos⟩ from Fin.ext h]; exact ReprV.dflt_zero p)

/-- The slot a `push` of a primitive lands on: its default. -/
theorem pushSlot_prim (p : PrimTy) (l : List (SVal (.prim p))) :
    (pushSlot (.prim p) l).1 = SVal.dflt (.prim p) := by
  cases l <;> rfl

/-- **A `push` in bounds**: the array not full, and the push its save. -/
theorem push_eq {E : Ty} {stor : Solidity.Storage C} {r : SRef C (.ref (.array E))} {k : Nat}
    {e : SVec E k} {sh : SList E} {hk : k < 2 ^ 256}
    (hf : stor.find r = some (.array e sh hk)) (val : SVal E → Option (SVal E)) {x : SVal E}
    (hx : val (pushSlot E sh.toList).1 = some x) (hb : k + 1 < 2 ^ 256) :
    stor.full r = false ∧ stor.push r val =
      stor.save r (.array (SVec.ofList (e.toList ++ [x])) (.ofList (pushSlot E sh.toList).2)
        (SVec.snoc_lt_bound e x hb)) := by
  refine ⟨?_, ?_⟩
  · simp only [Solidity.Storage.full, hf, SVal.view_array, hb, decide_true, Bool.not_true]
  · simp only [Solidity.Storage.push, hf, bind, Option.bind, SVal.view_array, hx, dif_pos hb]

end Evm
end Solidity
