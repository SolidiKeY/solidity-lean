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

**Word arithmetic.**  The operators' tails are proved against the integer
arithmetic of the untyped operators (`applyBinOp`, `checkArith`,
`Semantics.lean`), on the integers a word represents (`ReprW`, `ValOutW`,
private here): `tail_sim` and its signed half.  The typed operators are that
arithmetic range-checked (`BinOp.evalT_erase`, `UnOp.evalT_erase`,
`Semantics/Ops.lean`), so the typed tails (`tail_simT`, `neg_simT`,
`bnot_simT`, `compound_simT`, `bump_simT`) read them off it; nothing outside
this file reads an untyped value.
-/

namespace Solidity
namespace Evm

/-! ## Values, typed -/

/-- A `uint` is represented by itself, a word below `2^256`: `total` read as `7` pushes `7`. -/
theorem ReprV.uint_inv {v : PrimTy.uint.Denote} {w : Word} (h : ReprV .uint v w) :
    ∃ a : Nat, a < W ∧ v.1 = a ∧ w = .val a := by
  obtain ⟨n, hn⟩ := v
  simp only [PrimTy.inRange, decide_eq_true_eq] at hn
  refine ⟨n.toNat, ?_, by simp only; omega, h⟩
  unfold W; omega

/-- A `bool` is represented by `1` or `0`: `flags[3]` read as `true` pushes `1`. -/
theorem ReprV.bool_inv {b : PrimTy.bool.Denote} {w : Word} (h : ReprV .bool b w) :
    w = .val (bword b) := h

/-- An `int` is represented by a word, its two's complement: `-1` is `2^256 - 1`. -/
theorem ReprV.int_inv {v : PrimTy.int.Denote} {w : Word} (h : ReprV .int v w) :
    ∃ a : Nat, a < W ∧ v.1 = sgn a ∧ w = .val a := by
  obtain ⟨a, rfl, ha, hv⟩ := h
  exact ⟨a, ha, hv, rfl⟩

/-- A word below `2^256` represents itself as a `uint`: `total = 7;` pushes `7`. -/
theorem ReprV.uint_of {v : PrimTy.uint.Denote} {a : Nat} (h : v.1 = a) : ReprV .uint v (.val a) := by
  show Word.val a = .val v.1.toNat
  rw [h, Int.toNat_natCast]

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

open Semantics SemanticsProperties

/-! ## The guard sequences -/

/-- A sum below `2^256` does not wrap: `3 + 4` is `7`. -/
theorem mod_W_of_lt {x : Nat} (h : x < W) : x % W = x := Nat.mod_eq_of_lt h

/-- A sum of two words that wraps loses exactly `2^256`: `(2^256 - 1) + 1` wraps to `0`. -/
theorem mod_W_of_ge {x : Nat} (h₁ : W ≤ x) (h₂ : x < W + W) : x % W = x - W := by
  rw [Nat.mod_eq_sub_mod h₁, Nat.mod_eq_of_lt (by omega)]

/-- `OR` of two comparison words is `0` exactly when both are false (the `*` guard). -/
@[simp] theorem bword_or_eq_zero (x y : Bool) :
    (bword x ||| bword y) = 0 ↔ x = false ∧ y = false := by
  cases x <;> cases y <;> decide

/-- `a + b` with solc's overflow check: the sum wraps exactly when it is below
`a`.  With `a = 2^256 - 1` and `b = 1` the word is `0`, below `a`, and the code
reverts; with `a = 3`, `b = 4` it is `7`. -/
theorem add_tail (m : Machine) (st : List Word) {a b : Nat} (ha : a < W) (hb : b < W) :
    run (uTail .add) { m with stack := .val b :: .val a :: st } =
      if a + b < W then .ok { m with stack := .val (a + b) :: st } 0 else .revert := by
  simp [run, uTail, assertTop, Instr.step, Machine.next]
  by_cases h : a + b < W
  · rw [mod_W_of_lt h]; simp [h, show ¬ a + b < a by omega, Instr.step, Machine.next]
  · rw [mod_W_of_ge (by omega) (by omega)]
    simp [h, Instr.step, show a + b - W < a by omega]

/-- `a - b` with solc's underflow check: revert when `b > a`.  `3 - 4`
reverts, `4 - 3` is `1`. -/
theorem sub_tail (m : Machine) (st : List Word) {a b : Nat} (ha : a < W) (hb : b < W) :
    run (uTail .sub) { m with stack := .val b :: .val a :: st } =
      if b ≤ a then .ok { m with stack := .val (a - b) :: st } 0 else .revert := by
  simp [run, uTail, assertTop, Instr.step, Machine.next]
  by_cases h : b ≤ a
  · have e : (a + (W - b)) % W = a - b := by
      rw [show a + (W - b) = (a - b) + W by omega, Nat.add_mod_right, mod_W_of_lt (by omega)]
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
    · right; rw [mod_W_of_lt h, Nat.mul_div_cancel_left _ hpos]

/-- `a * b` with solc's overflow check. -/
theorem mul_tail (m : Machine) (st : List Word) {a b : Nat} (ha : a < W) :
    run (uTail .mul) { m with stack := .val b :: .val a :: st } =
      if a * b < W then .ok { m with stack := .val (a * b) :: st } 0 else .revert := by
  simp [run, uTail, assertTop, Instr.step, Machine.next]
  have key := mul_ok_iff (a := a) (b := b)
  by_cases h : a * b < W
  · simp only [h, if_true]
    have e : b * a % W = a * b := by rw [Nat.mul_comm, mod_W_of_lt h]
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
theorem div_tail (m : Machine) (st : List Word) (a b : Nat) :
    run (uTail .div) { m with stack := .val b :: .val a :: st } =
      if b = 0 then .revert else .ok { m with stack := .val (a / b) :: st } 0 := by
  by_cases h : b = 0
  · subst h; rfl
  · simp [run, uTail, assertTop, Instr.step, Machine.next, h]

/-- `a % b`, reverting on `b = 0`. -/
theorem mod_tail (m : Machine) (st : List Word) (a b : Nat) :
    run (uTail .mod) { m with stack := .val b :: .val a :: st } =
      if b = 0 then .revert else .ok { m with stack := .val (a % b) :: st } 0 := by
  by_cases h : b = 0
  · subst h; rfl
  · simp [run, uTail, assertTop, Instr.step, Machine.next, h]

/-- A comparison or an equality: one or two instructions and no guard. -/
theorem cmp_tail (m : Machine) (st : List Word) (a b : Nat) :
    run (uTail .lt) { m with stack := .val b :: .val a :: st } =
        .ok { m with stack := .val (bword (decide (a < b))) :: st } 0 ∧
    run (uTail .gt) { m with stack := .val b :: .val a :: st } =
        .ok { m with stack := .val (bword (decide (b < a))) :: st } 0 ∧
    run (uTail .le) { m with stack := .val b :: .val a :: st } =
        .ok { m with stack := .val (bword (decide (a ≤ b))) :: st } 0 ∧
    run (uTail .ge) { m with stack := .val b :: .val a :: st } =
        .ok { m with stack := .val (bword (decide (b ≤ a))) :: st } 0 ∧
    run (uTail .eqB) { m with stack := .val b :: .val a :: st } =
        .ok { m with stack := .val (bword (decide (a = b))) :: st } 0 ∧
    run (uTail .neB) { m with stack := .val b :: .val a :: st } =
        .ok { m with stack := .val (bword (!decide (a = b))) :: st } 0 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [run, uTail, Instr.step, Machine.next, bword]
  · simp [run, uTail, Instr.step, Machine.next, bword]
  · simp [run, uTail, Instr.step, Machine.next, bword]
    by_cases h : a = b <;> simp [h, eq_comm]
  · simp [run, uTail, Instr.step, Machine.next, bword]
    by_cases h : a = b <;> simp [h, eq_comm]

/-! ## Word arithmetic -/

/-- A stack word represents an integer value of primitive type `p`: a `uint`
below `2^256` as itself, a `bool` as `1` or `0`, an `int` as its two's
complement word.  The untyped reading of `ReprV` (`reprV_iff`), on which the
operators' tails are proved. -/
private def ReprW : PrimTy → Value → Word → Prop
  | .uint, .int n, .val w => 0 ≤ n ∧ n < W ∧ w = n.toNat
  | .bool, .bool b, .val w => w = bword b
  | .int, .int n, .val w => w < W ∧ n = sgn w
  | _, _, _ => False


/-- A `uint` is represented by itself, a word below `2^256`: `total` read as `7` pushes `7`. -/
private theorem ReprW.uint_inv {v : Value} {w : Word} (h : ReprW .uint v w) :
    ∃ a : Nat, a < W ∧ v = .int a ∧ w = .val a := by
  match v, w, h with
  | .int n, .val w, ⟨h0, h1, h2⟩ =>
    exact ⟨n.toNat, by omega, by rw [Int.toNat_of_nonneg h0], h2 ▸ rfl⟩

/-- A `bool` is represented by `1` or `0`: `flags[3]` read as `true` pushes `1`. -/
private theorem ReprW.bool_inv {v : Value} {w : Word} (h : ReprW .bool v w) :
    ∃ b : Bool, v = .bool b ∧ w = .val (bword b) := by
  match v, w, h with
  | .bool b, .val w, h => exact ⟨b, rfl, h ▸ rfl⟩

/-- An `int` is represented by a word, its two's complement: `-1` is `2^256 - 1`. -/
private theorem ReprW.int_inv {v : Value} {w : Word} (h : ReprW .int v w) :
    ∃ a : Nat, a < W ∧ v = .int (sgn a) ∧ w = .val a := by
  match v, w, h with
  | .int n, .val w, ⟨h1, h2⟩ => exact ⟨w, h1, by rw [h2], rfl⟩

/-- An `int256` is represented by its word: `x = -1;` pushes `2^256 - 1`. -/
private theorem ReprW.int {n : Int} (h1 : -(H : Int) ≤ n) (h2 : n < H) :
    ReprW .int (.int n) (.val (toWord n)) :=
  ⟨toWord_lt (by have := W_eq; omega) (by have := W_eq; omega), (sgn_toWord h1 h2).symm⟩

/-- `1`, the step of `++`, at a numeric type. -/
private theorem ReprW.one {p : PrimTy} (hp : p ≠ .bool) : ReprW p (.int 1) (.val 1) := by
  have := W_pos; have := W_eq; have := H_pos
  cases p with
  | uint => exact ⟨by decide, by unfold W at *; omega, rfl⟩
  | int => exact ⟨by unfold W at *; omega, by simp [sgn]; unfold H at *; omega⟩
  | bool => exact absurd rfl hp

/-- A word below `2^256` represents itself as a `uint`: `total = 7;` pushes `7`. -/
private theorem ReprW.uint {a : Nat} (h : a < W) : ReprW .uint (.int a) (.val a) :=
  ⟨Int.natCast_nonneg a, by omega, rfl⟩

/-- `true` is `1`, `false` is `0`: `require(true);` pushes `1`. -/
private theorem ReprW.bool (b : Bool) : ReprW .bool (.bool b) (.val (bword b)) := rfl

/-- An expression's outcome, interpreter and machine together: a value and the
word representing it pushed, or both revert. -/
private def ValOutW (p : PrimTy) (res : Res Value) (out : Out) (m : Machine) : Prop :=
  (∃ v w, res = .ok v ∧ ReprW p v w ∧ out = .ok (m.push w) 0) ∨
    (res = .error .revert ∧ out = .revert)

/-- The interpreter's `uint256` bound is the machine's word bound: `2^256`. -/
private theorem uintBound_eq : uintBound = (W : Int) := rfl

/-- On `uint`s the interpreter's truncating division is the machine's: `7 / 2` is `3`. -/
private theorem tdiv_natCast (a b : Nat) : Int.tdiv (a : Int) (b : Int) = ((a / b : Nat) : Int) := rfl
/-- On `uint`s the interpreter's `%` is the machine's: `7 % 2` is `1`. -/
private theorem tmod_natCast (a b : Nat) : Int.tmod (a : Int) (b : Int) = ((a % b : Nat) : Int) := rfl

/-- The range check at `uint`. -/
private theorem checkArith_uint (n : Int) :
    checkArith (.prim .uint) (.int n) = if 0 ≤ n ∧ n < W then .ok (.int n) else .error .revert :=
  rfl

/-- The range check at `int`. -/
private theorem checkArith_int (n : Int) :
    checkArith (.prim .int) (.int n) =
      if -(H : Int) ≤ n ∧ n < H then .ok (.int n) else .error .revert :=
  rfl

/-- The interpreter's checked `+`, `-`, `*`, `/`, `%` on `uint`s. -/
private theorem src_arith {a b : Nat} (ha : a < W) :
    (applyBinOp .add (.int a) (.int b) >>= checkArith (BinOp.add.retTy (.prim .uint))) =
      (if a + b < W then .ok (.int ↑(a + b)) else .error .revert) ∧
    (applyBinOp .sub (.int a) (.int b) >>= checkArith (BinOp.sub.retTy (.prim .uint))) =
      (if b ≤ a then .ok (.int ↑(a - b)) else .error .revert) ∧
    (applyBinOp .mul (.int a) (.int b) >>= checkArith (BinOp.mul.retTy (.prim .uint))) =
      (if a * b < W then .ok (.int ↑(a * b)) else .error .revert) ∧
    (applyBinOp .div (.int a) (.int b) >>= checkArith (BinOp.div.retTy (.prim .uint))) =
      (if b = 0 then .error .revert else .ok (.int ↑(a / b))) ∧
    (applyBinOp .mod (.int a) (.int b) >>= checkArith (BinOp.mod.retTy (.prim .uint))) =
      (if b = 0 then .error .revert else .ok (.int ↑(a % b))) := by
  have ret : ∀ op : BinOp, op.isArith = true → op.retTy (.prim .uint) = .prim .uint :=
    fun op h => by simp [BinOp.retTy, h]
  have okb : ∀ (x : Value) (f : Value → Res Value), (Except.ok x >>= f) = f x := fun _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [ret .add rfl, show applyBinOp .add (.int a) (.int b) = .ok (.int (↑a + ↑b)) from rfl,
      okb, checkArith_uint]
    by_cases h : a + b < W
    · rw [if_pos (by omega), if_pos h]; rfl
    · rw [if_neg (by omega), if_neg h]
  · rw [ret .sub rfl, show applyBinOp .sub (.int a) (.int b) = .ok (.int (↑a - ↑b)) from rfl,
      okb, checkArith_uint]
    by_cases h : b ≤ a
    · rw [if_pos (by omega), if_pos h, Int.ofNat_sub h]
    · rw [if_neg (by omega), if_neg h]
  · rw [ret .mul rfl, show applyBinOp .mul (.int a) (.int b) = .ok (.int (↑a * ↑b)) from rfl,
      okb, checkArith_uint, ← Int.natCast_mul]
    by_cases h : a * b < W
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]
  · rw [ret .div rfl, show applyBinOp .div (.int a) (.int b) =
      (if (b : Int) = 0 then .error .revert else .ok (.int (Int.tdiv ↑a ↑b))) from rfl]
    by_cases h : b = 0
    · subst h; rfl
    · rw [if_neg (by omega), if_neg h, okb, checkArith_uint, tdiv_natCast]
      have := Nat.div_le_self a b
      generalize a / b = q at this ⊢
      rw [if_pos (by omega)]
  · rw [ret .mod rfl, show applyBinOp .mod (.int a) (.int b) =
      (if (b : Int) = 0 then .error .revert else .ok (.int (Int.tmod ↑a ↑b))) from rfl]
    by_cases h : b = 0
    · subst h; rfl
    · rw [if_neg (by omega), if_neg h, okb, checkArith_uint, tmod_natCast]
      have := Nat.mod_le a b
      generalize a % b = q at this ⊢
      rw [if_pos (by omega)]

/-- The operators agree at `int`: `tail_sim`'s signed half. -/
private theorem stail_sim {op : BinOp} (hop : binInFrag op .int = true) (hand : op ≠ .and)
    (hor : op ≠ .or) {va vb : Value} {wa wb : Word} (ha : ReprW .int va wa) (hb : ReprW .int vb wb)
    (m : Machine) :
    ValOutW (op.ret .int) (applyBinOp op va vb >>= checkArith (op.retTy (.prim .int)))
      (run (sTail op) { m with stack := wb :: wa :: m.stack }) m := by
  obtain ⟨a, ha', rfl, rfl⟩ := ha.int_inv
  obtain ⟨b, hb', rfl, rfl⟩ := hb.int_inv
  have ra := sgn_range ha'
  have rb := sgn_range hb'
  have ret : ∀ op : BinOp, op.isArith = true → op.retTy (.prim .int) = .prim .int :=
    fun op h => by simp [BinOp.retTy, h]
  have okb : ∀ (x : Value) (f : Value → Res Value), (Except.ok x >>= f) = f x := fun _ _ => rfl
  have arith : ∀ n : Int, ValOutW .int (checkArith (.prim .int) (.int n))
      (if -(H : Int) ≤ n ∧ n < H then .ok { m with stack := .val (toWord n) :: m.stack } 0
        else .revert) m := fun n => by
    rw [checkArith_int]
    by_cases h : -(H : Int) ≤ n ∧ n < H
    · rw [if_pos h, if_pos h]; exact .inl ⟨_, _, rfl, ReprW.int h.1 h.2, rfl⟩
    · rw [if_neg h, if_neg h]; exact .inr ⟨rfl, rfl⟩
  have hb0 : (sgn b = 0) ↔ b = 0 := sgn_eq_zero hb'
  cases op <;> simp [binInFrag] at hop hand hor
  · rw [sadd_tail m m.stack ha' hb', ret .add rfl]; exact arith _
  · rw [ssub_tail m m.stack ha' hb', ret .sub rfl]; exact arith _
  · rw [smul_tail m m.stack ha' hb', ret .mul rfl]; exact arith _
  · -- `/`
    rw [sdiv_tail, ret .div rfl, show applyBinOp .div (.int (sgn a)) (.int (sgn b)) =
      (if sgn b = 0 then .error .revert else .ok (.int (Int.tdiv (sgn a) (sgn b)))) from rfl]
    by_cases h0 : b = 0
    · rw [if_pos h0, if_pos (hb0.2 h0)]; exact .inr ⟨rfl, rfl⟩
    · rw [if_neg h0, if_neg (fun h => h0 (hb0.1 h)), okb]
      have hr := tdiv_range ra (y := sgn b) (fun h => h0 (hb0.1 h))
      have e1 : a = H ↔ sgn a = -(H : Int) := by
        have := W_eq; unfold sgn; constructor <;> intro h <;> split at * <;> omega
      have e2 : b = W - 1 ↔ sgn b = -1 := by
        have := W_eq; have := H_pos; unfold sgn; constructor <;> intro h <;> split at * <;> omega
      by_cases hs : a = H ∧ b = W - 1
      · rw [if_pos hs, checkArith_int, if_neg (fun h => (hr.1 h) ⟨e1.1 hs.1, e2.1 hs.2⟩)]
        exact .inr ⟨rfl, rfl⟩
      · rw [if_neg hs, checkArith_int,
          if_pos (hr.2 fun h => hs ⟨e1.2 h.1, e2.2 h.2⟩)]
        exact .inl ⟨_, _, rfl, ReprW.int (hr.2 fun h => hs ⟨e1.2 h.1, e2.2 h.2⟩).1
          (hr.2 fun h => hs ⟨e1.2 h.1, e2.2 h.2⟩).2, rfl⟩
  · -- `%`
    rw [smod_tail, ret .mod rfl, show applyBinOp .mod (.int (sgn a)) (.int (sgn b)) =
      (if sgn b = 0 then .error .revert else .ok (.int (Int.tmod (sgn a) (sgn b)))) from rfl]
    by_cases h0 : b = 0
    · rw [if_pos h0, if_pos (hb0.2 h0)]; exact .inr ⟨rfl, rfl⟩
    · have hr := tmod_range (x := sgn a) rb (fun h => h0 (hb0.1 h))
      rw [if_neg h0, if_neg (fun h => h0 (hb0.1 h)), okb, checkArith_int, if_pos hr]
      exact .inl ⟨_, _, rfl, ReprW.int hr.1 hr.2, rfl⟩
  · refine .inl ⟨.bool (decide (sgn a < sgn b)), _, ?_, ReprW.bool _, (scmp_tail m m.stack a b).1⟩
    simp [applyBinOp, checkArith, Value.asInt, bind, Except.bind]
  · refine .inl ⟨.bool (decide (sgn b < sgn a)), _, ?_, ReprW.bool _, (scmp_tail m m.stack a b).2.1⟩
    simp [applyBinOp, checkArith, Value.asInt, bind, Except.bind]
  · refine .inl ⟨.bool (decide (sgn a ≤ sgn b)), _, ?_, ReprW.bool _,
      (scmp_tail m m.stack a b).2.2.1⟩
    simp [applyBinOp, checkArith, Value.asInt, bind, Except.bind]
  · refine .inl ⟨.bool (decide (sgn b ≤ sgn a)), _, ?_, ReprW.bool _,
      (scmp_tail m m.stack a b).2.2.2.1⟩
    simp [applyBinOp, checkArith, Value.asInt, bind, Except.bind]
  · refine .inl ⟨.bool (decide (a = b)), _, ?_, ReprW.bool _, (scmp_tail m m.stack a b).2.2.2.2.1⟩
    have : (sgn a = sgn b) ↔ a = b := ⟨sgn_inj ha' hb', fun h => h ▸ rfl⟩
    simp [applyBinOp, checkArith, bind, Except.bind, this]
  · refine .inl ⟨.bool (!decide (a = b)), _, ?_, ReprW.bool _,
      (scmp_tail m m.stack a b).2.2.2.2.2⟩
    have : (sgn a = sgn b) ↔ a = b := ⟨sgn_inj ha' hb', fun h => h ▸ rfl⟩
    simp [applyBinOp, checkArith, bind, Except.bind, this]

/-- An operator whose tail is its opcode, with no guard: the interpreter's
result is a word, which the opcode pushes.  Example: `a & b`, `a +% b`. -/
private theorem word_tail {op : BinOp} (hop : op.isArith = true) {a b r : Nat} (hr : r < W)
    (hsrc : applyBinOp op (.int a) (.int b) = .ok (.int (r : Int))) {m : Machine}
    (hrun : run (uTail op) { m with stack := .val b :: .val a :: m.stack } = .ok (m.push (.val r)) 0) :
    ValOutW (op.ret .uint) (applyBinOp op (.int a) (.int b) >>= checkArith (op.retTy (.prim .uint)))
      (run (uTail op) { m with stack := .val b :: .val a :: m.stack }) m := by
  have e1 : op.ret .uint = .uint := by simp [BinOp.ret, hop]
  have e2 : op.retTy (.prim .uint) = .prim .uint := by simp [BinOp.retTy, hop]
  rw [e1, e2, hsrc, hrun, Res.ok_bind, checkArith_uint, if_pos (by omega)]
  exact .inl ⟨_, _, rfl, ReprW.uint hr, rfl⟩

/-- `x - y` modulo `2^256` is `x + (2^256 - y)` modulo `2^256`: `SUB`. -/
private theorem subW_eq {a b : Nat} (hb : b < W) :
    ((a + (W - b)) % W : Nat) = ((a : Int) - b) % (W : Int) := by
  rw [Int.natCast_emod, show ((a + (W - b) : Nat) : Int) = ((a : Int) - b) + W by omega,
    Int.add_emod_right]

/-- **The operators agree.**  On words representing its operands, an
operator's tail computes the word of the interpreter's checked result, or
reverts exactly when the interpreter does.

Example: `a + b` with `a = 2^256 - 1`, `b = 1`: `checkArith` reverts (the sum
is not a `uint256`), and so does `add_tail`'s guard. -/
private theorem tail_sim {op : BinOp} {p : PrimTy} (hop : binInFrag op p = true) (hand : op ≠ .and)
    (hor : op ≠ .or) {va vb : Value} {wa wb : Word} (ha : ReprW p va wa) (hb : ReprW p vb wb)
    (m : Machine) :
    ValOutW (op.ret p) (applyBinOp op va vb >>= checkArith (op.retTy (.prim p)))
      (run (binTail p op) { m with stack := wb :: wa :: m.stack }) m := by
  cases p with
  | int => exact stail_sim hop hand hor ha hb m
  | bool =>
    show ValOutW _ _ (run (uTail op) _) m
    obtain ⟨a, rfl, rfl⟩ := ha.bool_inv
    obtain ⟨b, rfl, rfl⟩ := hb.bool_inv
    have cmp := cmp_tail m m.stack (bword a) (bword b)
    cases op <;> simp [binInFrag] at hop hand hor
    · have e : decide (bword a = bword b) = decide (a = b) := by cases a <;> cases b <;> rfl
      refine .inl ⟨_, _, by simp [applyBinOp]; rfl,
        ReprW.bool (decide (a = b)), ?_⟩
      rw [cmp.2.2.2.2.1, e]; rfl
    · have e : decide (bword a = bword b) = decide (a = b) := by cases a <;> cases b <;> rfl
      refine .inl ⟨_, _, by simp [applyBinOp]; rfl,
        ReprW.bool (!decide (a = b)), ?_⟩
      rw [cmp.2.2.2.2.2, e]; rfl
  | uint =>
    show ValOutW _ _ (run (uTail op) _) m
    obtain ⟨a, ha', rfl, rfl⟩ := ha.uint_inv
    obtain ⟨b, hb', rfl, rfl⟩ := hb.uint_inv
    clear ha hb
    cases op <;> simp [binInFrag] at hop hand hor
    · -- `+`
      rw [add_tail m m.stack ha' hb', (src_arith ha').1]
      by_cases h : a + b < W
      · exact .inl ⟨.int ↑(a + b), .val (a + b), by simp [h], ReprW.uint h, by simp [h]; rfl⟩
      · exact .inr ⟨by simp [h], by simp [h]⟩
    · -- `-`
      rw [sub_tail m m.stack ha' hb', (src_arith ha').2.1]
      by_cases h : b ≤ a
      · exact .inl ⟨.int ↑(a - b), .val (a - b), by simp [h], ReprW.uint (by omega),
          by simp [h]; rfl⟩
      · exact .inr ⟨by simp [h], by simp [h]⟩
    · -- `*`
      rw [mul_tail m m.stack ha', (src_arith ha').2.2.1]
      by_cases h : a * b < W
      · exact .inl ⟨.int ↑(a * b), .val (a * b), by simp [h], ReprW.uint h, by simp [h]; rfl⟩
      · exact .inr ⟨by simp [h], by simp [h]⟩
    · -- `**`
      rw [exp_tail m m.stack ha' hb']
      have hsrc : (applyBinOp .pow (.int ↑a) (.int ↑b) >>= checkArith (BinOp.pow.retTy (.prim .uint))) =
          if a ^ b < W then .ok (.int ↑(a ^ b)) else .error .revert := by
        have e1 : applyBinOp .pow (.int ↑a) (.int ↑b) = .ok (.int ↑(a ^ b)) := by
          simp [applyBinOp, Value.asInt, bind, Except.bind, Int.natCast_pow]
        have e2 : BinOp.pow.retTy (.prim .uint) = .prim .uint := rfl
        rw [e1, e2, Res.ok_bind, checkArith_uint]
        by_cases h : a ^ b < W
        · rw [if_pos (by omega), if_pos h]
        · rw [if_neg (by omega), if_neg h]
      rw [hsrc]
      by_cases h : a ^ b < W
      · exact .inl ⟨.int ↑(a ^ b), .val (a ^ b), by simp [h], ReprW.uint h, by simp [h]; rfl⟩
      · exact .inr ⟨by simp [h], by simp [h]⟩
    · -- `/`
      rw [div_tail, (src_arith ha').2.2.2.1]
      by_cases h : b = 0
      · exact .inr ⟨by simp [h], by simp [h]⟩
      · exact .inl ⟨.int ↑(a / b), .val (a / b), by simp [h],
          ReprW.uint (Nat.lt_of_le_of_lt (Nat.div_le_self a b) ha'), by simp [h]; rfl⟩
    · -- `%`
      rw [mod_tail, (src_arith ha').2.2.2.2]
      by_cases h : b = 0
      · exact .inr ⟨by simp [h], by simp [h]⟩
      · exact .inl ⟨.int ↑(a % b), .val (a % b), by simp [h],
          ReprW.uint (Nat.lt_of_le_of_lt (Nat.mod_le a b) ha'), by simp [h]; rfl⟩
    · -- `<`
      refine .inl ⟨.bool (decide (a < b)), _, ?_, ReprW.bool _, (cmp_tail m m.stack a b).1⟩
      simp [applyBinOp, checkArith, Value.asInt, bind, Except.bind]
    · -- `>`
      refine .inl ⟨.bool (decide (b < a)), _, ?_, ReprW.bool _, (cmp_tail m m.stack a b).2.1⟩
      simp [applyBinOp, checkArith, Value.asInt, bind, Except.bind]
    · -- `<=`
      refine .inl ⟨.bool (decide (a ≤ b)), _, ?_, ReprW.bool _, (cmp_tail m m.stack a b).2.2.1⟩
      simp [applyBinOp, checkArith, Value.asInt, bind, Except.bind]
    · -- `>=`
      refine .inl ⟨.bool (decide (b ≤ a)), _, ?_, ReprW.bool _, (cmp_tail m m.stack a b).2.2.2.1⟩
      simp [applyBinOp, checkArith, Value.asInt, bind, Except.bind]
    · -- `==`
      refine .inl ⟨.bool (decide (a = b)), _, ?_, ReprW.bool _, (cmp_tail m m.stack a b).2.2.2.2.1⟩
      simp [applyBinOp, checkArith, bind, Except.bind, Int.natCast_inj]
    · -- `!=`
      refine .inl ⟨.bool (!decide (a = b)), _, ?_, ReprW.bool _, (cmp_tail m m.stack a b).2.2.2.2.2⟩
      simp [applyBinOp, checkArith, bind, Except.bind, Int.natCast_inj]
    · -- `&`
      refine word_tail rfl (Nat.and_lt_two_pow b ha') ?_ (by simp [run, uTail, Instr.step, Machine.next]; rfl)
      simp [applyBinOp, Value.asInt, bind, Except.bind, uintBitwise_natCast, Nat.and_comm]
    · -- `|`
      refine word_tail rfl (Nat.or_lt_two_pow hb' ha') ?_ (by simp [run, uTail, Instr.step, Machine.next]; rfl)
      simp [applyBinOp, Value.asInt, bind, Except.bind, uintBitwise_natCast, Nat.or_comm]
    · -- `^`
      refine word_tail rfl (Nat.xor_lt_two_pow hb' ha') ?_ (by simp [run, uTail, Instr.step, Machine.next]; rfl)
      simp [applyBinOp, Value.asInt, bind, Except.bind, uintBitwise_natCast, Nat.xor_comm]
    · -- `<<`
      refine word_tail (op := .shl) rfl (r := if b < 256 then a * 2 ^ b % W else 0)
        (by split <;> first | exact Nat.mod_lt _ W_pos | exact W_pos) ?_
        (by simp [run, uTail, Instr.step, Machine.next]; rfl)
      simp only [applyBinOp, Value.asInt, bind, Except.bind]
      by_cases h : b < 256
      · rw [if_pos (by omega), if_pos h, uintBound_eq, Int.toNat_natCast]
        simp [Int.natCast_emod, Int.natCast_mul, Int.natCast_pow]
      · rw [if_neg (by omega), if_neg h]; rfl
    · -- `>>`
      refine word_tail (op := .shr) rfl (r := if b < 256 then a / 2 ^ b else 0)
        (by split <;> first | exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha' | exact W_pos) ?_
        (by simp [run, uTail, Instr.step, Machine.next]; rfl)
      simp only [applyBinOp, Value.asInt, bind, Except.bind]
      by_cases h : b < 256
      · rw [if_pos (by omega), if_pos h, Int.toNat_natCast]
        simp [Int.natCast_ediv, Int.natCast_pow]
      · rw [if_neg (by omega), if_neg h]; rfl
    · -- `+%`
      refine word_tail rfl (Nat.mod_lt (b + a) W_pos) ?_
        (by simp [run, uTail, Instr.step, Machine.next]; rfl)
      simp [applyBinOp, Value.asInt, bind, Except.bind, uintBound_eq, Int.natCast_emod, Nat.add_comm]
    · -- `-%`
      refine word_tail rfl (Nat.mod_lt (a + (W - b)) W_pos) ?_
        (by simp [run, uTail, Instr.step, Machine.next]; rfl)
      simp [applyBinOp, Value.asInt, bind, Except.bind, uintBound_eq, subW_eq hb']
    · -- `*%`
      refine word_tail rfl (Nat.mod_lt (b * a) W_pos) ?_
        (by simp [run, uTail, Instr.step, Machine.next]; rfl)
      simp [applyBinOp, Value.asInt, bind, Except.bind, uintBound_eq, Int.natCast_emod, Nat.mul_comm]
    · -- `**%`
      refine word_tail rfl (Nat.mod_lt (a ^ b) W_pos) ?_
        (by simp [run, uTail, Instr.step, Machine.next]; rfl)
      simp [applyBinOp, Value.asInt, bind, Except.bind, uintBound_eq, Int.natCast_emod,
        Int.natCast_pow]

/-- An operator other than `&&`/`||` evaluates both operands: `a + b` evaluates `b` even when `a =
0`. -/
private theorem evalBinop_eq {op : BinOp} (hand : op ≠ .and) (hor : op ≠ .or) (p : PrimTy) (lv : Value)
    (b : Res Value) :
    evalBinop op p lv b =
      (b >>= fun rv => applyBinOp op lv rv >>= checkArith (op.retTy (.prim p))) := by
  cases op <;> simp at hand hor <;> cases lv <;> rfl

/-- The operators with an `op=` form are compiled with their checks, at `uint`
and at `int`. -/
theorem compound_frag {op : BinOp} {p : PrimTy} (h : op.hasCompoundAssign = true)
    (hp : p ≠ .bool) :
    binInFrag op p = true ∧ op ≠ .and ∧ op ≠ .or ∧ op.ret p = p ∧
      op.retTy (.prim p) = .prim p := by
  cases op <;> cases p <;>
    simp_all [BinOp.hasCompoundAssign, binInFrag, BinOp.ret, BinOp.retTy, BinOp.isArith]

attribute [local simp] Res.ok_bind Res.error_bind

/-- A numeric value is an integer: `total` and an `int` local both read as `.int`. -/
private theorem ReprW.num_inv {p : PrimTy} {v : Value} {w : Word} (hp : p ≠ .bool) (h : ReprW p v w) :
    ∃ n, v = .int n := by
  cases p with
  | uint => obtain ⟨a, _, rfl, _⟩ := h.uint_inv; exact ⟨_, rfl⟩
  | int => obtain ⟨a, _, rfl, _⟩ := h.int_inv; exact ⟨_, rfl⟩
  | bool => exact absurd rfl hp

/-- `x++` and `x--` are `x += 1` and `x -= 1`, checked the same way. -/
private theorem bump_src (op : IncDec) (p : PrimTy) (a : Int) :
    checkArith (.prim p) (.int (if op.isIncrement then a + 1 else a - 1)) =
      (applyBinOp op.binOp (.int a) (.int 1) >>= checkArith (op.binOp.retTy (.prim p))) := by
  cases op <;> rfl

/-- `++` and `--` are the `+=`/`-=` of the fragment: `x++;` is checked as `x += 1;`. -/
theorem bump_frag (op : IncDec) : op.binOp.hasCompoundAssign = true := by
  cases op <;> rfl

/-- The step of `++`: its old value an integer, its checked result computed by
`PUSH 1` and the operator's tail, or both revert. -/
private theorem bump_sim {p : PrimTy} (hp : p ≠ .bool) (op : IncDec) {old : Value} {w : Word}
    (h : ReprW p old w) (m : Machine) :
    ∃ n, old = .int n ∧ ValOutW p (checkArith (.prim p) (.int (if op.isIncrement then n + 1 else n - 1)))
      (run ([.push (.val 1)] ++ binTail p op.binOp) { m with stack := w :: m.stack }) m := by
  obtain ⟨hfrag, hand, hor, hret, hretTy⟩ := compound_frag (bump_frag op) hp
  obtain ⟨n, rfl⟩ := h.num_inv hp
  refine ⟨n, rfl, ?_⟩
  rw [bump_src, run_append_ok (m' := { m with stack := .val 1 :: w :: m.stack }) rfl]
  have ht := tail_sim hfrag hand hor h (ReprW.one hp) m
  rwa [hret] at ht

private theorem erase_numeric {p : PrimTy} (hp : p.isNumeric = true) (x : p.Denote) :
    PrimTy.erase x = .int (PrimTy.key x) := by
  cases p <;> first | rfl | cases hp

/-- `a ⊕= b`'s operator, checked: `compoundT` erased. -/
private theorem compound_erase {op : BinOp} (hop : op.hasCompoundAssign = true) {p : PrimTy}
    (hp : p.isNumeric = true) (x y : p.Denote) :
    (applyBinOp op (PrimTy.erase x) (PrimTy.erase y) >>= checkArith (.prim p)) =
      Solidity.toRes PrimTy.erase
        (Solidity.compoundT op p (PrimTy.key x) (PrimTy.key y)) := by
  have hA : op.isArith = true := by
    cases op <;> simp only [BinOp.hasCompoundAssign, Bool.false_eq_true] at hop <;> rfl
  rw [erase_numeric hp x, erase_numeric hp y, BinOp.applyBinOp_int hA]
  unfold Solidity.compoundT
  cases BinOp.arithInt op (PrimTy.key x) (PrimTy.key y) with
  | none => rfl
  | some n => exact PrimTy.checkArith_ofInt hp n

/-- `x++`'s new value, checked: `bumpT` erased. -/
private theorem bump_erase {p : PrimTy} (hp : p.isNumeric = true) (op : IncDec) (x : Int) :
    checkArith (.prim p) (.int (if op.isIncrement then x + 1 else x - 1)) =
      Solidity.toRes PrimTy.erase (Solidity.bumpT op p x) :=
  PrimTy.checkArith_ofInt hp _

/-! ## Typed values -/

/-- A word represents a typed value as it represents the value erased. -/
private theorem reprV_iff {p : PrimTy} {v : p.Denote} {w : Word} :
    ReprV p v w ↔ ReprW p (PrimTy.erase v) w := by
  cases p with
  | uint =>
    obtain ⟨n, hn⟩ := v
    simp only [PrimTy.inRange, decide_eq_true_eq] at hn
    cases w with
    | val a =>
      show (Word.val a = .val n.toNat) ↔ (0 ≤ n ∧ n < W ∧ a = n.toNat)
      unfold W
      constructor
      · intro h; cases h; omega
      · intro h; rw [h.2.2]
    | slot s => exact ⟨fun h => (by cases h), fun h => h.elim⟩
  | bool =>
    cases w with
    | val a =>
      exact ⟨fun h => (by cases h; rfl), fun h => show Word.val a = .val (bword v) by
        rw [show a = bword v from h]⟩
    | slot s => exact ⟨fun h => (by cases h), fun h => h.elim⟩
  | int =>
    cases w with
    | val a =>
      exact ⟨fun ⟨b, hb, h1, h2⟩ => by cases hb; exact ⟨h1, h2⟩,
        fun ⟨h1, h2⟩ => ⟨a, rfl, h1, h2⟩⟩
    | slot s => exact ⟨fun ⟨b, hb, _⟩ => (by cases hb), fun h => h.elim⟩

/-- A typed operator's outcome read off its untyped one. -/
private theorem ValOutT.ofW {p : PrimTy} {o : Option p.Denote} {out : Out} {m : Machine}
    (h : ValOutW p (Solidity.toRes PrimTy.erase o) out m) : ValOutT p (TRes.ofOpt o) out m := by
  cases o with
  | none =>
    rcases h with ⟨_, _, h, _⟩ | ⟨_, h⟩
    · cases h
    · exact .inr ⟨rfl, h⟩
  | some v =>
    rcases h with ⟨v', w, h, hr, hout⟩ | ⟨h, _⟩
    · cases h; exact .inl ⟨v, w, rfl, reprV_iff.2 hr, hout⟩
    · cases h

/-- An `int` is represented by its two's complement word: `-1` is `2^256 - 1`. -/
theorem ReprV.int_word (v : PrimTy.int.Denote) : ReprV .int v (.val (toWord v.1)) := by
  obtain ⟨n, hn⟩ := v
  simp only [PrimTy.inRange, decide_eq_true_eq] at hn
  exact reprV_iff.2 (ReprW.int hn.1 hn.2)

/-- **The operators agree**, typed: on words representing its operands, an
operator's tail computes the word of the typed result, or reverts exactly
when the typed operator does. -/
theorem tail_simT {op : BinOp} {p : PrimTy} (hop : binInFrag op p = true) (hand : op ≠ .and)
    (hor : op ≠ .or) (hacc : op.accepts p = true) {a b : p.Denote} {wa wb : Word}
    (ha : ReprV p a wa) (hb : ReprV p b wb) (m : Machine) :
    ValOutT (op.ret p) (TRes.ofOpt (op.evalT a b))
      (run (binTail p op) { m with stack := wb :: wa :: m.stack }) m := by
  apply ValOutT.ofW
  rw [← BinOp.evalT_erase op hacc, evalBinop_eq hand hor]
  exact tail_sim hop hand hor (reprV_iff.1 ha) (reprV_iff.1 hb) m

/-- `-x` at `int`: the negation, or a revert at `-2^255`. -/
theorem neg_simT {a : PrimTy.int.Denote} {wa : Word} (ha : ReprV .int a wa) (m : Machine) :
    ValOutT .int (TRes.ofOpt (UnOp.neg.evalT a)) (run negCode (m.push wa)) m := by
  obtain ⟨x, rfl, hx, hax⟩ := ha
  apply ValOutT.ofW
  rw [← UnOp.evalT_erase .neg rfl a]
  simp only [Machine.push]
  rw [neg_run m m.stack hx]
  change ValOutW _ (checkArith (.prim .int) (.int (-a.1))) _ _
  rw [hax, checkArith_int]
  by_cases h : -(H : Int) ≤ -sgn x ∧ -sgn x < H
  · rw [if_pos h, if_pos h]; exact .inl ⟨_, _, rfl, ReprW.int h.1 h.2, rfl⟩
  · rw [if_neg h, if_neg h]; exact .inr ⟨rfl, rfl⟩

/-- `~x` at `uint`: `NOT`. -/
theorem bnot_simT {a : PrimTy.uint.Denote} {wa : Word} (ha : ReprV .uint a wa) (m : Machine) :
    ValOutT .uint (TRes.ofOpt (UnOp.bnot.evalT a)) (run [.not] (m.push wa)) m := by
  apply ValOutT.ofW
  rw [← UnOp.evalT_erase .bnot rfl a]
  obtain ⟨x, hx, hza, rfl⟩ := (reprV_iff.1 ha).uint_inv
  rw [hza]
  have := W_pos
  refine .inl ⟨.int ↑(W - 1 - x), .val (W - 1 - x), ?_, ReprW.uint (by omega), ?_⟩
  · simp only [applyUnOp, Value.asInt, unopCheck, bind, Except.bind, pure, Except.pure,
      uintBound_eq]
    congr 2; omega
  · simp only [run, Machine.push, exec_cons_zero, Instr.step, Machine.next, exec_nil]; rfl

/-- `a ⊕= b`'s operator and its checks, typed. -/
theorem compound_simT {op : BinOp} (hop : op.hasCompoundAssign = true) {p : PrimTy}
    (hp : p.isNumeric = true) {a b : p.Denote} {wa wb : Word} (ha : ReprV p a wa)
    (hb : ReprV p b wb) (m : Machine) :
    ValOutT p (TRes.ofOpt (Solidity.compoundT op p (PrimTy.key a) (PrimTy.key b)))
      (run (binTail p op) { m with stack := wb :: wa :: m.stack }) m := by
  have hp' : p ≠ .bool := by rintro rfl; exact Bool.noConfusion hp
  obtain ⟨hfrag, hand, hor, hret, hretTy⟩ := compound_frag hop hp'
  have ht := tail_sim hfrag hand hor (reprV_iff.1 ha) (reprV_iff.1 hb) m
  rw [hret, hretTy, compound_erase hop hp] at ht
  exact ValOutT.ofW ht

/-- The step of `++`, typed: `PUSH 1` and the operator's tail. -/
theorem bump_simT {p : PrimTy} (hp : p.isNumeric = true) (op : IncDec) {a : p.Denote} {w : Word}
    (h : ReprV p a w) (m : Machine) :
    ValOutT p (TRes.ofOpt (Solidity.bumpT op p (PrimTy.key a)))
      (run ([.push (.val 1)] ++ binTail p op.binOp) { m with stack := w :: m.stack }) m := by
  have hp' : p ≠ .bool := by rintro rfl; exact Bool.noConfusion hp
  obtain ⟨n, hn, hv⟩ := bump_sim hp' op (reprV_iff.1 h) m
  rw [erase_numeric hp] at hn
  cases hn
  rw [bump_erase hp] at hv
  exact ValOutT.ofW hv

end Words

/-! ## Locations -/

/-- With `… s i` on the stack, the bounds check passes when `i` is below the
word at `s` and reverts otherwise: `values[3]` with three values reverts. -/
theorem boundsCheck_run (m : Machine) (st : List Word) (rest : List Instr) (i : Nat) (s : Slot) :
    run (boundsCheck ++ rest) { m with stack := .val i :: .slot s :: st } =
      if i < m.store s then run rest { m with stack := .val i :: .slot s :: st } else .revert := by
  by_cases h : i < m.store s
  · simp [run, boundsCheck, assertTop, Instr.step, Machine.next, h, bword]
  · simp [run, boundsCheck, assertTop, Instr.step, Machine.next, h, bword]

/-- `z` additions of `i` to a slot add `z·i`: element `i` of `Person[]` is `3·i` past
`keccak(9)`. -/
theorem addRep_run (m : Machine) (st : List Word) (i : Nat) :
    ∀ (z : Nat) (t : Slot), run (addRep z) { m with stack := .slot t :: .val i :: st } =
      .ok { m with stack := .slot (t.add (z * i)) :: .val i :: st } 0
  | 0, t => by simp [addRep]
  | z + 1, t => by
    rw [addRep, run_append_ok (m' := { m with stack := .slot (t.add i) :: .val i :: st })
      (by simp [run, Instr.step, Machine.next]), addRep_run m st i z (t.add i),
      Slot.add_add, Nat.succ_mul, Nat.add_comm (z * i)]

/-- Element `i` of the array at `s`, whose elements take `z` slots, is at
`keccak(s) + i·z`: `persons[1].age` is `keccak(9) + 3 + 2`. -/
theorem elemSlot_run (m : Machine) (st : List Word) (i z : Nat) (s : Slot) :
    run (elemSlot z) { m with stack := .val i :: .slot s :: st } =
      .ok { m with stack := .slot (.data s (i * z)) :: st } 0 := by
  rw [elemSlot, List.append_assoc,
    run_append_ok (m' := { m with stack := .slot (.data s 0) :: .val i :: st })
    (by simp [run, Instr.step, Machine.next]), run_append_ok (addRep_run m st i z _)]
  simp [run, Instr.step, Machine.next, Slot.add, Nat.mul_comm]

/-- A fixed-size array's bound is its type's, a constant: `fixedValues[k]`
checks `k < 3` and reads no length slot. -/
theorem fixedCheck_run (m : Machine) (st : List Word) (rest : List Instr) (n i : Nat) (s : Slot) :
    run (fixedCheck n ++ rest) { m with stack := .val i :: .slot s :: st } =
      if i < n then run rest { m with stack := .val i :: .slot s :: st } else .revert := by
  by_cases h : i < n
  · simp [run, fixedCheck, assertTop, Instr.step, Machine.next, h, bword]
  · simp [run, fixedCheck, assertTop, Instr.step, Machine.next, h, bword]

/-- Element `i` of the fixed-size array laid out from `s`, whose elements take
`z` slots, is at `s + i·z`: `fixedTokens[1].value` is `fixedTokens`'s slot plus `1`. -/
theorem fixedSlot_run (m : Machine) (st : List Word) (i z : Nat) (s : Slot) :
    run (fixedSlot z) { m with stack := .val i :: .slot s :: st } =
      .ok { m with stack := .slot (s.add (i * z)) :: st } 0 := by
  rw [fixedSlot, List.append_assoc,
    run_append_ok (m' := { m with stack := .slot s :: .val i :: st })
    (by simp [run, Instr.step, Machine.next]), run_append_ok (addRep_run m st i z _)]
  simp [run, Instr.step, Machine.next, Nat.mul_comm]


/-! ## The simulation relation -/

/-- The machine's environment is the transaction's: `CALLER` pushes
`msg.sender`, `ADDRESS` the contract's address, `address(this)`, and each of
them is a word. -/
def EnvSim (t : TTx) (m : Machine) : Prop :=
  t.msgSender.1 = m.caller ∧ t.msgValue.1 = m.callvalue ∧ t.timestamp.1 = m.timestamp ∧
    t.selfAddress.1 = m.self ∧
    m.caller < W ∧ m.callvalue < W ∧ m.timestamp < W ∧ m.self < W

/-- `net(a)`: the ledger's entry at `a`, `0` where nothing was booked. -/
def netAt (net : List (Int × Int)) (a : Int) : Int := (Semantics.lookupBy a net).getD 0

/-- The ledger after a payment of `y` to `x`: as it was when `x` is the
contract itself, else `x`'s entry down by `y`. -/
theorem netAt_pay {C : Contract} {Γ : Ctx} (τ : State C Γ) (x y a : Int) :
    netAt (τ.pay x y).net a =
      if x = τ.tx.selfAddress.1 then netAt τ.net a
      else if a = x then netAt τ.net x - y else netAt τ.net a := by
  by_cases h1 : x = τ.tx.selfAddress.1
  · simp only [State.pay, netAt, h1, ↓reduceIte]
  · simp only [State.pay, netAt, h1, ↓reduceIte]
    by_cases h2 : a = x
    · subst h2; simp only [SemanticsProperties.lookupBy_setBy_self, ↓reduceIte, Option.getD_some]
    · simp only [SemanticsProperties.lookupBy_setBy_ne h2, h2, ↓reduceIte]

variable {C : Contract} {L : Nat}

/-- A primitive storage value is read as the word at its slot: `alice.age`
pushes slot `13`'s word, an `int` its two's complement. -/
theorem prim_read {st : Slot → Nat} {p : PrimTy} {s : Slot} {sv : SVal (.prim p)}
    (h : ReprAt st L (.prim p) s sv) : ∃ v, sv = .prim v ∧ ReprV p v (.val (st s)) := by
  cases h with
  | prim h => exact ⟨_, rfl, h⟩

/-! ## Statements -/

/-- A write to a primitive leaves every array's length. -/
theorem upd_len {st : Slot → Nat} {a : Bool} {p : PrimTy} {r : SRef C (.prim p)} {s : Slot}
    (hp : PathSlot C a r s) (v : Nat) :
    ∀ x, LenSlot C x → st x ≤ upd st s v x := fun x hx => by
  rw [upd_other _ _ fun he => len_prim_disjoint hx (by rw [he]; exact hp.primSlot)]
  exact Nat.le_refl _

/-- `delete`'s writes: `0` at each leaf, the slot kept on the stack; `delete alice;` writes `11`,
`12`, `13`. -/
theorem zeroCode_run (m : Machine) (st : List Word) (s : Slot) : ∀ (os : List Nat),
    run (zeroCode os) { m with stack := .slot s :: st } =
      .ok { m with stack := .slot s :: st, store := zeroAt m.store s os } 0
  | [] => rfl
  | o :: os => by
    rw [zeroCode, List.flatMap_cons, ← zeroCode,
      run_append_ok (m' := { m with stack := .slot s :: st, store := upd m.store (s.add o) 0 })
        (by simp [run, Instr.step, Machine.next])]
    exact zeroCode_run { m with store := upd m.store (s.add o) 0 } st s os

/-- `pop` on the array at `s`: revert on an empty array, else the length
decremented. -/
theorem popCode_run (m : Machine) (st : List Word) (s : Slot) (hW : m.store s < W) :
    run popCode { m with stack := .slot s :: st } =
      if m.store s = 0 then .revert
      else .ok { m with stack := st, store := upd m.store s (m.store s - 1) } 0 := by
  by_cases h : m.store s = 0
  · simp [run, popCode, assertTop, Instr.step, Machine.next, h]
  · have e : (m.store s + (W - 1)) % W = m.store s - 1 := by
      rw [show m.store s + (W - 1) = (m.store s - 1) + W by omega, Nat.add_mod_right,
        mod_W_of_lt (by omega)]
    simp [run, popCode, assertTop, Instr.step, Machine.next, h]
    rw [e]

/-- A value written to a slot is represented there: a `uint` or a `bool` as
itself, an `int` as its word. -/
theorem repr_write {p : PrimTy} {v : p.Denote} {w : Word}
    (hv : ReprV p v w) (st : Slot → Nat) (s : Slot) :
    ∃ a, w = .val a ∧ ReprAt (upd st s a) L (.prim p) s (.prim v) := by
  cases p with
  | uint =>
    obtain ⟨a, _, ha, rfl⟩ := hv.uint_inv
    exact ⟨a, rfl, .prim (by rw [upd_same]; exact ReprV.uint_of ha)⟩
  | bool =>
    have := hv.bool_inv
    subst this
    exact ⟨_, rfl, .prim (by rw [upd_same]; rfl)⟩
  | int =>
    obtain ⟨a, ha, hax, rfl⟩ := hv.int_inv
    exact ⟨a, rfl, .prim ⟨a, by rw [upd_same], ha, hax⟩⟩

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
    rw [show [Instr.dup 1, .push (.val 1)] ++ binTail p op.binOp =
      [Instr.dup 1] ++ ([.push (.val 1)] ++ binTail p op.binOp) from rfl,
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
def storeAt (st : Slot → Nat) (d : Slot) : List Nat → List Nat → Slot → Nat
  | o :: os, v :: vs => storeAt (upd st (d.add o) v) d os vs
  | _, _ => st

/-- Writing at some offsets leaves the other slots. -/
theorem storeAt_other {d x : Slot} : ∀ {os vs : List Nat} {st : Slot → Nat},
    (∀ o ∈ os, x ≠ d.add o) → storeAt st d os vs x = st x
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | o :: os, v :: vs, st, h => by
    simp only [storeAt]
    rw [storeAt_other fun o' ho' => h o' (List.mem_cons_of_mem _ ho')]
    exact upd_other _ _ (h o List.mem_cons_self)

/-- Writing `f o` at each `d + o` leaves `f o` there. -/
theorem storeAt_map (f : Nat → Nat) {d : Slot} {o : Nat} : ∀ {os : List Nat} {st : Slot → Nat},
    o ∈ os → storeAt st d os (os.map f) (d.add o) = f o
  | o' :: os, st, h => by
    simp only [List.map_cons, storeAt]
    by_cases ho : o ∈ os
    · exact storeAt_map f ho
    · obtain rfl : o = o' := by
        rcases List.mem_cons.1 h with h | h
        · exact h
        · exact absurd h ho
      rw [storeAt_other fun o'' ho'' he => ho (by rw [Slot.add_inj he]; exact ho''), upd_same]

/-- A write to a static value's leaves leaves every array's length. -/
theorem storeAt_len {st : Slot → Nat} {a : Bool} {R : RefTy} {r : SRef C (.ref R)}
    {d : Slot} (hp : PathSlot C a r d) (hst : static (.ref R) = true)
    (vs : List Nat) : ∀ x, LenSlot C x → st x ≤ storeAt st d (leaves (.ref R)).reverse vs x :=
  fun x hx => by
    rw [storeAt_other fun o ho he => len_prim_disjoint hx (by
      obtain ⟨T₀, h0, oc⟩ := hp.occAt (leavesF_occAt _ _ d o hst (List.mem_reverse.1 ho))
      exact ⟨r.root, T₀, h0, he ▸ oc⟩)]
    exact Nat.le_refl _

/-- A `push`'s writes: the length one more, and the new element's primitives. -/
theorem push_len {st st' : Slot → Nat} {a : Bool} {E : Ty} {r : SRef C (.ref (.array E))}
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
theorem loadLeaves_run (m : Machine) (s : Slot) : ∀ (os : List Nat) (st : List Word),
    run (loadLeaves os) { m with stack := .slot s :: st } =
      .ok { m with stack := .slot s ::
        ((os.map fun o => m.store (s.add o)).reverse.map Word.val ++ st) } 0
  | [], st => rfl
  | o :: os, st => by
    rw [loadLeaves, List.flatMap_cons, ← loadLeaves,
      run_append_ok (m' := { m with stack := .slot s :: .val (m.store (s.add o)) :: st })
        (by simp [run, Instr.step, Machine.next]),
      loadLeaves_run m s os]
    simp

/-- `storeLeaves`: each word stored at `d + o`. -/
theorem storeLeaves_run (m : Machine) (d : Slot) : ∀ (os vs : List Nat) (st : List Word)
    (mst : Slot → Nat), os.length = vs.length →
    run (storeLeaves os) { m with stack := .slot d :: (vs.map Word.val ++ st), store := mst } =
      .ok { m with stack := .slot d :: st, store := storeAt mst d os vs } 0
  | [], [], st, mst, _ => rfl
  | o :: os, v :: vs, st, mst, h => by
    rw [storeLeaves, List.flatMap_cons, ← storeLeaves,
      run_append_ok
        (m' := { m with stack := .slot d :: (vs.map Word.val ++ st), store := upd mst (d.add o) v })
        (by simp [run, Instr.step, Machine.next]),
      storeLeaves_run m d os vs st _ (by simpa using h)]
    rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h

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
        store := upd m.store s (m.store s + 1) } 0 := by
  have hW := Lmax_lt_W
  have e : (m.store s + 1) % W = m.store s + 1 := Nat.mod_eq_of_lt (by omega)
  have h1 : run ([.dup 1, .sload, .push (.val Lmax), .dup 2, .lt] ++ assertTop ++
      [.push (.val 1), .dup 2, .add, .dup 3, .sstore]) { m with stack := .slot s :: st } =
      .ok { m with
        stack := .val (m.store s) :: .slot s :: st
        store := upd m.store s (m.store s + 1) } 0 := by
    simp [run, assertTop, Instr.step, Machine.next, hl, e, bword]
  rw [pushSlotCode, run_append_ok h1]
  exact elemSlot_run { m with store := upd m.store s (m.store s + 1) } st (m.store s) z s

/-- A slot holding `0` represents a primitive type's default. -/
theorem zero_prim_repr {st : Slot → Nat} {p : PrimTy} {x : Slot}
    (h : st x = 0) : ReprAt st L (.prim p) x (SVal.dflt (.prim p)) :=
  .prim (by rw [h]; exact ReprV.dflt_zero p)

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
