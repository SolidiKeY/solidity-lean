import Solidity.Evm.Repr
import Solidity.Evm.Signed
import Solidity.Evm.Exp

/-!
# The machine lemmas of the simulation

What `Evm/Sim.lean`, `Evm/Expr.lean` and `Evm/Stmt.lean` build
the simulation from, none of it about the syntax: the guard sequences of
`Evm/Layout.lean` computed on the machine (`add_tail`/`sub_tail`/`mul_tail`
are solc's overflow checks, exact on words below `2^256`; `mul_ok_iff` is the
arithmetic fact behind the `*` check; the signed ones are `Evm/Signed.lean`'s,
`**` is `Evm/Exp.lean`'s), a value's word (`ReprV`, `ValOut`: a value pushed,
or both revert), the slot sequences (`boundsCheck_run`, `elemSlot_run`, …),
the machine's environment (`EnvSim`), and the store sequences of `delete`,
`pop`, a copy and a `push` (`zeroCode_run`, `popCode_run`, `storeLeaves_run`,
`pushSlotCode_run`).
-/

namespace Solidity
namespace Evm

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

/-! ## Values -/

/-- A `uint` is represented by itself, a word below `2^256`: `total` read as `7` pushes `7`. -/
theorem ReprV.uint_inv {v : Value} {w : Word} (h : ReprV .uint v w) :
    ∃ a : Nat, a < W ∧ v = .int a ∧ w = .val a := by
  match v, w, h with
  | .int n, .val w, ⟨h0, h1, h2⟩ =>
    exact ⟨n.toNat, by omega, by rw [Int.toNat_of_nonneg h0], h2 ▸ rfl⟩

/-- A `bool` is represented by `1` or `0`: `flags[3]` read as `true` pushes `1`. -/
theorem ReprV.bool_inv {v : Value} {w : Word} (h : ReprV .bool v w) :
    ∃ b : Bool, v = .bool b ∧ w = .val (bword b) := by
  match v, w, h with
  | .bool b, .val w, h => exact ⟨b, rfl, h ▸ rfl⟩

/-- An `int` is represented by a word, its two's complement: `-1` is `2^256 - 1`. -/
theorem ReprV.int_inv {v : Value} {w : Word} (h : ReprV .int v w) :
    ∃ a : Nat, a < W ∧ v = .int (sgn a) ∧ w = .val a := by
  match v, w, h with
  | .int n, .val w, ⟨h1, h2⟩ => exact ⟨w, h1, by rw [h2], rfl⟩

/-- An `int256` is represented by its word: `x = -1;` pushes `2^256 - 1`. -/
theorem ReprV.int {n : Int} (h1 : -(H : Int) ≤ n) (h2 : n < H) :
    ReprV .int (.int n) (.val (toWord n)) :=
  ⟨toWord_lt (by have := W_eq; omega) (by have := W_eq; omega), (sgn_toWord h1 h2).symm⟩

/-- `1`, the step of `++`, at a numeric type. -/
theorem ReprV.one {p : PrimTy} (hp : p ≠ .bool) : ReprV p (.int 1) (.val 1) := by
  have := W_pos; have := W_eq; have := H_pos
  cases p with
  | uint => exact ⟨by decide, by unfold W at *; omega, rfl⟩
  | int => exact ⟨by unfold W at *; omega, by simp [sgn]; unfold H at *; omega⟩
  | bool => exact absurd rfl hp

/-- A word below `2^256` represents itself as a `uint`: `total = 7;` pushes `7`. -/
theorem ReprV.uint {a : Nat} (h : a < W) : ReprV .uint (.int a) (.val a) :=
  ⟨Int.natCast_nonneg a, by omega, rfl⟩

/-- `true` is `1`, `false` is `0`: `require(true);` pushes `1`. -/
theorem ReprV.bool (b : Bool) : ReprV .bool (.bool b) (.val (bword b)) := rfl

/-- An expression's outcome, interpreter and machine together: a value and the
word representing it pushed, or both revert. -/
def ValOut (p : PrimTy) (res : Res Value) (out : Out) (m : Machine) : Prop :=
  (∃ v w, res = .ok v ∧ ReprV p v w ∧ out = .ok (m.push w) 0) ∨
    (res = .error .revert ∧ out = .revert)

/-- The interpreter's `uint256` bound is the machine's word bound: `2^256`. -/
theorem uintBound_eq : uintBound = (W : Int) := rfl

/-- On `uint`s the interpreter's truncating division is the machine's: `7 / 2` is `3`. -/
theorem tdiv_natCast (a b : Nat) : Int.tdiv (a : Int) (b : Int) = ((a / b : Nat) : Int) := rfl
/-- On `uint`s the interpreter's `%` is the machine's: `7 % 2` is `1`. -/
theorem tmod_natCast (a b : Nat) : Int.tmod (a : Int) (b : Int) = ((a % b : Nat) : Int) := rfl

/-- The range check at `uint`. -/
theorem checkArith_uint (n : Int) :
    checkArith (.prim .uint) (.int n) = if 0 ≤ n ∧ n < W then .ok (.int n) else .error .revert :=
  rfl

/-- The range check at `int`. -/
theorem checkArith_int (n : Int) :
    checkArith (.prim .int) (.int n) =
      if -(H : Int) ≤ n ∧ n < H then .ok (.int n) else .error .revert :=
  rfl

/-- The interpreter's checked `+`, `-`, `*`, `/`, `%` on `uint`s. -/
theorem src_arith {a b : Nat} (ha : a < W) :
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
theorem stail_sim {op : BinOp} (hop : binInFrag op .int = true) (hand : op ≠ .and)
    (hor : op ≠ .or) {va vb : Value} {wa wb : Word} (ha : ReprV .int va wa) (hb : ReprV .int vb wb)
    (m : Machine) :
    ValOut (op.ret .int) (applyBinOp op va vb >>= checkArith (op.retTy (.prim .int)))
      (run (sTail op) { m with stack := wb :: wa :: m.stack }) m := by
  obtain ⟨a, ha', rfl, rfl⟩ := ha.int_inv
  obtain ⟨b, hb', rfl, rfl⟩ := hb.int_inv
  have ra := sgn_range ha'
  have rb := sgn_range hb'
  have ret : ∀ op : BinOp, op.isArith = true → op.retTy (.prim .int) = .prim .int :=
    fun op h => by simp [BinOp.retTy, h]
  have okb : ∀ (x : Value) (f : Value → Res Value), (Except.ok x >>= f) = f x := fun _ _ => rfl
  have arith : ∀ n : Int, ValOut .int (checkArith (.prim .int) (.int n))
      (if -(H : Int) ≤ n ∧ n < H then .ok { m with stack := .val (toWord n) :: m.stack } 0
        else .revert) m := fun n => by
    rw [checkArith_int]
    by_cases h : -(H : Int) ≤ n ∧ n < H
    · rw [if_pos h, if_pos h]; exact .inl ⟨_, _, rfl, ReprV.int h.1 h.2, rfl⟩
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
        exact .inl ⟨_, _, rfl, ReprV.int (hr.2 fun h => hs ⟨e1.2 h.1, e2.2 h.2⟩).1
          (hr.2 fun h => hs ⟨e1.2 h.1, e2.2 h.2⟩).2, rfl⟩
  · -- `%`
    rw [smod_tail, ret .mod rfl, show applyBinOp .mod (.int (sgn a)) (.int (sgn b)) =
      (if sgn b = 0 then .error .revert else .ok (.int (Int.tmod (sgn a) (sgn b)))) from rfl]
    by_cases h0 : b = 0
    · rw [if_pos h0, if_pos (hb0.2 h0)]; exact .inr ⟨rfl, rfl⟩
    · have hr := tmod_range (x := sgn a) rb (fun h => h0 (hb0.1 h))
      rw [if_neg h0, if_neg (fun h => h0 (hb0.1 h)), okb, checkArith_int, if_pos hr]
      exact .inl ⟨_, _, rfl, ReprV.int hr.1 hr.2, rfl⟩
  · refine .inl ⟨.bool (decide (sgn a < sgn b)), _, ?_, ReprV.bool _, (scmp_tail m m.stack a b).1⟩
    simp [applyBinOp, checkArith, Value.asInt, bind, Except.bind]
  · refine .inl ⟨.bool (decide (sgn b < sgn a)), _, ?_, ReprV.bool _, (scmp_tail m m.stack a b).2.1⟩
    simp [applyBinOp, checkArith, Value.asInt, bind, Except.bind]
  · refine .inl ⟨.bool (decide (sgn a ≤ sgn b)), _, ?_, ReprV.bool _,
      (scmp_tail m m.stack a b).2.2.1⟩
    simp [applyBinOp, checkArith, Value.asInt, bind, Except.bind]
  · refine .inl ⟨.bool (decide (sgn b ≤ sgn a)), _, ?_, ReprV.bool _,
      (scmp_tail m m.stack a b).2.2.2.1⟩
    simp [applyBinOp, checkArith, Value.asInt, bind, Except.bind]
  · refine .inl ⟨.bool (decide (a = b)), _, ?_, ReprV.bool _, (scmp_tail m m.stack a b).2.2.2.2.1⟩
    have : (sgn a = sgn b) ↔ a = b := ⟨sgn_inj ha' hb', fun h => h ▸ rfl⟩
    simp [applyBinOp, checkArith, bind, Except.bind, this]
  · refine .inl ⟨.bool (!decide (a = b)), _, ?_, ReprV.bool _,
      (scmp_tail m m.stack a b).2.2.2.2.2⟩
    have : (sgn a = sgn b) ↔ a = b := ⟨sgn_inj ha' hb', fun h => h ▸ rfl⟩
    simp [applyBinOp, checkArith, bind, Except.bind, this]

/-- An operator whose tail is its opcode, with no guard: the interpreter's
result is a word, which the opcode pushes.  Example: `a & b`, `a +% b`. -/
theorem word_tail {op : BinOp} (hop : op.isArith = true) {a b r : Nat} (hr : r < W)
    (hsrc : applyBinOp op (.int a) (.int b) = .ok (.int (r : Int))) {m : Machine}
    (hrun : run (uTail op) { m with stack := .val b :: .val a :: m.stack } = .ok (m.push (.val r)) 0) :
    ValOut (op.ret .uint) (applyBinOp op (.int a) (.int b) >>= checkArith (op.retTy (.prim .uint)))
      (run (uTail op) { m with stack := .val b :: .val a :: m.stack }) m := by
  have e1 : op.ret .uint = .uint := by simp [BinOp.ret, hop]
  have e2 : op.retTy (.prim .uint) = .prim .uint := by simp [BinOp.retTy, hop]
  rw [e1, e2, hsrc, hrun, Res.ok_bind, checkArith_uint, if_pos (by omega)]
  exact .inl ⟨_, _, rfl, ReprV.uint hr, rfl⟩

/-- `x - y` modulo `2^256` is `x + (2^256 - y)` modulo `2^256`: `SUB`. -/
theorem subW_eq {a b : Nat} (hb : b < W) :
    ((a + (W - b)) % W : Nat) = ((a : Int) - b) % (W : Int) := by
  rw [Int.natCast_emod, show ((a + (W - b) : Nat) : Int) = ((a : Int) - b) + W by omega,
    Int.add_emod_right]

/-- **The operators agree.**  On words representing its operands, an
operator's tail computes the word of the interpreter's checked result, or
reverts exactly when the interpreter does.

Example: `a + b` with `a = 2^256 - 1`, `b = 1`: `checkArith` reverts (the sum
is not a `uint256`), and so does `add_tail`'s guard. -/
theorem tail_sim {op : BinOp} {p : PrimTy} (hop : binInFrag op p = true) (hand : op ≠ .and)
    (hor : op ≠ .or) {va vb : Value} {wa wb : Word} (ha : ReprV p va wa) (hb : ReprV p vb wb)
    (m : Machine) :
    ValOut (op.ret p) (applyBinOp op va vb >>= checkArith (op.retTy (.prim p)))
      (run (binTail p op) { m with stack := wb :: wa :: m.stack }) m := by
  cases p with
  | int => exact stail_sim hop hand hor ha hb m
  | bool =>
    show ValOut _ _ (run (uTail op) _) m
    obtain ⟨a, rfl, rfl⟩ := ha.bool_inv
    obtain ⟨b, rfl, rfl⟩ := hb.bool_inv
    have cmp := cmp_tail m m.stack (bword a) (bword b)
    cases op <;> simp [binInFrag] at hop hand hor
    · have e : decide (bword a = bword b) = decide (a = b) := by cases a <;> cases b <;> rfl
      refine .inl ⟨_, _, by simp [applyBinOp]; rfl,
        ReprV.bool (decide (a = b)), ?_⟩
      rw [cmp.2.2.2.2.1, e]; rfl
    · have e : decide (bword a = bword b) = decide (a = b) := by cases a <;> cases b <;> rfl
      refine .inl ⟨_, _, by simp [applyBinOp]; rfl,
        ReprV.bool (!decide (a = b)), ?_⟩
      rw [cmp.2.2.2.2.2, e]; rfl
  | uint =>
    show ValOut _ _ (run (uTail op) _) m
    obtain ⟨a, ha', rfl, rfl⟩ := ha.uint_inv
    obtain ⟨b, hb', rfl, rfl⟩ := hb.uint_inv
    clear ha hb
    cases op <;> simp [binInFrag] at hop hand hor
    · -- `+`
      rw [add_tail m m.stack ha' hb', (src_arith ha').1]
      by_cases h : a + b < W
      · exact .inl ⟨.int ↑(a + b), .val (a + b), by simp [h], ReprV.uint h, by simp [h]; rfl⟩
      · exact .inr ⟨by simp [h], by simp [h]⟩
    · -- `-`
      rw [sub_tail m m.stack ha' hb', (src_arith ha').2.1]
      by_cases h : b ≤ a
      · exact .inl ⟨.int ↑(a - b), .val (a - b), by simp [h], ReprV.uint (by omega),
          by simp [h]; rfl⟩
      · exact .inr ⟨by simp [h], by simp [h]⟩
    · -- `*`
      rw [mul_tail m m.stack ha', (src_arith ha').2.2.1]
      by_cases h : a * b < W
      · exact .inl ⟨.int ↑(a * b), .val (a * b), by simp [h], ReprV.uint h, by simp [h]; rfl⟩
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
      · exact .inl ⟨.int ↑(a ^ b), .val (a ^ b), by simp [h], ReprV.uint h, by simp [h]; rfl⟩
      · exact .inr ⟨by simp [h], by simp [h]⟩
    · -- `/`
      rw [div_tail, (src_arith ha').2.2.2.1]
      by_cases h : b = 0
      · exact .inr ⟨by simp [h], by simp [h]⟩
      · exact .inl ⟨.int ↑(a / b), .val (a / b), by simp [h],
          ReprV.uint (Nat.lt_of_le_of_lt (Nat.div_le_self a b) ha'), by simp [h]; rfl⟩
    · -- `%`
      rw [mod_tail, (src_arith ha').2.2.2.2]
      by_cases h : b = 0
      · exact .inr ⟨by simp [h], by simp [h]⟩
      · exact .inl ⟨.int ↑(a % b), .val (a % b), by simp [h],
          ReprV.uint (Nat.lt_of_le_of_lt (Nat.mod_le a b) ha'), by simp [h]; rfl⟩
    · -- `<`
      refine .inl ⟨.bool (decide (a < b)), _, ?_, ReprV.bool _, (cmp_tail m m.stack a b).1⟩
      simp [applyBinOp, checkArith, Value.asInt, bind, Except.bind]
    · -- `>`
      refine .inl ⟨.bool (decide (b < a)), _, ?_, ReprV.bool _, (cmp_tail m m.stack a b).2.1⟩
      simp [applyBinOp, checkArith, Value.asInt, bind, Except.bind]
    · -- `<=`
      refine .inl ⟨.bool (decide (a ≤ b)), _, ?_, ReprV.bool _, (cmp_tail m m.stack a b).2.2.1⟩
      simp [applyBinOp, checkArith, Value.asInt, bind, Except.bind]
    · -- `>=`
      refine .inl ⟨.bool (decide (b ≤ a)), _, ?_, ReprV.bool _, (cmp_tail m m.stack a b).2.2.2.1⟩
      simp [applyBinOp, checkArith, Value.asInt, bind, Except.bind]
    · -- `==`
      refine .inl ⟨.bool (decide (a = b)), _, ?_, ReprV.bool _, (cmp_tail m m.stack a b).2.2.2.2.1⟩
      simp [applyBinOp, checkArith, bind, Except.bind, Int.natCast_inj]
    · -- `!=`
      refine .inl ⟨.bool (!decide (a = b)), _, ?_, ReprV.bool _, (cmp_tail m m.stack a b).2.2.2.2.2⟩
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

/-- The machine's environment is the state's: `CALLER` pushes `msg.sender`,
`ADDRESS` the contract's address, `address(this)`, and each of them is a word. -/
def EnvSim (σ : State) (m : Machine) : Prop :=
  σ.tx.msgSender = m.caller ∧ σ.tx.msgValue = m.callvalue ∧ σ.tx.timestamp = m.timestamp ∧
    σ.tx.selfAddress = m.self ∧
    m.caller < W ∧ m.callvalue < W ∧ m.timestamp < W ∧ m.self < W

/-- The ledger after a payment of `y` to `x`: as it was when `x` is the
contract itself, else `x`'s entry down by `y`. -/
theorem getNet_pay (τ : State) (x y a : Int) : (τ.pay x y).getNet a =
    if x = τ.tx.selfAddress then τ.getNet a
    else if a = x then τ.getNet x - y else τ.getNet a := by
  by_cases h1 : x = τ.tx.selfAddress
  · simp only [State.pay, State.getNet, h1, ↓reduceIte]
  · simp only [State.pay, State.getNet, h1, ↓reduceIte]
    by_cases h2 : a = x
    · subst h2; simp only [lookupBy_setBy_self, ↓reduceIte, Option.getD_some]
    · simp only [lookupBy_setBy_ne h2, h2, ↓reduceIte]

/-- A path that indexes no array may be used where any path may: `folks[7]` as an alias target and
as a read. -/
theorem PathSlot.ofTrue {C : Contract} {r : Name} {segs : List Seg} {T : Ty} {s : Slot}
    (h : PathSlot C true r segs T s) : ∀ free, PathSlot C free r segs T s
  | true => h
  | false => h.weaken

variable {C : Contract} {L : Nat} {σ : State}

/-- A primitive storage value is read as the word at its slot: `alice.age`
pushes slot `13`'s word, an `int` its two's complement. -/
theorem prim_read {st : Slot → Nat} {p : PrimTy} {s : Slot} {sv : SVal}
    (h : ReprAt st L (.prim p) s sv) :
    ∃ v, sv.asValue = .ok v ∧ ReprV p v (.val (st s)) ∧ sv = v.toSVal := by
  cases h with
  | uint h0 h1 h2 => exact ⟨_, rfl, ⟨h0, h1, h2⟩, rfl⟩
  | bool h => exact ⟨_, rfl, h, rfl⟩
  | int h0 h1 => exact ⟨_, rfl, ⟨h0, h1⟩, rfl⟩

/-- An operator other than `&&`/`||` evaluates both operands: `a + b` evaluates `b` even when `a =
0`. -/
theorem evalBinop_eq {op : BinOp} (hand : op ≠ .and) (hor : op ≠ .or) (p : PrimTy) (lv : Value)
    (b : Res Value) :
    evalBinop op p lv b =
      (b >>= fun rv => applyBinOp op lv rv >>= checkArith (op.retTy (.prim p))) := by
  cases op <;> simp at hand hor <;> cases lv <;> rfl

/-! ## Statements -/

/-- A write to a primitive leaves every array's length. -/
theorem upd_len {st : Slot → Nat} {a : Bool} {r : Name} {segs : List Seg} {p : PrimTy} {s : Slot}
    (hp : PathSlot C a r segs (.prim p) s) (v : Nat) :
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

/-- The operators with an `op=` form are compiled with their checks, at `uint`
and at `int`. -/
theorem compound_frag {op : BinOp} {p : PrimTy} (h : op.hasCompoundAssign = true)
    (hp : p ≠ .bool) :
    binInFrag op p = true ∧ op ≠ .and ∧ op ≠ .or ∧ op.ret p = p ∧
      op.retTy (.prim p) = .prim p := by
  cases op <;> cases p <;>
    simp_all [BinOp.hasCompoundAssign, binInFrag, BinOp.ret, BinOp.retTy, BinOp.isArith]

attribute [local simp] Res.ok_bind Res.error_bind

/-- Reassociating a checked result: `total += 1;` computes, checks, then writes. -/
theorem bind_bind_ok {x : Res Value} {f : Value → Res Value} {g : Value → Res State} {v : Value}
    (h : (x >>= f) = .ok v) : (x >>= fun a => f a >>= g) = g v := by
  cases x with
  | error e => cases h
  | ok a => simp only [Res.ok_bind] at h ⊢; rw [h]; rfl

/-- A failed check stops the write: `total += 1;` at `2^256 - 1` never writes. -/
theorem bind_bind_error {x : Res Value} {f : Value → Res Value} {g : Value → Res State} {e : Halt}
    (h : (x >>= f) = .error e) : (x >>= fun a => f a >>= g) = .error e := by
  cases x with
  | error e' => simp only [Res.error_bind, Except.error.injEq] at h ⊢; exact h
  | ok a => simp only [Res.ok_bind] at h ⊢; rw [h]; rfl

/-- A value written to a slot is represented there: a `uint` or a `bool` as
itself, an `int` as its word. -/
theorem repr_write {p : PrimTy} {v : Value} {w : Word}
    (hv : ReprV p v w) (st : Slot → Nat) (s : Slot) :
    ∃ a, w = .val a ∧ ReprAt (upd st s a) L (.prim p) s v.toSVal := by
  cases p with
  | uint =>
    obtain ⟨a, ha, rfl, rfl⟩ := hv.uint_inv
    exact ⟨a, rfl, .uint (Int.natCast_nonneg a) (by omega) (by simp)⟩
  | bool =>
    obtain ⟨b, rfl, rfl⟩ := hv.bool_inv
    exact ⟨_, rfl, .bool (by simp)⟩
  | int =>
    obtain ⟨a, ha, rfl, rfl⟩ := hv.int_inv
    exact ⟨a, rfl, .int (by simpa using ha) (by simp)⟩

/-- A numeric value is an integer: `total` and an `int` local both read as `.int`. -/
theorem ReprV.num_inv {p : PrimTy} {v : Value} {w : Word} (hp : p ≠ .bool) (h : ReprV p v w) :
    ∃ n, v = .int n := by
  cases p with
  | uint => obtain ⟨a, _, rfl, _⟩ := h.uint_inv; exact ⟨_, rfl⟩
  | int => obtain ⟨a, _, rfl, _⟩ := h.int_inv; exact ⟨_, rfl⟩
  | bool => exact absurd rfl hp

/-- The default a declaration binds is the word `0`. -/
theorem ReprV.default (p : PrimTy) : ReprV p (PrimTy.default p) (.val 0) := by
  cases p with
  | uint => exact ReprV.uint (a := 0) W_pos
  | bool => exact ReprV.bool false
  | int => exact ⟨W_pos, by simp⟩

/-- `x++` and `x--` are `x += 1` and `x -= 1`, checked the same way. -/
theorem bump_src (op : IncDec) (p : PrimTy) (a : Int) :
    checkArith (.prim p) (.int (if op.isIncrement then a + 1 else a - 1)) =
      (applyBinOp op.binOp (.int a) (.int 1) >>= checkArith (op.binOp.retTy (.prim p))) := by
  cases op <;> rfl

/-- `++` and `--` are the `+=`/`-=` of the fragment: `x++;` is checked as `x += 1;`. -/
theorem bump_frag (op : IncDec) : op.binOp.hasCompoundAssign = true := by
  cases op <;> rfl

/-- The step of `++`: its old value an integer, its checked result computed by
`PUSH 1` and the operator's tail, or both revert. -/
theorem bump_sim {p : PrimTy} (hp : p ≠ .bool) (op : IncDec) {old : Value} {w : Word}
    (h : ReprV p old w) (m : Machine) :
    ∃ n, old = .int n ∧ ValOut p (checkArith (.prim p) (.int (if op.isIncrement then n + 1 else n - 1)))
      (run ([.push (.val 1)] ++ binTail p op.binOp) { m with stack := w :: m.stack }) m := by
  obtain ⟨hfrag, hand, hor, hret, hretTy⟩ := compound_frag (bump_frag op) hp
  obtain ⟨n, rfl⟩ := h.num_inv hp
  refine ⟨n, rfl, ?_⟩
  rw [bump_src, run_append_ok (m' := { m with stack := .val 1 :: w :: m.stack }) rfl]
  have ht := tail_sim hfrag hand hor h (ReprV.one hp) m
  rwa [hret] at ht

/-- `x++`'s code as an expression: `… old → … new v`, with `v` the new word
for `++x` and the old one for `x++`. -/
theorem bumpCode_sim {p : PrimTy} (hp : p ≠ .bool) (op : IncDec) {old : Value} {w : Word}
    (h : ReprV p old w) (m : Machine) :
    ∃ n, old = .int n ∧
      ((∃ vn wn, checkArith (.prim p) (.int (if op.isIncrement then n + 1 else n - 1)) = .ok vn ∧
          ReprV p vn wn ∧
          run (bumpCode p op) { m with stack := w :: m.stack } =
            .ok { m with stack := wn :: (if op.isPre then wn else w) :: m.stack } 0) ∨
        (checkArith (.prim p) (.int (if op.isIncrement then n + 1 else n - 1)) = .error .revert ∧
          run (bumpCode p op) { m with stack := w :: m.stack } = .revert)) := by
  unfold bumpCode
  cases hpre : op.isPre
  · -- `x++`: the old word kept under the new one
    obtain ⟨n, rfl, hv⟩ := bump_sim hp op h { m with stack := w :: m.stack }
    refine ⟨n, rfl, ?_⟩
    simp only [if_false, Bool.false_eq_true]
    rw [show [Instr.dup 1, .push (.val 1)] ++ binTail p op.binOp =
      [Instr.dup 1] ++ ([.push (.val 1)] ++ binTail p op.binOp) from rfl,
      run_append_ok (m' := { m with stack := w :: w :: m.stack }) rfl]
    rcases hv with ⟨vn, wn, h1, h2, h3⟩ | ⟨h1, h3⟩
    · exact .inl ⟨vn, wn, h1, h2, h3⟩
    · exact .inr ⟨h1, h3⟩
  · -- `++x`: the new word twice
    obtain ⟨n, rfl, hv⟩ := bump_sim hp op h m
    refine ⟨n, rfl, ?_⟩
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
theorem storeAt_len {st : Slot → Nat} {a : Bool} {r : Name} {segs : List Seg} {R : RefTy}
    {d : Slot} (hp : PathSlot C a r segs (.ref R) d) (hst : static (.ref R) = true)
    (vs : List Nat) : ∀ x, LenSlot C x → st x ≤ storeAt st d (leaves (.ref R)).reverse vs x :=
  fun x hx => by
    rw [storeAt_other fun o ho he => len_prim_disjoint hx (by
      obtain ⟨T₀, h0, oc⟩ := hp.occAt (leavesF_occAt _ _ d o hst (List.mem_reverse.1 ho))
      exact ⟨r, T₀, h0, he ▸ oc⟩)]
    exact Nat.le_refl _

/-- A `push`'s writes: the length one more, and the new element's primitives. -/
theorem push_len {st st' : Slot → Nat} {a : Bool} {r : Name} {segs : List Seg} {E : Ty}
    {s : Slot} (hp : PathSlot C a r segs (.ref (.array E)) s) (n : Nat)
    (hs : st' s = st s + 1)
    (hw : ∀ x, x ≠ s → st' x ≠ st x → OccAt true E (.data s (n * size E)) x) :
    ∀ x, LenSlot C x → st x ≤ st' x := fun x hx => by
  by_cases hxs : x = s
  · subst hxs; omega
  · by_cases he : st' x = st x
    · omega
    · exfalso
      obtain ⟨T₀, h0, oc⟩ := hp.occAt (OccAt.elem n (hw x hxs he))
      exact len_prim_disjoint hx ⟨r, T₀, h0, oc⟩

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

/-- A copied static value is a struct or an array, so the interpreter lays it
over what is there. -/
theorem writeStorage_static {st : Slot → Nat} {R : RefTy} {s : Slot} {sv old : SVal} {τ : State}
    {r : Name} {segs : List Seg} (hr : ReprAt st L (.ref R) s sv)
    (hst : static (.ref R) = true) (hold : τ.findStorage r segs = .ok old) :
    τ.writeStorage r segs sv = τ.saveStorage r segs (old.overlay sv) := by
  cases hr with
  | struct => simp [State.writeStorage, hold]
  | fixed => simp [State.writeStorage, hold]
  | array => simp [static, staticF] at hst
  | map => simp [static, staticF] at hst
  | mapOther => simp [static, staticF] at hst

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
    (h : st x = 0) : ReprAt st L (.prim p) x (defaultForTy (.prim p)) := by
  cases p with
  | uint => rw [defaultForTy]; exact .uint (Int.le_refl 0) (by have := W_pos; omega) (by simp [h])
  | bool => rw [defaultForTy]; exact .bool (by simp [h, bword])
  | int => rw [defaultForTy]; exact .int (by rw [h]; exact W_pos) (by rw [h]; rfl)

/-- A word written is a primitive value stripped: `values.push(3)`. -/
theorem Value.toSVal_strip (v : Value) : v.toSVal.strip = v.toSVal := by cases v <;> rfl

/-! ## The headline -/

/-- A fresh contract at address `self`: its storage at every type's default,
nothing bound, nothing sent, `balance` in funds. -/
def State.fresh (C : Contract) (balance : Nat) (self : Nat := 0) : State :=
  { storage := C.initStorage, selfBalance := balance, tx := { selfAddress := self } }

end Evm
end Solidity
