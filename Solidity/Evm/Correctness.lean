import Solidity.Evm.Repr
import Solidity.Evm.Signed
import Solidity.Evm.Exp

/-!
# The compiler is correct

`Sim C L Γ σ m` says the machine `m` *represents* the interpreter state `σ`
(mini-solkey's `Sim`, with control flow, reverts and the ledger added):

* the storage, by `ReprStore` (`Evm/Repr.lean`), every dynamic array holding
  fewer than `L ≤ 2^64` elements;
* a local `Γ` types as a value, by its memory cell (`ReprV`: an `int` as its
  two's complement word);
* a storage alias, by its memory cell holding the slot of the path it is bound
  to — a path that indexes no array, so the slot stays the path's; or, for a
  *fragile* alias bound through an index, a path in bounds, which stays in
  bounds because nothing but `pop` and `delete` lowers a length
  (`live_mono`), and those make the fragment forget it;
* the contract's funds and the `net` ledger, by the machine's.

**The headline** (`compile_correct`): for a program of the fragment
(`wtProg Γ P = some Γ'`), a machine representing the state it starts in, and
room for its pushes (`L + pushesP P ≤ 2^64`), the interpreter and the compiled
code *agree*: either both succeed, the machine's stack as it was and the
machine representing the interpreter's final state, or both revert.  The
interpreter is never stuck on the fragment.  `compile_storage` states it from
a fresh contract, for the storage alone: every typed `uint` path reads at its
slot what the interpreter reads there.

The bound is solc's: `push` reverts at `2^64` elements (`Panic(0x41)`), the
interpreter's arrays are unbounded, and the two agree as long as no array
reaches it.  A program has no loops, so it grows an array by at most its
`push` count; from a fresh contract (`L = 1`) any program with fewer than
`2^64 - 1` pushes qualifies.

The proof is a forward simulation by structural recursion on the syntax, one
lemma per syntactic class, each a *dichotomy*: `ValOut` (a value pushed, or
both revert), `LocOut` (a slot pushed, or both revert), `StmtOut`.  Being
total, they make the order of evaluation irrelevant where the two disagree on
it: the interpreter evaluates an `op=`'s right-hand side before its target,
the compiled code the target first, and they revert together either way.

The machine lemmas at the top compute the guard sequences of `Compile.lean`:
`add_tail`/`sub_tail`/`mul_tail` are solc's overflow checks, exact on words
below `2^256` (`mul_ok_iff` is the arithmetic fact behind the `*` check); the
signed ones are `Evm/Signed.lean`'s, `**` is `Evm/Exp.lean`'s.
-/

namespace Solidity
namespace Evm

open Semantics SemanticsProperties

/-! ## The guard sequences -/

/-- A successful step goes on: `uint x = 1;` then the next statement. -/
theorem Except.ok_bind' {ε α β : Type} (x : α) (f : α → Except ε β) :
    (Except.ok x >>= f) = f x := rfl
/-- A revert stops the rest: `revert(); total = 1;` never writes. -/
theorem Except.error_bind' {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl


/-- A sum below `2^256` does not wrap: `3 + 4` is `7`. -/
theorem mod_W_of_lt {x : Nat} (h : x < W) : x % W = x := Nat.mod_eq_of_lt h

/-- A sum of two words that wraps loses exactly `2^256`: `(2^256 - 1) + 1` wraps to `0`. -/
theorem mod_W_of_ge {x : Nat} (h₁ : W ≤ x) (h₂ : x < W + W) : x % W = x - W := by
  rw [Nat.mod_eq_sub_mod h₁, Nat.mod_eq_of_lt (by omega)]

/-- `OR` of two comparison words is `0` exactly when both are false (the `*` guard). -/
@[simp] theorem bword_or_eq_zero (x y : Bool) :
    (bword x ||| bword y) = 0 ↔ x = false ∧ y = false := by
  cases x <;> cases y <;> decide

/-- Comparison words tell `true` from `false`: `flag == true` compares `1` with `1`. -/
theorem bword_inj {x y : Bool} (h : bword x = bword y) : x = y := by
  cases x <;> cases y <;> simp_all [bword]

/-- A failed guard reverts. -/
theorem assertTop_zero (m : Machine) (st : List Word) (rest : List Instr) :
    run (assertTop ++ rest) { m with stack := .val 0 :: st } = .revert := rfl

/-- A passed guard goes on. -/
theorem assertTop_ok (m : Machine) (st : List Word) (rest : List Instr) {c : Nat} (hc : c ≠ 0) :
    run (assertTop ++ rest) { m with stack := .val c :: st } = run rest { m with stack := st } := by
  simp [run, assertTop, Instr.step, hc]

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

/-- A word represents its signed reading as an `int`. -/
theorem ReprV.ofWord {a : Nat} (h : a < W) : ReprV .int (.int (sgn a)) (.val a) := ⟨h, rfl⟩

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
  rw [e1, e2, hsrc, hrun, Except.ok_bind', checkArith_uint, if_pos (by omega)]
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
        rw [e1, e2, Except.ok_bind', checkArith_uint]
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
and each of them, the funds included, is a word. -/
def EnvSim (σ : State) (m : Machine) : Prop :=
  σ.tx.msgSender = m.caller ∧ σ.tx.msgValue = m.callvalue ∧ σ.tx.timestamp = m.timestamp ∧
    m.caller < W ∧ m.callvalue < W ∧ m.timestamp < W ∧ m.balance < W

/-- The machine `m` represents the interpreter state `σ`, whose locals `Γ` types. -/
structure Sim (C : Contract) (L : Nat) (Γ : TyCtx) (σ : State) (m : Machine) : Prop where
  store : ReprStore C L m.store σ.storage
  vals : ∀ x p, Γ x = some (.val p) →
    ∃ v, lookupBy x σ.env = some (.val v) ∧ ReprV p v (m.mem x)
  aliases : ∀ x R, Γ x = some (.alias R) →
    ∃ r segs s, lookupBy x σ.env = some (.spath r segs) ∧ m.mem x = .slot s ∧
      PathSlot C true r segs (.ref R) s
  balance : σ.selfBalance = m.balance
  net : ∀ a : Nat, a < W → σ.getNet a = m.net a
  /-- The bound on the arrays is at most solc's. -/
  bound : L ≤ Lmax
  /-- A fragile alias: its cell holds the slot of a path that indexes an
  array, and that path is in bounds. -/
  fragile : ∀ x R, Γ x = some (.falias R) →
    ∃ r segs s, lookupBy x σ.env = some (.spath r segs) ∧ m.mem x = .slot s ∧
      PathSlot C false r segs (.ref R) s ∧ ∃ sv, σ.findLive r segs = .ok sv
  /-- `msg.sender`, `msg.value`, `block.timestamp`, the funds. -/
  env : EnvSim σ m

/-- `Sim` does not look at the stack. -/
theorem Sim.stack {C : Contract} {L : Nat} {Γ : TyCtx} {σ : State} {m : Machine} (h : Sim C L Γ σ m)
    (st : List Word) : Sim C L Γ σ { m with stack := st } :=
  ⟨h.store, h.vals, h.aliases, h.balance, h.net, h.bound, h.fragile, h.env⟩

/-- Pushing a word keeps `Sim`: `total + 1` pushes `total`'s word, then `1`. -/
theorem Sim.push {C : Contract} {L : Nat} {Γ : TyCtx} {σ : State} {m : Machine} (h : Sim C L Γ σ m)
    (w : Word) : Sim C L Γ σ (m.push w) := h.stack _

/-- A location's outcome: its path read and its slot pushed; or both revert
while resolving it; or it resolves, and the read reverts (an index out of
bounds) and so does the machine. -/
def LocOut (C : Contract) (L : Nat) (σ : State) (free : Bool) (T : Ty) (res : Res (Name × List Seg))
    (out : Out) (m : Machine) : Prop :=
  (∃ r segs s sv, res = .ok (r, segs) ∧ σ.findLive r segs = .ok sv ∧
      PathSlot C free r segs T s ∧ ReprAt m.store L T s sv ∧ out = .ok (m.push (.slot s)) 0) ∨
    (res = .error .revert ∧ out = .revert)

/-- A path that indexes no array may be used where any path may: `folks[7]` as an alias target and
as a read. -/
theorem PathSlot.ofTrue {C : Contract} {r : Name} {segs : List Seg} {T : Ty} {s : Slot}
    (h : PathSlot C true r segs T s) : ∀ free, PathSlot C free r segs T s
  | true => h
  | false => h.weaken

variable {C : Contract} {L : Nat} {Γ : TyCtx} {σ : State}

/-- A primitive storage value is read as the word at its slot: `alice.age`
pushes slot `13`'s word, an `int` its two's complement. -/
theorem prim_read {st : Slot → Nat} {p : PrimTy} {s : Slot} {sv : SVal}
    (h : ReprAt st L (.prim p) s sv) :
    ∃ v, sv.asValue = .ok v ∧ ReprV p v (.val (st s)) ∧ sv = v.toSVal := by
  cases h with
  | uint h0 h1 h2 => exact ⟨_, rfl, ⟨h0, h1, h2⟩, rfl⟩
  | bool h => exact ⟨_, rfl, h, rfl⟩
  | int h0 h1 => exact ⟨_, rfl, ⟨h0, h1⟩, rfl⟩

/-- A literal or a local pushes its value.

Example: `x` with `x = 3` is `MLOAD x`, which pushes `3`. -/
theorem simple_sim {m : Machine} (hm : Sim C L Γ σ m) : ∀ {p : PrimTy} (s : Simple C p),
    wtSimple Γ s = true → ValOut p (s.eval σ) (run (compileSimple s) m) m
  | p, .lit n _, hw => by
    simp only [wtSimple, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
    rcases hw with ⟨⟨rfl, h0⟩, h1⟩ | ⟨⟨rfl, h0⟩, h1⟩
    · exact .inl ⟨.int n, .val (toWord n), rfl, ⟨h0, h1, by simp [toWord, h0]⟩, rfl⟩
    · exact .inl ⟨.int n, .val (toWord n), rfl, ReprV.int h0 h1, rfl⟩
  | _, .bool b, _ => .inl ⟨.bool b, .val (bword b), rfl, rfl, rfl⟩
  | p, .local x, hw => by
    have hx : Γ x = some (.val p) := by simpa [wtSimple] using hw
    obtain ⟨v, henv, hv⟩ := hm.vals x p hx
    exact .inl ⟨v, m.mem x, by simp [Simple.eval, State.getEnv, henv]; rfl, hv, rfl⟩
  | _, .env k hp, _ => by
    subst hp
    obtain ⟨h1, h2, h3, w1, w2, w3, w4⟩ := hm.env
    have hn : ∀ n : Nat, n < W → ReprV .uint (.int n) (.val n) := fun n h =>
      ⟨by omega, by exact_mod_cast h, by simp⟩
    cases k
    · exact .inl ⟨_, _, by simp [Simple.eval, State.envVal, h1]; rfl, hn _ w1, rfl⟩
    · exact .inl ⟨_, _, by simp [Simple.eval, State.envVal, h2]; rfl, hn _ w2, rfl⟩
    · exact .inl ⟨_, _, by simp [Simple.eval, State.envVal, h3]; rfl, hn _ w3, rfl⟩
    · exact .inl ⟨_, _, by simp [Simple.eval, State.envVal, hm.balance]; rfl, hn _ w4, rfl⟩

/-- An operator other than `&&`/`||` evaluates both operands: `a + b` evaluates `b` even when `a =
0`. -/
theorem evalBinop_eq {op : BinOp} (hand : op ≠ .and) (hor : op ≠ .or) (p : PrimTy) (lv : Value)
    (b : Res Value) :
    evalBinop op p lv b =
      (b >>= fun rv => applyBinOp op lv rv >>= checkArith (op.retTy (.prim p))) := by
  cases op <;> simp at hand hor <;> cases lv <;> rfl

mutual

/-- A storage path pushes its slot.

Example: after `Person storage p = folks[7];`, `p.age` compiles to
`MLOAD p; PUSH 2; ADD`, and `MLOAD p` pushes `keccak(7, 7)`. -/
theorem spath_sim : ∀ {T : Ty} (b : SPath C T) {free : Bool} {m : Machine}, Sim C L Γ σ m →
    wtSPath Γ free b = true → LocOut C L σ free T (b.resolve σ) (run (compileSPath b) m) m
  | _, @SPath.alias _ R x, free, m, hm, hw => by
    simp only [wtSPath, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true'] at hw
    rcases hw with hx | ⟨rfl, hx⟩
    · obtain ⟨r, segs, s, henv, hmem, hp⟩ := hm.aliases x R hx
      rcases find_repr hm.store hp with ⟨sv, hsv, hr⟩ | ⟨h, _⟩
      · refine .inl ⟨r, segs, s, sv, ?_, hsv, hp.ofTrue free, hr, ?_⟩
        · simp [SPath.resolve, aliasPath, State.getEnv, henv]; rfl
        · simp [compileSPath, run, Instr.step, Machine.next, hmem]; rfl
      · cases h
    · obtain ⟨r, segs, s, henv, hmem, hp, sv₀, hsv₀⟩ := hm.fragile x R hx
      rcases find_repr hm.store hp with ⟨sv, hsv, hr⟩ | ⟨_, hsv⟩
      · refine .inl ⟨r, segs, s, sv, ?_, hsv, hp, hr, ?_⟩
        · simp [SPath.resolve, aliasPath, State.getEnv, henv]; rfl
        · simp [compileSPath, run, Instr.step, Machine.next, hmem]; rfl
      · rw [hsv₀] at hsv; cases hsv
  | _, .loc l, free, m, hm, hw => by
    simp only [SPath.resolve, compileSPath]
    exact loc_sim l hm (by simpa [wtSPath] using hw)

/-- A location pushes its slot, checking every array index against the
length on the way.

Example: `folks[7].age` pushes `keccak(7, 7) + 2`; `persons[5].age` with three
persons reverts at the bounds check, as the interpreter's read does. -/
theorem loc_sim : ∀ {T : Ty} (l : Loc C T) {free : Bool} {m : Machine}, Sim C L Γ σ m →
    wtLoc Γ free l = true → LocOut C L σ free T (l.resolve σ) (run (compileLoc l) m) m
  | _, .root r h, free, m, hm, _ => by
    obtain ⟨sv, hl, hr⟩ := hm.store r _ h
    exact .inl ⟨r, [], rootSlot C r, sv, rfl, by simp [State.findLive, hl], .root h, hr, rfl⟩
  | _, @Loc.field _ s T b f h, free, m, hm, hw => by
    have hwb : wtSPath Γ free b = true := by simpa [wtLoc] using hw
    have h' : lookupBy f (structDef s) = some T := h
    simp only [Loc.resolve, compileLoc]
    rcases spath_sim b hm hwb with ⟨r, segs, s₀, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
    · cases hr with
      | struct hex hall =>
        obtain ⟨v, hv⟩ := hex f T h'
        refine .inl ⟨r, segs ++ [.field f], s₀.add (offset s f), v, ?_, ?_, .field hp h,
          hall f T v h' hv, ?_⟩
        · simp [hres]; rfl
        · rw [findLive_append, hsv]; simp [bind, Except.bind, SVal.findLive, hv]
        · rw [run_append_ok hrun]; simp [run, Instr.step, Machine.next, Machine.push]
    · exact .inr ⟨by simp [hres]; rfl, run_append_revert hrun⟩
  | _, @Loc.index _ _ k V .map b i, free, m, hm, hw => by
    have ihb : ∀ {m : Machine}, Sim C L Γ σ m → wtSPath Γ free b = true →
        LocOut C L σ free _ (b.resolve σ) (run (compileSPath b) m) m := fun hm hw => spath_sim b hm hw
    have ihi : ∀ {m : Machine}, Sim C L Γ σ m → wtVal Γ i = true →
        ValOut _ (i.eval σ) (run (compileVal i) m) m := fun hm hw => val_sim i hm hw
    simp only [wtLoc, Bool.and_eq_true, beq_iff_eq] at hw
    obtain ⟨⟨rfl, hwb⟩, hwi⟩ := hw
    simp only [Loc.resolve, compileLoc, List.append_assoc]
    rcases ihb hm hwb with ⟨r, segs, s₀, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
    · cases hr with
      | mapOther hK => exact absurd rfl hK
      | map hall =>
        rename_i entries dflt
        rw [run_append_ok hrun]
        rcases ihi (hm.push _) hwi with ⟨v, w, hv, hrep, hrun'⟩ | ⟨hv, hrun'⟩
        · obtain ⟨n, hn, rfl, rfl⟩ := hrep.uint_inv
          have hp' := PathSlot.key hp (Int.natCast_nonneg n) (by omega)
          rw [Int.toNat_natCast] at hp'
          refine .inl ⟨r, segs ++ [.at n], .hash n s₀ 0, _, ?_, ?_, hp', hall n hn, ?_⟩
          · simp [hres, hv, Value.asInt, State.checkIndex, State.findStorage_of_findLive hsv, bind,
              Except.bind, pure, Except.pure] <;> rfl
          · rw [findLive_append, hsv]
            simp only [bind, Except.bind, SVal.findLive]
            cases lookupBy (n : Int) entries <;> simp
          · rw [run_append_ok hrun']; simp [run, Instr.step, Machine.next, Machine.push]
        · exact .inr ⟨by simp [hres, hv]; rfl, run_append_revert hrun'⟩
    · exact .inr ⟨by simp [hres]; rfl, run_append_revert hrun⟩
  | _, @Loc.index _ _ _ E (.arr .dyn) b i, free, m, hm, hw => by
    have ihb : ∀ {m : Machine}, Sim C L Γ σ m → wtSPath Γ free b = true →
        LocOut C L σ free _ (b.resolve σ) (run (compileSPath b) m) m := fun hm hw => spath_sim b hm hw
    have ihi : ∀ {m : Machine}, Sim C L Γ σ m → wtVal Γ i = true →
        ValOut _ (i.eval σ) (run (compileVal i) m) m := fun hm hw => val_sim i hm hw
    simp only [wtLoc, Bool.and_eq_true, Bool.not_eq_true'] at hw
    obtain ⟨⟨rfl, hwb⟩, hwi⟩ := hw
    simp only [Loc.resolve, compileLoc, List.append_assoc]
    rcases ihb hm hwb with ⟨r, segs, s₀, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
    · cases hr with
      | array hl hW hall =>
        rename_i elems shadow
        rw [run_append_ok hrun]
        rcases ihi (hm.push _) hwi with ⟨v, w, hv, hrep, hrun'⟩ | ⟨hv, hrun'⟩
        · obtain ⟨n, hn, rfl, rfl⟩ := hrep.uint_inv
          rw [run_append_ok hrun']
          have hsv' := State.findStorage_of_findLive hsv
          have hres' : (do
              let (r, segs) ← b.resolve σ
              let i ← (← i.eval σ).asInt
              σ.checkIndex r segs i
              pure (r, segs ++ [Seg.at i]) : Res (Name × List Seg)) =
                (if n < elems.length then .ok (r, segs ++ [.at n]) else .error .revert) := by
            by_cases hin : n < elems.length <;>
              simp [hres, hv, Value.asInt, State.checkIndex, hsv', hin, bind, Except.bind, pure,
                Except.pure] <;> rfl
          rw [hres']
          have hb := boundsCheck_run m m.stack (elemSlot (size E)) n s₀
          simp only [Machine.push] at hb ⊢
          rw [hb, hl]
          by_cases hin : n < elems.length
          · rw [if_pos hin, if_pos hin]
            have hp' := PathSlot.elem hp (Int.natCast_nonneg n) (by omega)
            rw [Int.toNat_natCast] at hp'
            refine .inl ⟨r, segs ++ [.at n], .data s₀ (n * size E), elems[n], rfl, ?_, hp',
              hall n hin, elemSlot_run m m.stack n (size E) s₀⟩
            rw [findLive_append, hsv]
            simp [bind, Except.bind, SVal.findLive, hin]
          · rw [if_neg hin, if_neg hin]
            exact .inr ⟨rfl, rfl⟩
        · exact .inr ⟨by simp [hres, hv]; rfl, run_append_revert hrun'⟩
    · exact .inr ⟨by simp [hres]; rfl, run_append_revert hrun⟩
  | _, @Loc.index _ _ _ E (@IndexTy.arr _ _ (@ArrTy.fixed _ n)) b i, free, m, hm, hw => by
    have ihb : ∀ {m : Machine}, Sim C L Γ σ m → wtSPath Γ free b = true →
        LocOut C L σ free _ (b.resolve σ) (run (compileSPath b) m) m := fun hm hw => spath_sim b hm hw
    have ihi : ∀ {m : Machine}, Sim C L Γ σ m → wtVal Γ i = true →
        ValOut _ (i.eval σ) (run (compileVal i) m) m := fun hm hw => val_sim i hm hw
    simp only [wtLoc, Bool.and_eq_true, Bool.not_eq_true'] at hw
    obtain ⟨⟨rfl, hwb⟩, hwi⟩ := hw
    simp only [Loc.resolve, compileLoc, List.append_assoc]
    rcases ihb hm hwb with ⟨r, segs, s₀, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
    · cases hr with
      | fixed hl hall =>
        rename_i elems shadow
        rw [run_append_ok hrun]
        rcases ihi (hm.push _) hwi with ⟨v, w, hv, hrep, hrun'⟩ | ⟨hv, hrun'⟩
        · obtain ⟨k, hk, rfl, rfl⟩ := hrep.uint_inv
          rw [run_append_ok hrun']
          have hsv' := State.findStorage_of_findLive hsv
          have hres' : (do
              let (r, segs) ← b.resolve σ
              let i ← (← i.eval σ).asInt
              σ.checkIndex r segs i
              pure (r, segs ++ [Seg.at i]) : Res (Name × List Seg)) =
                (if k < elems.length then .ok (r, segs ++ [.at k]) else .error .revert) := by
            by_cases hin : k < elems.length <;>
              simp [hres, hv, Value.asInt, State.checkIndex, hsv', hin, bind, Except.bind, pure,
                Except.pure] <;> rfl
          rw [hres']
          have hb := fixedCheck_run m m.stack (fixedSlot (size E)) n k s₀
          simp only [Machine.push] at hb ⊢
          rw [hb, ← hl]
          by_cases hin : k < elems.length
          · rw [if_pos hin, if_pos hin]
            have hp' := PathSlot.felem hp (Int.natCast_nonneg k) (by omega)
            rw [Int.toNat_natCast] at hp'
            refine .inl ⟨r, segs ++ [.at k], s₀.add (k * size E), elems[k], rfl, ?_, hp',
              hall k hin, fixedSlot_run m m.stack k (size E) s₀⟩
            rw [findLive_append, hsv]
            simp [bind, Except.bind, SVal.findLive, hin]
          · rw [if_neg hin, if_neg hin]
            exact .inr ⟨rfl, rfl⟩
        · exact .inr ⟨by simp [hres, hv]; rfl, run_append_revert hrun'⟩
    · exact .inr ⟨by simp [hres]; rfl, run_append_revert hrun⟩

/-- An expression pushes its value, or reverts where the interpreter does.

Example: `total * 2` pushes twice `total`'s word, and reverts with the
interpreter when that overflows; `c ? a : b` runs only the branch `c` picks. -/
theorem val_sim : ∀ {p : PrimTy} (e : Val C p) {m : Machine}, Sim C L Γ σ m →
    wtVal Γ e = true → ValOut p (e.eval σ) (run (compileVal e) m) m
  | _, .simple s, m, hm, hw => by
    simp only [Val.eval, compileVal]
    exact simple_sim hm s (by simpa [wtVal] using hw)
  | p, .read l, m, hm, hw => by
    simp only [wtVal] at hw
    simp only [Val.eval, compileVal]
    rcases loc_sim l hm hw with ⟨r, segs, s, sv, hres, hsv, _, hr, hrun⟩ | ⟨hres, hrun⟩
    · rw [run_append_ok hrun]
      obtain ⟨v, hv, hrv, _⟩ := prim_read hr
      refine .inl ⟨v, .val (m.store s), ?_, hrv, rfl⟩
      simp [hres, (State.findStorage_of_findLive hsv), hv, bind, Except.bind]
    · exact .inr ⟨by simp [hres]; rfl, run_append_revert hrun⟩
  | _, @Val.binop _ p q op hacc hq a b, m, hm, hw => by
    have iha : ∀ {m : Machine}, Sim C L Γ σ m → wtVal Γ a = true →
        ValOut p (a.eval σ) (run (compileVal a) m) m := fun hm hw => val_sim a hm hw
    have ihb : ∀ {m : Machine}, Sim C L Γ σ m → wtVal Γ b = true →
        ValOut p (b.eval σ) (run (compileVal b) m) m := fun hm hw => val_sim b hm hw
    subst hq
    simp only [wtVal, Bool.and_eq_true] at hw
    obtain ⟨⟨hop, hwa⟩, hwb⟩ := hw
    simp only [Val.eval]
    by_cases hand : op = .and
    · subst hand
      obtain rfl : p = .bool := by cases p <;> simp [binInFrag] at hop ⊢
      simp only [compileVal, List.append_assoc]
      rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
      · obtain ⟨x, rfl, rfl⟩ := hra.bool_inv
        rw [run_append_ok hruna, hva]
        cases x
        · refine .inl ⟨.bool false, .val (bword false), rfl, rfl, ?_⟩
          rw [show [Instr.dup 1, .iszero, .jumpi ((compileVal b).length + 1), .pop] ++ compileVal b
            = [Instr.dup 1, .iszero, .jumpi ((compileVal b).length + 1)] ++ ([.pop] ++ compileVal b)
            from rfl, run_append_skip (m' := m.push (.val (bword false)))
            (k := (compileVal b).length + 1) rfl]
          exact exec_length ([.pop] ++ compileVal b) _
        · rw [show [Instr.dup 1, .iszero, .jumpi ((compileVal b).length + 1), .pop] ++ compileVal b
            = [Instr.dup 1, .iszero, .jumpi ((compileVal b).length + 1), .pop] ++ compileVal b
            from rfl, run_append_ok (m' := m) rfl]
          rcases ihb hm hwb with ⟨vb, wb, hvb, hrb, hrunb⟩ | ⟨hvb, hrunb⟩
          · obtain ⟨y, rfl, rfl⟩ := hrb.bool_inv
            refine .inl ⟨.bool y, .val (bword y), ?_, rfl, hrunb⟩
            simp [evalBinop, hvb, applyBinOp, Value.asBool, checkArith, bind, Except.bind]
          · exact .inr ⟨by simp [evalBinop, hvb, bind, Except.bind], hrunb⟩
      · exact .inr ⟨by simp [hva, bind, Except.bind], run_append_revert hruna⟩
    by_cases hor : op = .or
    · subst hor
      obtain rfl : p = .bool := by cases p <;> simp [binInFrag] at hop ⊢
      simp only [compileVal, List.append_assoc]
      rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
      · obtain ⟨x, rfl, rfl⟩ := hra.bool_inv
        rw [run_append_ok hruna, hva]
        cases x
        · rw [show [Instr.dup 1, .jumpi ((compileVal b).length + 1), .pop] ++ compileVal b
            = [Instr.dup 1, .jumpi ((compileVal b).length + 1), .pop] ++ compileVal b
            from rfl, run_append_ok (m' := m) rfl]
          rcases ihb hm hwb with ⟨vb, wb, hvb, hrb, hrunb⟩ | ⟨hvb, hrunb⟩
          · obtain ⟨y, rfl, rfl⟩ := hrb.bool_inv
            refine .inl ⟨.bool y, .val (bword y), ?_, rfl, hrunb⟩
            simp [evalBinop, hvb, applyBinOp, Value.asBool, checkArith, bind, Except.bind]
          · exact .inr ⟨by simp [evalBinop, hvb, bind, Except.bind], hrunb⟩
        · refine .inl ⟨.bool true, .val (bword true), rfl, rfl, ?_⟩
          rw [show [Instr.dup 1, .jumpi ((compileVal b).length + 1), .pop] ++ compileVal b
            = [Instr.dup 1, .jumpi ((compileVal b).length + 1)] ++ ([.pop] ++ compileVal b)
            from rfl, run_append_skip (m' := m.push (.val (bword true)))
            (k := (compileVal b).length + 1) rfl]
          exact exec_length ([.pop] ++ compileVal b) _
      · exact .inr ⟨by simp [hva, bind, Except.bind], run_append_revert hruna⟩
    have hcode :
        compileVal (.binop op hacc rfl a b) = compileVal a ++ compileVal b ++ binTail p op := by
      cases op <;> simp_all [compileVal]
    rw [hcode, List.append_assoc]
    rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
    · rw [run_append_ok hruna, hva]
      simp only [bind, Except.bind]
      rw [evalBinop_eq hand hor]
      rcases ihb (hm.push wa) hwb with ⟨vb, wb, hvb, hrb, hrunb⟩ | ⟨hvb, hrunb⟩
      · rw [run_append_ok hrunb, hvb]
        exact tail_sim hop hand hor hra hrb m
      · exact .inr ⟨by rw [hvb]; rfl, run_append_revert hrunb⟩
    · exact .inr ⟨by simp [hva, bind, Except.bind], run_append_revert hruna⟩
  | _, @Val.unop _ p q op hacc hq a, m, hm, hw => by
    have iha : ∀ {m : Machine}, Sim C L Γ σ m → wtVal Γ a = true →
        ValOut p (a.eval σ) (run (compileVal a) m) m := fun hm hw => val_sim a hm hw
    subst hq
    simp only [wtVal, Bool.and_eq_true] at hw
    obtain ⟨hop, hwa⟩ := hw
    cases op with
    | not =>
      obtain rfl : p = .bool := by cases p <;> simp [UnOp.accepts] at hacc ⊢
      simp only [Val.eval, compileVal]
      rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
      · obtain ⟨x, rfl, rfl⟩ := hra.bool_inv
        rw [run_append_ok hruna, hva]
        refine .inl ⟨.bool !x, .val (bword !x), ?_, rfl, ?_⟩
        · simp [applyUnOp, Value.asBool, unopCheck, bind, Except.bind]; rfl
        · cases x <;> rfl
      · exact .inr ⟨by simp [hva, bind, Except.bind], run_append_revert hruna⟩
    | neg =>
      obtain rfl : p = .int := by simpa [unInFrag] using hop
      simp only [Val.eval, compileVal]
      rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
      · obtain ⟨a, ha, rfl, rfl⟩ := hra.int_inv
        rw [run_append_ok hruna, hva]
        simp only [Machine.push]
        rw [neg_run m m.stack ha]
        change ValOut _ (checkArith (.prim .int) (.int (-sgn a))) _ _
        rw [checkArith_int]
        by_cases h : -(H : Int) ≤ -sgn a ∧ -sgn a < H
        · rw [if_pos h, if_pos h]; exact .inl ⟨_, _, rfl, ReprV.int h.1 h.2, rfl⟩
        · rw [if_neg h, if_neg h]; exact .inr ⟨rfl, rfl⟩
      · exact .inr ⟨by simp [hva, bind, Except.bind], run_append_revert hruna⟩
    | bnot =>
      obtain rfl : p = .uint := by simpa [unInFrag] using hop
      simp only [Val.eval, compileVal]
      rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
      · obtain ⟨a, ha, rfl, rfl⟩ := hra.uint_inv
        rw [run_append_ok hruna, hva]
        have := W_pos
        refine .inl ⟨.int ↑(W - 1 - a), .val (W - 1 - a), ?_, ReprV.uint (by omega), ?_⟩
        · simp only [applyUnOp, Value.asInt, unopCheck, bind, Except.bind, pure, Except.pure,
            uintBound_eq]
          congr 2; omega
        · simp [run, Instr.step, Machine.next]; rfl
      · exact .inr ⟨by simp [hva, bind, Except.bind], run_append_revert hruna⟩
  | p, .ternary c a b, m, hm, hw => by
    have ihc : ∀ {m : Machine}, Sim C L Γ σ m → wtVal Γ c = true →
        ValOut .bool (c.eval σ) (run (compileVal c) m) m := fun hm hw => val_sim c hm hw
    have iha : ∀ {m : Machine}, Sim C L Γ σ m → wtVal Γ a = true →
        ValOut p (a.eval σ) (run (compileVal a) m) m := fun hm hw => val_sim a hm hw
    have ihb : ∀ {m : Machine}, Sim C L Γ σ m → wtVal Γ b = true →
        ValOut p (b.eval σ) (run (compileVal b) m) m := fun hm hw => val_sim b hm hw
    simp only [wtVal, Bool.and_eq_true] at hw
    obtain ⟨⟨hwc, hwa⟩, hwb⟩ := hw
    simp only [Val.eval, compileVal, List.append_assoc]
    rcases ihc hm hwc with ⟨vc, wc, hvc, hrc, hrunc⟩ | ⟨hvc, hrunc⟩
    · obtain ⟨x, rfl, rfl⟩ := hrc.bool_inv
      rw [run_append_ok hrunc, hvc]
      cases x
      · rw [run_append_skip (m' := m) (k := (compileVal a).length + 1) rfl,
          show (compileVal a).length + 1 = (compileVal a).length + 1 from rfl, exec_append,
          exec_skip]
        simp only [Out.ok_bind]
        exact ihb hm hwb
      · rw [run_append_skip (m' := m) (k := 0) rfl]
        rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
        · refine .inl ⟨va, wa, hva, hra, ?_⟩
          change run _ m = _
          rw [run_append_ok hruna]
          exact exec_length _ _
        · exact .inr ⟨hva, run_append_revert hruna⟩
    · exact .inr ⟨by simp [hvc, bind, Except.bind], run_append_revert hrunc⟩
  | _, .len b hp, m, hm, hw => by
    cases hp
    simp only [wtVal] at hw
    simp only [Val.eval, compileVal]
    rcases spath_sim b hm hw with ⟨r, segs, s, sv, hres, hsv, _, hr, hrun⟩ | ⟨hres, hrun⟩
    · cases hr with
      | @array _ _ elems shadow hl hW _ =>
        rw [run_append_ok hrun]
        have := hm.bound; have := Lmax_lt_W
        refine .inl ⟨.int elems.length, .val elems.length, ?_, ReprV.uint (by omega), ?_⟩
        · simp [hres, State.findStorage_of_findLive hsv, arrayLen, bind, Except.bind]; rfl
        · simp [run, Instr.step, Machine.next, Machine.push, hl]
    · exact .inr ⟨by simp [hres]; rfl, run_append_revert hrun⟩
  | _, .readMem _, _, _, hw => by simp [wtVal] at hw
  | _, .mlen .., _, _, hw => by simp [wtVal] at hw

end

/-! ## Statements -/

/-- A statement's outcome: both succeed, the machine's stack as it was and the
states related, or both revert. -/
def StmtOut (C : Contract) (L : Nat) (Γ' : TyCtx) (res : Res State) (out : Out) (m : Machine) : Prop :=
  (∃ σ' m', res = .ok σ' ∧ out = .ok m' 0 ∧ m'.stack = m.stack ∧ Sim C L Γ' σ' m') ∨
    (res = .error .revert ∧ out = .revert)

/-- Forgetting locals keeps `Sim`: after `if`, only what both branches agree on. -/
theorem Sim.weaken {Γ' : TyCtx} {m : Machine} (h : Sim C L Γ σ m)
    (hΓ : ∀ x t, Γ' x = some t → Γ x = some t) : Sim C L Γ' σ m :=
  ⟨h.store, fun x p hx => h.vals x p (hΓ x _ hx), fun x R hx => h.aliases x R (hΓ x _ hx),
    h.balance, h.net, h.bound, fun x R hx => h.fragile x R (hΓ x _ hx), h.env⟩

/-- `uint x = e;`: the cell of `x` and the binding of `x` change together. -/
theorem Sim.bindVal {m : Machine} (h : Sim C L Γ σ m) (x : Var) {p : PrimTy} {v : Value} {w : Word}
    (hv : ReprV p v w) :
    Sim C L (Γ.set x (some (.val p))) (σ.setEnv x (.val v)) { m with mem := upd m.mem x w } := by
  refine ⟨h.store, fun y q hy => ?_, fun y R hy => ?_, h.balance, h.net, h.bound,
    fun y R hy => ?_, h.env⟩
  · by_cases hyx : y = x
    · subst hyx
      simp only [TyCtx.set, upd_same, Option.some.injEq, LTy.val.injEq] at hy
      subst hy
      exact ⟨v, by simp [State.setEnv], by simpa using hv⟩
    · simp only [TyCtx.set, upd_other _ _ hyx] at hy
      obtain ⟨v', h1, h2⟩ := h.vals y q hy
      exact ⟨v', by simp [State.setEnv, lookupBy_setBy_ne hyx, h1], by simpa [upd_other _ _ hyx]⟩
  · by_cases hyx : y = x
    · subst hyx; simp [TyCtx.set] at hy
    · simp only [TyCtx.set, upd_other _ _ hyx] at hy
      obtain ⟨r, segs, s, h1, h2, h3⟩ := h.aliases y R hy
      exact ⟨r, segs, s, by simp [State.setEnv, lookupBy_setBy_ne hyx, h1],
        by simp [upd_other _ _ hyx, h2], h3⟩
  · by_cases hyx : y = x
    · subst hyx; simp [TyCtx.set] at hy
    · simp only [TyCtx.set, upd_other _ _ hyx] at hy
      obtain ⟨r, segs, s, h1, h2, h3, h4⟩ := h.fragile y R hy
      exact ⟨r, segs, s, by simp [State.setEnv, lookupBy_setBy_ne hyx, h1],
        by simp [upd_other _ _ hyx, h2], h3, h4⟩

/-- `Person storage p = alice;`: the cell of `p` holds `alice`'s slot. -/
theorem Sim.bindAlias {m : Machine} (h : Sim C L Γ σ m) (x : Var) {R : RefTy} {r : Name}
    {segs : List Seg} {s : Slot} (hp : PathSlot C true r segs (.ref R) s) :
    Sim C L (Γ.set x (some (.alias R))) (σ.setEnv x (.spath r segs))
      { m with mem := upd m.mem x (.slot s) } := by
  refine ⟨h.store, fun y q hy => ?_, fun y R' hy => ?_, h.balance, h.net, h.bound,
    fun y R' hy => ?_, h.env⟩
  · by_cases hyx : y = x
    · subst hyx; simp [TyCtx.set] at hy
    · simp only [TyCtx.set, upd_other _ _ hyx] at hy
      obtain ⟨v', h1, h2⟩ := h.vals y q hy
      exact ⟨v', by simp [State.setEnv, lookupBy_setBy_ne hyx, h1], by simpa [upd_other _ _ hyx]⟩
  · by_cases hyx : y = x
    · subst hyx
      simp only [TyCtx.set, upd_same, Option.some.injEq, LTy.alias.injEq] at hy
      subst hy
      exact ⟨r, segs, s, by simp [State.setEnv], by simp, hp⟩
    · simp only [TyCtx.set, upd_other _ _ hyx] at hy
      obtain ⟨r', segs', s', h1, h2, h3⟩ := h.aliases y R' hy
      exact ⟨r', segs', s', by simp [State.setEnv, lookupBy_setBy_ne hyx, h1],
        by simp [upd_other _ _ hyx, h2], h3⟩
  · by_cases hyx : y = x
    · subst hyx; simp [TyCtx.set] at hy
    · simp only [TyCtx.set, upd_other _ _ hyx] at hy
      obtain ⟨r', segs', s', h1, h2, h3, h4⟩ := h.fragile y R' hy
      exact ⟨r', segs', s', by simp [State.setEnv, lookupBy_setBy_ne hyx, h1],
        by simp [upd_other _ _ hyx, h2], h3, h4⟩

/-- `Person storage p = persons[i];`: a fragile alias, its cell the slot of a
path in bounds. -/
theorem Sim.bindFragile {m : Machine} (h : Sim C L Γ σ m) (x : Var) {R : RefTy} {r : Name}
    {segs : List Seg} {s : Slot} (hp : PathSlot C false r segs (.ref R) s)
    (hlive : ∃ sv, σ.findLive r segs = .ok sv) :
    Sim C L (Γ.set x (some (.falias R))) (σ.setEnv x (.spath r segs))
      { m with mem := upd m.mem x (.slot s) } := by
  refine ⟨h.store, fun y q hy => ?_, fun y R' hy => ?_, h.balance, h.net, h.bound,
    fun y R' hy => ?_, h.env⟩
  · by_cases hyx : y = x
    · subst hyx; simp [TyCtx.set] at hy
    · simp only [TyCtx.set, upd_other _ _ hyx] at hy
      obtain ⟨v', h1, h2⟩ := h.vals y q hy
      exact ⟨v', by simp [State.setEnv, lookupBy_setBy_ne hyx, h1], by simpa [upd_other _ _ hyx]⟩
  · by_cases hyx : y = x
    · subst hyx; simp [TyCtx.set] at hy
    · simp only [TyCtx.set, upd_other _ _ hyx] at hy
      obtain ⟨r', segs', s', h1, h2, h3⟩ := h.aliases y R' hy
      exact ⟨r', segs', s', by simp [State.setEnv, lookupBy_setBy_ne hyx, h1],
        by simp [upd_other _ _ hyx, h2], h3⟩
  · by_cases hyx : y = x
    · subst hyx
      simp only [TyCtx.set, upd_same, Option.some.injEq, LTy.falias.injEq] at hy
      subst hy
      exact ⟨r, segs, s, by simp [State.setEnv], by simp, hp, hlive⟩
    · simp only [TyCtx.set, upd_other _ _ hyx] at hy
      obtain ⟨r', segs', s', h1, h2, h3, h4⟩ := h.fragile y R' hy
      exact ⟨r', segs', s', by simp [State.setEnv, lookupBy_setBy_ne hyx, h1],
        by simp [upd_other _ _ hyx, h2], h3, h4⟩

/-- A storage write: the new storage represented by the new machine storage,
and no array's length slot lower (so the fragile aliases stay in bounds,
`live_mono`). -/
theorem Sim.store' {m : Machine} (h : Sim C L Γ σ m) {st' : Slot → Nat} {stor : List (Name × SVal)}
    (hs : ReprStore C L st' stor) (hlen : ∀ x, LenSlot C x → m.store x ≤ st' x) :
    Sim C L Γ { σ with storage := stor } { m with store := st' } :=
  ⟨hs, h.vals, h.aliases, h.balance, h.net, h.bound, fun x R hx => by
    obtain ⟨r, segs, s, h1, h2, h3, h4⟩ := h.fragile x R hx
    exact ⟨r, segs, s, h1, h2, h3, live_mono (σ' := { σ with storage := stor }) h.store hs hlen h3 h4⟩, h.env⟩

/-- A storage write that may shrink an array (`pop`, `delete`): the fragile
aliases forgotten. -/
theorem Sim.storeDrop {m : Machine} (h : Sim C L Γ σ m) {st' : Slot → Nat}
    {stor : List (Name × SVal)} (hs : ReprStore C L st' stor) :
    Sim C L Γ.dropFragile { σ with storage := stor } { m with store := st' } := by
  refine ⟨hs, fun x p hx => h.vals x p ?_, fun x R hx => h.aliases x R ?_, h.balance, h.net, h.bound,
    fun x R hx => ?_, h.env⟩ <;> simp only [TyCtx.dropFragile] at hx <;> split at hx <;> simp_all

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

/-- An `op=` on a storage target resolves the target once: `folks[k].age += 1;` evaluates `k`
once. -/
theorem opLoc_store {p : PrimTy} {l : OpLoc C p} {loc : Loc C (.prim p)}
    (h : opLocToLoc l = some loc)
    (op : BinOp) (v : Value) :
    l.store σ op v = (loc.resolve σ >>= fun rs => opStore σ op p rs.1 rs.2 v) := by
  cases l <;> simp [opLocToLoc] at h <;> subst h <;> rfl


attribute [simp] Except.ok_bind' Except.error_bind'

/-- Reassociating a checked result: `total += 1;` computes, checks, then writes. -/
theorem bind_bind_ok {x : Res Value} {f : Value → Res Value} {g : Value → Res State} {v : Value}
    (h : (x >>= f) = .ok v) : (x >>= fun a => f a >>= g) = g v := by
  cases x with
  | error e => cases h
  | ok a => simp only [Except.ok_bind'] at h ⊢; rw [h]; rfl

/-- A failed check stops the write: `total += 1;` at `2^256 - 1` never writes. -/
theorem bind_bind_error {x : Res Value} {f : Value → Res Value} {g : Value → Res State} {e : Halt}
    (h : (x >>= f) = .error e) : (x >>= fun a => f a >>= g) = .error e := by
  cases x with
  | error e' => simp only [Except.error_bind', Except.error.injEq] at h ⊢; exact h
  | ok a => simp only [Except.ok_bind'] at h ⊢; rw [h]; rfl

/-- Retyping a local at its type changes nothing: `x = 3;` keeps `x` a `uint`. -/
theorem TyCtx.set_self {Δ : TyCtx} {x : Var} {t : Option LTy} (h : Δ x = t) : Δ.set x t = Δ := by
  funext y
  by_cases hy : y = x
  · subst hy; simp [TyCtx.set, h]
  · simp [TyCtx.set, upd_other _ _ hy]

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

/-- `Person storage p = folks[7];` binds the alias to the path's slot. -/
theorem alias_sim {Δ : TyCtx} {τ : State} {m : Machine} {R : RefTy} (q : SPath C (.ref R))
    (x : Var) (hm : Sim C L Δ τ m) (hw : wtSPath Δ true q = true) :
    StmtOut C L (Δ.set x (some (.alias R))) (ARhs.bind τ x (.path q))
      (run (compileSPath q ++ [.mstore x]) m) m := by
  rcases spath_sim q hm hw with ⟨r, segs, s, sv, hres, _, hp, _, hrun⟩ | ⟨hres, hrun⟩
  · refine .inl ⟨_, { m with mem := upd m.mem x (.slot s) }, ?_, ?_, rfl, hm.bindAlias x hp⟩
    · simp [ARhs.bind, hres, bind, Except.bind]; rfl
    · rw [run_append_ok hrun]; rfl
  · exact .inr ⟨by simp [ARhs.bind, hres, bind, Except.bind], run_append_revert hrun⟩

/-- `Person storage p = persons[i];` binds a fragile alias to the element's
slot; the path is in bounds, since resolving it checked the index. -/
theorem falias_sim {Δ : TyCtx} {τ : State} {m : Machine} {R : RefTy} (q : SPath C (.ref R))
    (x : Var) (hm : Sim C L Δ τ m) (hw : wtSPath Δ false q = true) :
    StmtOut C L (Δ.set x (some (.falias R))) (ARhs.bind τ x (.path q))
      (run (compileSPath q ++ [.mstore x]) m) m := by
  rcases spath_sim q hm hw with ⟨r, segs, s, sv, hres, hsv, hp, _, hrun⟩ | ⟨hres, hrun⟩
  · refine .inl ⟨_, { m with mem := upd m.mem x (.slot s) }, ?_, ?_, rfl,
      hm.bindFragile x hp ⟨sv, hsv⟩⟩
    · simp [ARhs.bind, hres, bind, Except.bind]; rfl
    · rw [run_append_ok hrun]; rfl
  · exact .inr ⟨by simp [ARhs.bind, hres, bind, Except.bind], run_append_revert hrun⟩

/-- `total += e;` and its siblings on a storage target: the target resolved
and read once, the right-hand side, the checked operator, the write back.

Example: with `total = 2^256 - 1`, `total += 1;` reverts in both; with
`total = 3` it writes `4` to slot `0`. -/
theorem opStore_sim {Δ : TyCtx} {τ : State} {m : Machine} {p : PrimTy} (hp : p ≠ .bool)
    {op : BinOp} (hop : op.hasCompoundAssign = true) {l : OpLoc C p} {loc : Loc C (.prim p)}
    (hl : opLocToLoc l = some loc) (r : Val C p) (hm : Sim C L Δ τ m)
    (hwl : wtLoc Δ false loc = true) (hwr : wtVal Δ r = true) :
    StmtOut C L Δ (do l.store τ op (← r.eval τ))
      (run (compileLoc loc ++ [.dup 1, .sload] ++ compileVal r ++ binTail p op ++
        [.swap 1, .sstore]) m)
      m := by
  obtain ⟨hfrag, hand, hor, hret, hretTy⟩ := compound_frag hop hp
  simp only [opLoc_store hl, List.append_assoc]
  rcases loc_sim loc hm hwl with ⟨rt, segs, s, sv, hres, hsv, hps, hr, hrunl⟩ | ⟨hres, hrunl⟩
  · obtain ⟨old, hold, hrold, rfl⟩ := prim_read hr
    rw [run_append_ok hrunl,
      run_append_ok (m' := { m with stack := .val (m.store s) :: .slot s :: m.stack })
      (by simp [run, Instr.step, Machine.next, Machine.push])]
    rcases val_sim r (hm.stack _) hwr with ⟨vr, wr, hvr, hrv, hrunr⟩ | ⟨hvr, hrunr⟩
    · rw [run_append_ok hrunr]
      have ht := tail_sim hfrag hand hor hrold hrv { m with stack := .slot s :: m.stack }
      rw [hret, hretTy] at ht
      rcases ht with ⟨vn, wn, hvn, hrn, hrunt⟩ | ⟨hvn, hrunt⟩
      · obtain ⟨an, rfl, hnew⟩ := repr_write (L := L) hrn m.store s
        obtain ⟨stor, hsave, hrep⟩ := save_repr hm.store hps ⟨_, hsv⟩ hnew
          (fun x hx => upd_other _ _ fun he => hx (he ▸ Occ.prim))
        refine .inl ⟨_, { m with store := upd m.store s an }, ?_, ?_, rfl,
          hm.store' hrep (upd_len hps an)⟩
        · simp only [hvr, hres, Except.ok_bind', opStore, (State.findStorage_of_findLive hsv),
            hold]
          rw [bind_bind_ok hvn]; exact hsave
        · change run (binTail p op ++ _)
            { m with stack := wr :: .val (m.store s) :: .slot s :: m.stack } = _
          rw [run_append_ok hrunt]; rfl
      · refine .inr ⟨?_, ?_⟩
        · simp only [hvr, hres, Except.ok_bind', opStore, (State.findStorage_of_findLive hsv),
            hold]
          rw [bind_bind_error hvn]
        · change run (binTail p op ++ _)
            { m with stack := wr :: .val (m.store s) :: .slot s :: m.stack } = _
          rw [run_append_revert hrunt]
    · exact .inr ⟨by simp [hvr, bind, Except.bind], run_append_revert hrunr⟩
  · rcases val_sim r hm hwr with ⟨vr, wr, hvr, _, _⟩ | ⟨hvr, _⟩
    · exact .inr ⟨by simp [hvr, hres, bind, Except.bind], run_append_revert hrunl⟩
    · exact .inr ⟨by simp [hvr, bind, Except.bind], run_append_revert hrunl⟩

/-- `x += e;` on a numeric local: its cell read, the checked operator, the cell
written. -/
theorem opLocal_sim {Δ : TyCtx} {τ : State} {m : Machine} {p : PrimTy} (hp : p ≠ .bool)
    {op : BinOp} (hop : op.hasCompoundAssign = true) (x : Var) (r : Val C p) (hm : Sim C L Δ τ m)
    (hx : Δ x = some (.val p)) (hwr : wtVal Δ r = true) :
    StmtOut C L Δ (do (OpLoc.local (C := C) (p := p) x).store τ op (← r.eval τ))
      (run ([.mload x] ++ compileVal r ++ binTail p op ++ [.mstore x]) m) m := by
  obtain ⟨hfrag, hand, hor, hret, hretTy⟩ := compound_frag hop hp
  obtain ⟨old, henv, hrold⟩ := hm.vals x p hx
  simp only [List.append_assoc]
  rw [run_append_ok (m' := m.push (m.mem x)) rfl]
  rcases val_sim r (hm.push _) hwr with ⟨vr, wr, hvr, hrv, hrunr⟩ | ⟨hvr, hrunr⟩
  · rw [run_append_ok hrunr]
    have ht := tail_sim hfrag hand hor hrold hrv m
    rw [hret, hretTy] at ht
    rcases ht with ⟨vn, wn, hvn, hrn, hrunt⟩ | ⟨hvn, hrunt⟩
    · have hs := hm.bindVal x hrn
      rw [TyCtx.set_self hx] at hs
      refine .inl ⟨_, { m with mem := upd m.mem x wn }, ?_, ?_, rfl, hs⟩
      · simp only [hvr, Except.ok_bind', OpLoc.store, opLocal, State.getEnv, henv, pure_bind]
        rw [bind_bind_ok hvn]; rfl
      · change run (binTail p op ++ _) { m with stack := wr :: m.mem x :: m.stack } = _
        rw [run_append_ok hrunt]; rfl
    · refine .inr ⟨?_, ?_⟩
      · simp only [hvr, Except.ok_bind', OpLoc.store, opLocal, State.getEnv, henv, pure_bind]
        rw [bind_bind_error hvn]
      · change run (binTail p op ++ _) { m with stack := wr :: m.mem x :: m.stack } = _
        rw [run_append_revert hrunt]
  · exact .inr ⟨by simp [hvr, bind, Except.bind], run_append_revert hrunr⟩

/-- `x++` and `x--` are `x += 1` and `x -= 1`, checked the same way. -/
theorem bump_src (op : IncDec) (p : PrimTy) (a : Int) :
    checkArith (.prim p) (.int (if op.isIncrement then a + 1 else a - 1)) =
      (applyBinOp op.binOp (.int a) (.int 1) >>= checkArith (op.binOp.retTy (.prim p))) := by
  cases op <;> rfl

/-- `++` and `--` are the `+=`/`-=` of the fragment: `x++;` is checked as `x += 1;`. -/
theorem bump_frag (op : IncDec) : op.binOp.hasCompoundAssign = true := by
  cases op <;> rfl

/-- `++` on a storage target resolves it once: `folks[k].age++;` evaluates `k` once. -/
theorem opLoc_bump {p : PrimTy} {l : OpLoc C p} {loc : Loc C (.prim p)}
    (h : opLocToLoc l = some loc)
    (op : IncDec) :
    l.bump σ op = (loc.resolve σ >>= fun rs => bumpStore σ op p rs.1 rs.2) := by
  cases l <;> simp [opLocToLoc] at h <;> subst h <;> rfl

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

/-- `total++;` on a storage target: read once, the checked increment, the write
back.  With `total = 2^256 - 1` both revert; with `total = 3`, slot `0` holds
`4`. -/
theorem bumpStore_sim {Δ : TyCtx} {τ : State} {m : Machine} {p : PrimTy} (hp : p ≠ .bool)
    (op : IncDec) {l : OpLoc C p} {loc : Loc C (.prim p)} (hl : opLocToLoc l = some loc)
    (hm : Sim C L Δ τ m) (hwl : wtLoc Δ false loc = true) :
    StmtOut C L Δ (do pure (← l.bump τ op).1)
      (run (compileLoc loc ++ [.dup 1, .sload, .push (.val 1)] ++ binTail p op.binOp ++
        [.swap 1, .sstore]) m) m := by
  simp only [opLoc_bump hl, List.append_assoc]
  rcases loc_sim loc hm hwl with ⟨rt, segs, s, sv, hres, hsv, hps, hr, hrunl⟩ | ⟨hres, hrunl⟩
  · obtain ⟨old, hold, hrold, rfl⟩ := prim_read hr
    obtain ⟨n, rfl, hv⟩ := bump_sim hp op hrold { m with stack := .slot s :: m.stack }
    rw [run_append_ok hrunl, show [Instr.dup 1, .sload, .push (.val 1)] ++ (binTail p op.binOp ++
        [.swap 1, .sstore]) = [Instr.dup 1, .sload] ++ (([.push (.val 1)] ++ binTail p op.binOp) ++
        [.swap 1, .sstore]) by simp,
      run_append_ok (m' := { m with stack := .val (m.store s) :: .slot s :: m.stack })
      (by simp [run, Instr.step, Machine.next, Machine.push])]
    rcases hv with ⟨vn, wn, hvn, hrn, hrunt⟩ | ⟨hvn, hrunt⟩
    · obtain ⟨an, rfl, hnew⟩ := repr_write (L := L) hrn m.store s
      obtain ⟨stor, hsave, hrep⟩ := save_repr hm.store hps ⟨_, hsv⟩ hnew
        (fun x hx => upd_other _ _ fun he => hx (he ▸ Occ.prim))
      refine .inl ⟨_, { m with store := upd m.store s an }, ?_, ?_, rfl,
        hm.store' hrep (upd_len hps an)⟩
      · simp only [hres, Except.ok_bind', bumpStore, (State.findStorage_of_findLive hsv), hold,
          Value.asInt, hvn, hsave]; rfl
      · rw [run_append_ok hrunt]; rfl
    · refine .inr ⟨?_, run_append_revert hrunt⟩
      simp only [hres, Except.ok_bind', bumpStore, (State.findStorage_of_findLive hsv), hold,
        Value.asInt, hvn]; rfl
  · exact .inr ⟨by simp [hres] <;> rfl, run_append_revert hrunl⟩

/-- `x++;` on a numeric local. -/
theorem bumpLocal_sim {Δ : TyCtx} {τ : State} {m : Machine} {p : PrimTy} (hp : p ≠ .bool)
    (op : IncDec) (x : Var) (hm : Sim C L Δ τ m) (hx : Δ x = some (.val p)) :
    StmtOut C L Δ (do pure (← (OpLoc.local (C := C) (p := p) x).bump τ op).1)
      (run ([.mload x, .push (.val 1)] ++ binTail p op.binOp ++ [.mstore x]) m) m := by
  obtain ⟨old, henv, hrold⟩ := hm.vals x p hx
  obtain ⟨n, rfl, hv⟩ := bump_sim hp op hrold m
  rw [show [Instr.mload x, .push (.val 1)] ++ binTail p op.binOp ++ [.mstore x] =
      [Instr.mload x] ++ (([.push (.val 1)] ++ binTail p op.binOp) ++ [.mstore x]) by simp,
    run_append_ok (m' := { m with stack := m.mem x :: m.stack }) rfl]
  rcases hv with ⟨vn, wn, hvn, hrn, hrunt⟩ | ⟨hvn, hrunt⟩
  · have hs := hm.bindVal x hrn
    rw [TyCtx.set_self hx] at hs
    refine .inl ⟨_, { m with mem := upd m.mem x wn }, ?_, ?_, rfl, hs⟩
    · simp only [OpLoc.bump, bumpLocal, State.getEnv, henv, Except.ok_bind', pure_bind,
        Value.asInt, hvn]; rfl
    · rw [run_append_ok hrunt]; rfl
  · refine .inr ⟨?_, run_append_revert hrunt⟩
    simp only [OpLoc.bump, bumpLocal, State.getEnv, henv, Except.ok_bind', pure_bind, Value.asInt,
      hvn]; rfl

/-- `v = x++;` on a numeric local: the cell of `x` bumped, and `v` given the
old or the new word. -/
theorem assignBumpLocal_sim {Δ : TyCtx} {τ : State} {m : Machine} {p : PrimTy} (hp : p ≠ .bool)
    (op : IncDec) (x y : Var) (hm : Sim C L Δ τ m) (hx : Δ x = some (.val p))
    (hy : Δ y = some (.val p)) :
    StmtOut C L Δ (do
        let (σ', v) ← (OpLoc.local (C := C) (p := p) y).bump τ op
        pure (σ'.setEnv x (.val v)))
      (run ([.mload y] ++ bumpCode p op ++ [.mstore y, .mstore x]) m) m := by
  obtain ⟨old, henv, hrold⟩ := hm.vals y p hy
  obtain ⟨n, rfl, hv⟩ := bumpCode_sim hp op hrold m
  rw [List.append_assoc, run_append_ok (m' := { m with stack := m.mem y :: m.stack }) rfl]
  rcases hv with ⟨vn, wn, hvn, hrn, hrunt⟩ | ⟨hvn, hrunt⟩
  · have hs := (hm.bindVal y hrn).bindVal x (v := if op.isPre then vn else .int n)
      (w := if op.isPre then wn else m.mem y) (by cases op.isPre <;> simpa)
    rw [TyCtx.set_self (by by_cases h : x = y <;> simp [TyCtx.set, upd, h, hx]),
      TyCtx.set_self hy] at hs
    refine .inl ⟨_, { m with mem := upd (upd m.mem y wn) x (if op.isPre then wn else m.mem y) },
      ?_, ?_, rfl, hs⟩
    · simp only [OpLoc.bump, bumpLocal, State.getEnv, henv, Except.ok_bind', pure_bind,
        Value.asInt, hvn]; rfl
    · rw [run_append_ok hrunt]; rfl
  · refine .inr ⟨?_, run_append_revert hrunt⟩
    simp only [OpLoc.bump, bumpLocal, State.getEnv, henv, Except.ok_bind', pure_bind, Value.asInt,
      hvn]; rfl

/-- A call's parameters: the code stores each argument in its parameter's
cell, as `Arg.bindSeq` binds it. -/
theorem args_sim : ∀ (args : List (Arg C)) {Δ Δ' : TyCtx} {τ : State} {m : Machine},
    Sim C L Δ τ m → wtArgs Δ args = some Δ' →
      StmtOut C L Δ' (Arg.bindSeq args τ) (run (argsCode args) m) m
  | [], Δ, Δ', τ, m, hm, hw => by
    simp only [wtArgs, Option.some.injEq] at hw
    subst hw
    exact .inl ⟨τ, m, rfl, rfl, rfl, hm⟩
  | a :: as, Δ, Δ', τ, m, hm, hw => by
    simp only [wtArgs] at hw
    split at hw
    · rename_i hc
      simp only [Arg.bindSeq, argsCode, List.append_assoc]
      rcases val_sim a.e hm hc with ⟨v, w, hv, hrv, hrun⟩ | ⟨hv, hrun⟩
      · rw [run_append_ok hrun, hv]
        have hm₁ := hm.bindVal a.x hrv
        rw [run_append_ok (m' := { m with mem := upd m.mem a.x w }) rfl]
        rcases args_sim as hm₁ hw with ⟨τ', m', hτ', hrun', hst', hm'⟩ | ⟨hτ', hrun'⟩
        · exact .inl ⟨τ', m', by simpa using hτ', hrun', hst', hm'⟩
        · exact .inr ⟨by simpa using hτ', hrun'⟩
      · exact .inr ⟨by simp [hv], run_append_revert hrun⟩
    · cases hw

/-- `Sim` under a looser bound on the arrays. -/
theorem Sim.mono {Γ : TyCtx} {m : Machine} {L' : Nat} (h : Sim C L Γ σ m) (hL : L ≤ L')
    (hL' : L' ≤ Lmax) : Sim C L' Γ σ m :=
  ⟨h.store.mono hL, h.vals, h.aliases, h.balance, h.net, hL', h.fragile, h.env⟩

/-- `StmtOut` under a looser bound. -/
theorem StmtOut.mono {Γ' : TyCtx} {res : Res State} {out : Out} {m : Machine} {L' : Nat}
    (h : StmtOut C L Γ' res out m) (hL : L ≤ L') (hL' : L' ≤ Lmax) : StmtOut C L' Γ' res out m := by
  rcases h with ⟨σ', m', h1, h2, h3, h4⟩ | h
  · exact .inl ⟨σ', m', h1, h2, h3, h4.mono hL hL'⟩
  · exact .inr h

/-- `v = total++;`: the target bumped, `v` given the old or the new word. -/
theorem assignBumpStore_sim {Δ : TyCtx} {τ : State} {m : Machine} {p : PrimTy} (hp : p ≠ .bool)
    (op : IncDec) (x : Var) {l : OpLoc C p} {loc : Loc C (.prim p)} (hl : opLocToLoc l = some loc)
    (hm : Sim C L Δ τ m) (hx : Δ x = some (.val p)) (hwl : wtLoc Δ false loc = true) :
    StmtOut C L Δ (do
        let (σ', v) ← l.bump τ op
        pure (σ'.setEnv x (.val v)))
      (run (compileLoc loc ++ [.dup 1, .sload] ++ bumpCode p op ++
        [.dup 3, .sstore, .swap 1, .pop, .mstore x]) m) m := by
  simp only [opLoc_bump hl, List.append_assoc]
  rcases loc_sim loc hm hwl with ⟨rt, segs, s, sv, hres, hsv, hps, hr, hrunl⟩ | ⟨hres, hrunl⟩
  · obtain ⟨old, hold, hrold, rfl⟩ := prim_read hr
    obtain ⟨n, rfl, hv⟩ := bumpCode_sim hp op hrold { m with stack := .slot s :: m.stack }
    rw [run_append_ok hrunl,
      run_append_ok (m' := { m with stack := .val (m.store s) :: .slot s :: m.stack })
      (by simp [run, Instr.step, Machine.next, Machine.push])]
    rcases hv with ⟨vn, wn, hvn, hrn, hrunt⟩ | ⟨hvn, hrunt⟩
    · obtain ⟨an, rfl, hnew⟩ := repr_write (L := L) hrn m.store s
      obtain ⟨stor, hsave, hrep⟩ := save_repr hm.store hps ⟨_, hsv⟩ hnew
        (fun x hx => upd_other _ _ fun he => hx (he ▸ Occ.prim))
      have hs := (hm.store' hrep (upd_len hps an)).bindVal x (v := if op.isPre then vn else .int n)
        (w := if op.isPre then .val an else .val (m.store s)) (by cases op.isPre <;> simpa)
      rw [TyCtx.set_self hx] at hs
      refine .inl ⟨_, { m with
          store := upd m.store s an
          mem := upd m.mem x (if op.isPre then .val an else .val (m.store s)) }, ?_, ?_, rfl, hs⟩
      · simp only [hres, Except.ok_bind', bumpStore, State.findStorage_of_findLive hsv, hold,
          Value.asInt, hvn, hsave]; rfl
      · simp only at hrunt
        rw [run_append_ok hrunt]
        simp [run, Instr.step, Machine.next]
    · refine .inr ⟨?_, run_append_revert hrunt⟩
      simp only [hres, Except.ok_bind', bumpStore, State.findStorage_of_findLive hsv, hold,
        Value.asInt, hvn]; rfl
  · exact .inr ⟨by simp [hres] <;> rfl, run_append_revert hrunl⟩

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

/-- **`alice = bob;`** of a static type: the source's words loaded, the target
resolved, the words stored at the target's slots (solc copies member by
member; loading them all first is the same when the two do not overlap, and
right when they do). -/
theorem copy_sim {Δ : TyCtx} {τ : State} {m : Machine} {R : RefTy} (l : Loc C (.ref R))
    (q : SPath C (.ref R)) (hq : (Ty.ref R).mapFree = true) (hst : static (.ref R) = true)
    (hm : Sim C L Δ τ m) (hwq : wtSPath Δ false q = true) (hwl : wtLoc Δ false l = true) :
    StmtOut C L Δ ((Stmt.assign l (.copy q hq)).run τ)
      (run (compileStmt (Stmt.assign l (.copy q hq))) m) m := by
  simp only [Stmt.run, Src.value, compileStmt, List.append_assoc]
  rcases spath_sim q hm hwq with ⟨r, segs, s, sv, hres, hsv, hpq, hr, hrun⟩ | ⟨hres, hrun⟩
  · rw [run_append_ok hrun]
    simp only [Machine.push]
    rw [run_append_ok (loadLeaves_run m s _ m.stack)]
    generalize hvs : ((leaves (.ref R)).map fun o => m.store (s.add o)).reverse = vs
    rw [run_append_ok (m' := { m with stack := vs.map Word.val ++ m.stack }) rfl]
    rcases loc_sim l (hm.stack (vs.map Word.val ++ m.stack)) hwl with
      ⟨r', segs', d, old, hres', hold, hpl, hro, hrunl⟩ | ⟨hres', hrunl⟩
    · rw [run_append_ok hrunl]
      simp only [Machine.push]
      have hlen : (leaves (.ref R)).reverse.length = vs.length := by rw [← hvs]; simp
      rw [run_append_ok (storeLeaves_run { m with stack := vs.map Word.val ++ m.stack } d _ vs
        m.stack m.store hlen)]
      have hvs' : vs = (leaves (.ref R)).reverse.map fun o => m.store (s.add o) := by
        rw [← hvs, List.map_reverse]
      subst hvs'
      have hmove := move_repr (st' := storeAt m.store d (leaves (.ref R)).reverse
          ((leaves (.ref R)).reverse.map fun o => m.store (s.add o))) hr _ d
        (Nat.lt_succ_self _) hst fun o ho => storeAt_map _ (List.mem_reverse.2 ho)
      have hov := (overlay_repr hmove _ (Nat.lt_succ_self _) hst).2 old
      obtain ⟨stor, hsave, hrep⟩ := save_repr hm.store hpl ⟨_, hold⟩ hov
        (fun x hx => storeAt_other fun o ho hxo =>
          hx (hxo ▸ leavesF_occ _ _ d o (List.mem_reverse.1 ho)))
      refine .inl ⟨_, _, ?_, rfl, rfl, hm.store' hrep (storeAt_len hpl hst _)⟩
      simp [hres, State.findStorage_of_findLive hsv, hres',
        writeStorage_static hr hst (State.findStorage_of_findLive hold), hsave]
    · exact .inr ⟨by simp [hres, State.findStorage_of_findLive hsv, hres'],
        run_append_revert hrunl⟩
  · exact .inr ⟨by simp [hres], run_append_revert hrun⟩

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

/-- **`b.push(…)`**: the array's slot, the value, the length checked against
solc's `2^64` and grown, the element stored.  The bound on the arrays grows by
one, and the check never fires while it stays at most `2^64`. -/
theorem push_sim {Δ : TyCtx} {τ : State} {m : Machine} {E : Ty} (b : SPath C (.array E))
    (v : Option (Src C E)) (hd : (v.isSome || E.defaultOkS) = true)
    (hm : Sim C L Δ τ m) (hwp : wtPush Δ v b = true) (hL : L + 1 ≤ Lmax) :
    StmtOut C (L + 1) Δ ((Stmt.push b v hd).run τ) (run (compileStmt (Stmt.push b v hd)) m) m := by
  have hm' := hm.mono (Nat.le_succ L) hL
  cases v with
  | none =>
    simp only [wtPush, Bool.and_eq_true] at hwp
    obtain ⟨hE, hwb⟩ := hwp
    obtain ⟨p, rfl⟩ : ∃ p, E = .prim p := by cases E <;> simp_all [Ty.isPrimitive]
    simp only [Stmt.run, compileStmt, pushCode, List.append_assoc]
    rcases spath_sim b hm hwb with ⟨r, segs, s, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
    · have hr' := hr
      cases hr with
      | @array _ _ elems shadow hl hW hall =>
        rw [run_append_ok hrun]
        simp only [Machine.push]
        rw [run_append_ok (m' := { m with stack := .slot s :: .val 0 :: .slot s :: m.stack }) rfl,
          run_append_ok (pushSlotCode_run m _ 1 s (by omega))]
        obtain ⟨st', hst'⟩ : ∃ st', st' =
            upd (upd m.store s (m.store s + 1)) (.data s (m.store s * 1)) 0 := ⟨_, rfl⟩
        have hnew : ReprAt st' (L + 1) (.prim p) (.data s (elems.length * size (.prim p)))
            (defaultForTy (.prim p)) := zero_prim_repr (by rw [size_prim, ← hl, hst', upd_same])
        have hout : ∀ x, x ≠ s → x ≠ .data s (elems.length * 1) → st' x = m.store x :=
          fun x h1 h2 => by rw [hst', hl, upd_other _ _ h2, upd_other _ _ h1]
        have harr := push_repr (shadow' := (pushSlot (.prim p) shadow).2) hr'
          (st' := st') (by rw [hst', upd_other _ _ (Slot.ne_data _ _), upd_same, hl]) hnew
          (fun x hx hx' => hout x hx fun he => hx' (by rw [he, size_prim]; exact Occ.prim))
        obtain ⟨stor, hsave, hrep⟩ := save_repr hm'.store hp ⟨_, hsv⟩ harr
          (fun x hx => hout x (fun he => hx (he ▸ Occ.len))
            (fun he => hx (he ▸ Occ.elem elems.length (by rw [size_prim]; exact Occ.prim))))
        have hlen : ∀ x, LenSlot C x → m.store x ≤ st' x := push_len hp (m.store s)
          (by rw [hst', upd_other _ _ (Slot.ne_data _ _), upd_same])
          (fun x h1 h2 => by
            by_cases hx : x = .data s (m.store s * 1)
            · rw [hx]; exact OccAt.prim
            · exact absurd (by rw [hst', upd_other _ _ hx, upd_other _ _ h1]) h2)
        subst hst'
        refine .inl ⟨_, _, ?_, rfl, rfl, hm'.store' hrep hlen⟩
        simp [hres, pushAt, State.findStorage_of_findLive hsv, Src.pushVal, pushSlot_isPrim,
          hsave, Ty.isPrimitive]
        done
    · exact .inr ⟨by simp [hres], run_append_revert hrun⟩
  | some src =>
    cases src with
    | @val p e =>
      simp only [wtPush, Bool.and_eq_true] at hwp
      obtain ⟨hwb, hwe⟩ := hwp
      simp only [Stmt.run, compileStmt, pushCode, List.append_assoc]
      rcases spath_sim b hm hwb with ⟨r, segs, s, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
      · have hr' := hr
        cases hr with
        | @array _ _ elems shadow hl hW hall =>
          rw [run_append_ok hrun]
          rcases val_sim e (hm.push (.slot s)) hwe with ⟨ve, we, hve, hrve, hrune⟩ | ⟨hve, hrune⟩
          · rw [run_append_ok hrune]
            simp only [Machine.push]
            obtain ⟨a, rfl, hnew⟩ := repr_write (L := L + 1) hrve
              (upd m.store s (m.store s + 1)) (.data s (m.store s * 1))
            rw [run_append_ok (m' := { m with stack := .slot s :: .val a :: .slot s :: m.stack }) rfl,
              run_append_ok (pushSlotCode_run m _ 1 s (by omega))]
            obtain ⟨st', hst'⟩ : ∃ st', st' =
                upd (upd m.store s (m.store s + 1)) (.data s (m.store s * 1)) a := ⟨_, rfl⟩
            rw [← hst', hl, show elems.length * 1 = elems.length * size (.prim _) by simp] at hnew
            have hout : ∀ x, x ≠ s → x ≠ .data s (elems.length * 1) → st' x = m.store x :=
              fun x h1 h2 => by rw [hst', hl, upd_other _ _ h2, upd_other _ _ h1]
            have harr := push_repr (shadow' := (pushSlot (.prim p) shadow).2) hr'
              (st' := st') (by rw [hst', upd_other _ _ (Slot.ne_data _ _), upd_same, hl]) hnew
              (fun x hx hx' => hout x hx fun he => hx' (by rw [he, size_prim]; exact Occ.prim))
            obtain ⟨stor, hsave, hrep⟩ := save_repr hm'.store hp ⟨_, hsv⟩ harr
              (fun x hx => hout x (fun he => hx (he ▸ Occ.len))
                (fun he => hx (he ▸ Occ.elem elems.length (by rw [size_prim]; exact Occ.prim))))
            have hlen : ∀ x, LenSlot C x → m.store x ≤ st' x := push_len hp (m.store s)
              (by rw [hst', upd_other _ _ (Slot.ne_data _ _), upd_same])
              (fun x h1 h2 => by
                by_cases hx : x = .data s (m.store s * 1)
                · rw [hx]; exact OccAt.prim
                · exact absurd (by rw [hst', upd_other _ _ hx, upd_other _ _ h1]) h2)
            subst hst'
            refine .inl ⟨_, _, ?_, rfl, rfl, hm'.store' hrep hlen⟩
            simp [hres, pushAt, State.findStorage_of_findLive hsv, Src.pushVal, Src.value, hve,
              Value.toSVal_strip, hsave]
          · refine .inr ⟨?_, run_append_revert hrune⟩
            simp [hres, pushAt, State.findStorage_of_findLive hsv, Src.pushVal, Src.value, hve]
      · exact .inr ⟨by simp [hres], run_append_revert hrun⟩
    | @copy R q hq =>
      simp only [wtPush, Bool.and_eq_true] at hwp
      obtain ⟨⟨hst, hwb⟩, hwq⟩ := hwp
      simp only [Stmt.run, compileStmt, pushCode, List.append_assoc]
      rcases spath_sim b hm hwb with ⟨r, segs, s, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
      · have hr' := hr
        cases hr with
        | @array _ _ elems shadow hl hW hall =>
          rw [run_append_ok hrun]
          rcases spath_sim q (hm.push (.slot s)) hwq with
            ⟨r', segs', src, sv', hres', hsv', hpq, hrq, hrunq⟩ | ⟨hres', hrunq⟩
          · rw [run_append_ok hrunq]
            simp only [Machine.push]
            rw [run_append_ok (loadLeaves_run m src _ (.slot s :: m.stack))]
            generalize hvs : ((leaves (.ref R)).map fun o => m.store (src.add o)).reverse = vs
            have hlen : (leaves (.ref R)).reverse.length = vs.length := by rw [← hvs]; simp
            rw [run_append_ok (m' := { m with stack := .slot s :: (vs.map Word.val ++ .slot s :: m.stack) })
              (by simp [run, Instr.step, Machine.next, ← hlen]),
              run_append_ok (pushSlotCode_run m _ (size (.ref R)) s (by omega)),
              run_append_ok (storeLeaves_run m _ _ vs (.slot s :: m.stack) _ hlen)]
            have hvs' : vs = (leaves (.ref R)).reverse.map fun o => m.store (src.add o) := by
              rw [← hvs, List.map_reverse]
            subst hvs'
            obtain ⟨st', hst'⟩ : ∃ st', st' = storeAt (upd m.store s (m.store s + 1))
                (.data s (m.store s * size (.ref R))) (leaves (.ref R)).reverse
                ((leaves (.ref R)).reverse.map fun o => m.store (src.add o)) := ⟨_, rfl⟩
            have hmove := move_repr (st' := st') hrq _ (.data s (elems.length * size (.ref R)))
              (Nat.lt_succ_self _) hst fun o ho => by
                rw [hst', ← hl]; exact storeAt_map _ (List.mem_reverse.2 ho)
            have hnew := ((overlay_repr hmove _ (Nat.lt_succ_self _) hst).1).mono (Nat.le_succ L)
            have hout : ∀ x, x ≠ s → ¬ Occ (.ref R) (.data s (elems.length * size (.ref R))) x →
                st' x = m.store x := fun x h1 h2 => by
              rw [hst', hl, storeAt_other fun o ho hxo =>
                h2 (by rw [hxo]; exact leavesF_occ _ _ _ o (List.mem_reverse.1 ho)),
                upd_other _ _ h1]
            have harr := push_repr (shadow' := (pushSlot (.ref R) shadow).2) hr' (st' := st')
              (by rw [hst', storeAt_other fun o _ he => Slot.ne_data s _ he,
                upd_same, hl]) hnew hout
            obtain ⟨stor, hsave, hrep⟩ := save_repr hm'.store hp ⟨_, hsv⟩ harr
              (fun x hx => hout x (fun he => hx (he ▸ Occ.len))
                (fun he => hx (Occ.elem elems.length he)))
            have hlen : ∀ x, LenSlot C x → m.store x ≤ st' x := push_len hp (m.store s)
              (by rw [hst', storeAt_other fun o _ he => Slot.ne_data s _ he, upd_same])
              (fun x h1 h2 => by
                by_cases hx : ∃ o ∈ (leaves (.ref R)).reverse,
                    x = (Slot.data s (m.store s * size (.ref R))).add o
                · obtain ⟨o, ho, rfl⟩ := hx
                  exact leavesF_occAt _ _ _ o hst (List.mem_reverse.1 ho)
                · refine absurd ?_ h2
                  rw [hst', storeAt_other fun o ho he => hx ⟨o, ho, he⟩, upd_other _ _ h1])
            refine .inl ⟨_, { m with store := st' }, ?_, ?_, rfl, hm'.store' hrep hlen⟩
            · simp [hres, pushAt, State.findStorage_of_findLive hsv, Src.pushVal, Src.value, hres',
                State.findStorage_of_findLive hsv', hsave]
            · rw [hst']; rfl
          · exact .inr ⟨by simp [hres, pushAt, State.findStorage_of_findLive hsv, Src.pushVal,
              Src.value, hres'], run_append_revert hrunq⟩
      · exact .inr ⟨by simp [hres], run_append_revert hrun⟩


mutual

/-- **A statement's code does what the statement does**: both succeed, the
machine's stack as it was and the states related, or both revert.

Example: `alice.age = 10;` is `PUSH 10; PUSH @11; PUSH 2; ADD; SSTORE`, which
writes slot `13`; `require(total > 3);` with `total = 2` reverts in both. -/
theorem stmt_sim : ∀ (s : Stmt C) {L : Nat} {Δ Δ' : TyCtx} {τ : State} {m : Machine},
    Sim C L Δ τ m → wtStmt Δ s = some Δ' → L + pushes s ≤ Lmax →
      StmtOut C (L + pushes s) Δ' (s.run τ) (run (compileStmt s) m) m
  | .assign l (.val v), L, Δ, Δ', τ, m, hm, hw, hL => by
    simp only [wtStmt, Bool.and_eq_true, Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨⟨hwl, hwv⟩, rfl⟩ := hw
    simp only [Stmt.run, Src.value, compileStmt, List.append_assoc]
    rcases val_sim v hm hwv with ⟨vv, w, hvv, hrv, hrun⟩ | ⟨hvv, hrun⟩
    · rw [run_append_ok hrun]
      rcases loc_sim l (hm.push w) hwl with ⟨r, segs, s, sv, hres, hsv, hps, _, hrunl⟩ |
          ⟨hres, hrunl⟩
      · rw [run_append_ok hrunl]
        obtain ⟨a, rfl, hnew⟩ := repr_write (L := L) hrv m.store s
        obtain ⟨stor, hsave, hrep⟩ := save_repr hm.store hps ⟨sv, hsv⟩ hnew
          (fun x hx => upd_other _ _ fun he => hx (he ▸ Occ.prim))
        refine .inl ⟨_, { m with store := upd m.store s a }, ?_, rfl, rfl,
          hm.store' hrep (upd_len hps a)⟩
        simp [hvv, hres, hsave]
      · exact .inr ⟨by simp [hvv, hres], run_append_revert hrunl⟩
    · exact .inr ⟨by simp [hvv], run_append_revert hrun⟩
  | .rebind x (.path q), L, Δ, Δ', τ, m, hm, hw, hL => by
    simp only [wtStmt, bindAliasTy] at hw
    split at hw
    · cases hw; exact alias_sim q x hm (by assumption)
    · split at hw
      · cases hw; exact falias_sim q x hm (by assumption)
      · cases hw
  | .assignLocal x r, L, Δ, Δ', τ, m, hm, hw, hL => by
    simp only [wtStmt, Bool.and_eq_true, beq_iff_eq, Option.ite_none_right_eq_some,
      Option.some.injEq] at hw
    obtain ⟨⟨hx, hwr⟩, rfl⟩ := hw
    simp only [Stmt.run, compileStmt]
    rcases val_sim r hm hwr with ⟨v, w, hv, hrv, hrun⟩ | ⟨hv, hrun⟩
    · have hs := hm.bindVal x hrv
      rw [TyCtx.set_self hx] at hs
      refine .inl ⟨_, { m with mem := upd m.mem x w }, by simp [hv]; rfl, ?_, rfl, hs⟩
      rw [run_append_ok hrun]; rfl
    · exact .inr ⟨by rw [hv]; rfl, run_append_revert hrun⟩
  | .declLocal p x none, L, Δ, Δ', τ, m, hm, hw, hL => by
    simp only [wtStmt, Option.some.injEq] at hw
    subst hw
    exact .inl ⟨_, { m with mem := upd m.mem x (.val 0) }, rfl, rfl, rfl,
      hm.bindVal x (ReprV.default p)⟩
  | .declLocal p x (some e), L, Δ, Δ', τ, m, hm, hw, hL => by
    simp only [wtStmt, Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨hwe, rfl⟩ := hw
    simp only [Stmt.run, compileStmt]
    rcases val_sim e hm hwe with ⟨v, w, hv, hrv, hrun⟩ | ⟨hv, hrun⟩
    · refine .inl ⟨_, { m with mem := upd m.mem x w }, by simp [hv]; rfl, ?_, rfl,
        hm.bindVal x hrv⟩
      rw [run_append_ok hrun]; rfl
    · exact .inr ⟨by rw [hv]; rfl, run_append_revert hrun⟩
  | .declStorage R x none, L, Δ, Δ', τ, m, hm, hw, hL => by
    simp only [wtStmt, Option.some.injEq] at hw
    subst hw
    refine .inl ⟨τ, m, rfl, rfl, rfl, hm.weaken fun y t hy => ?_⟩
    by_cases hyx : y = x
    · subst hyx; simp [TyCtx.set] at hy
    · simpa [TyCtx.set, upd_other _ _ hyx] using hy
  | .declStorage R x (some (.path q)), L, Δ, Δ', τ, m, hm, hw, hL => by
    simp only [wtStmt, bindAliasTy] at hw
    split at hw
    · cases hw; exact alias_sim q x hm (by assumption)
    · split at hw
      · cases hw; exact falias_sim q x hm (by assumption)
      · cases hw
  | @Stmt.opAssign _ p op hop _ (.local x) r, L, Δ, Δ', τ, m, hm, hw, hL => by
    simp only [wtStmt, wtOpLoc, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
      Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨⟨⟨hp, hx⟩, hwr⟩, rfl⟩ := hw
    exact opLocal_sim hp hop x r hm hx hwr
  | @Stmt.opAssign _ p op hop _ (.root rt h) r, L, Δ, Δ', τ, m, hm, hw, hL => by
    simp only [wtStmt, wtOpLoc, opLocToLoc, Bool.and_eq_true, bne_iff_ne, ne_eq,
      Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨⟨⟨hp, hwl⟩, hwr⟩, rfl⟩ := hw
    exact opStore_sim hp hop rfl r hm hwl hwr
  | @Stmt.opAssign _ p op hop _ (.field b f h) r, L, Δ, Δ', τ, m, hm, hw, hL => by
    simp only [wtStmt, wtOpLoc, opLocToLoc, Bool.and_eq_true, bne_iff_ne, ne_eq,
      Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨⟨⟨hp, hwl⟩, hwr⟩, rfl⟩ := hw
    exact opStore_sim hp hop rfl r hm hwl hwr
  | @Stmt.opAssign _ p op hop _ (.index it b i) r, L, Δ, Δ', τ, m, hm, hw, hL => by
    simp only [wtStmt, wtOpLoc, opLocToLoc, Bool.and_eq_true, bne_iff_ne, ne_eq,
      Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨⟨⟨hp, hwl⟩, hwr⟩, rfl⟩ := hw
    exact opStore_sim hp hop rfl r hm hwl hwr
  | .opAssign _ _ _ (.mfield ..) _, _, _, _, _, _, _, hw, _ => by
    simp [wtStmt, wtOpLoc, opLocToLoc] at hw
  | .opAssign _ _ _ (.mindex ..) _, _, _, _, _, _, _, hw, _ => by
    simp [wtStmt, wtOpLoc, opLocToLoc] at hw
  | .pop (E := E) b, L, Δ, Δ', τ, m, hm, hw, hL => by
    simp only [wtStmt, Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨hwb, rfl⟩ := hw
    simp only [Stmt.run, compileStmt]
    rcases spath_sim b hm hwb with ⟨r, segs, s, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
    · have hr' := hr
      cases hr with
      | array hl hW hall =>
        rename_i elems shadow
        rw [run_append_ok hrun]
        have hpc := popCode_run m m.stack s
          (by rw [hl]; have := hm.bound; have := Lmax_lt_W; omega)
        simp only [Machine.push] at hpc ⊢
        rw [hpc, hl]
        by_cases h0 : elems.length = 0
        · rw [if_pos h0]
          have : elems = [] := List.eq_nil_of_length_eq_zero h0
          subst this
          exact .inr ⟨by simp [hres, popAt, (State.findStorage_of_findLive hsv)], rfl⟩
        · rw [if_neg h0]
          obtain ⟨last, restRev, hrev⟩ : ∃ last restRev, elems.reverse = last :: restRev := by
            cases h : elems.reverse with
            | nil => simp at h; exact absurd (by simp [h]) h0
            | cons last restRev => exact ⟨last, restRev, rfl⟩
          have hnew := pop_repr (if E.isMapping then last else last.defaultOf) hr' hrev
          obtain ⟨stor, hsave, hrep⟩ := save_repr hm.store hp ⟨_, hsv⟩ hnew
            (fun x hx => upd_other _ _ fun he => hx (he ▸ Occ.len))
          refine .inl ⟨_, _, ?_, rfl, rfl, hm.storeDrop hrep⟩
          simp [hres, popAt, (State.findStorage_of_findLive hsv), hrev, hsave]
    · exact .inr ⟨by simp [hres], run_append_revert hrun⟩
  | .transfer r a, L, Δ, Δ', τ, m, hm, hw, hL => by
    simp only [wtStmt, Bool.and_eq_true, Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨⟨hwr, hwa⟩, rfl⟩ := hw
    simp only [Stmt.run, compileStmt, List.append_assoc]
    rcases val_sim r hm hwr with ⟨vr, wr, hvr, hrv, hrunr⟩ | ⟨hvr, hrunr⟩
    · obtain ⟨x, hx, rfl, rfl⟩ := hrv.uint_inv
      rw [run_append_ok hrunr]
      rcases val_sim a (hm.push _) hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
      · obtain ⟨y, hy, rfl, rfl⟩ := hra.uint_inv
        rw [run_append_ok hruna]
        by_cases hb : m.balance < y
        · refine .inr ⟨?_, ?_⟩
          · simp only [hvr, hva, Value.asInt, transferAt, hm.balance, Except.ok_bind']
            rw [if_neg (by omega), if_pos (by exact_mod_cast hb)]
          · simp [run, Instr.step, Machine.next, Machine.push, hb, assertTop]
        · have hsrc : transferAt τ x y = .ok { τ.setNet x (τ.getNet x - y) with
              selfBalance := τ.selfBalance - y } := by
            unfold transferAt
            rw [if_neg (by omega), if_neg (by rw [hm.balance]; exact_mod_cast hb)]
          refine .inl ⟨_, { m with balance := m.balance - y, net := upd m.net x (m.net x - y) },
            by simp only [hvr, hva, Value.asInt, Except.ok_bind']; exact hsrc, ?_, rfl, ?_⟩
          · simp [run, Instr.step, Machine.push, hb, assertTop]
          · refine ⟨hm.store, hm.vals, hm.aliases, ?_, fun a' ha' => ?_, hm.bound, hm.fragile, ?_⟩
            · show τ.selfBalance - ↑y = ↑(m.balance - y)
              rw [hm.balance]; omega
            · show (lookupBy (↑a') (setBy (↑x) (τ.getNet ↑x - ↑y) τ.net)).getD 0 =
                upd m.net x (m.net x - ↑y) a'
              by_cases hax : a' = x
              · subst hax
                rw [lookupBy_setBy_self, upd_same, ← hm.net a' ha']; rfl
              · have : (a' : Int) ≠ x := by omega
                rw [lookupBy_setBy_ne this, upd_other _ _ hax]
                exact hm.net a' ha'
            · obtain ⟨h1, h2, h3, w1, w2, w3, w4⟩ := hm.env
              exact ⟨h1, h2, h3, w1, w2, w3, Nat.lt_of_le_of_lt (Nat.sub_le _ _) w4⟩
      · exact .inr ⟨by simp [hvr, hva, Value.asInt], run_append_revert hruna⟩
    · exact .inr ⟨by simp [hvr], run_append_revert hrunr⟩
  | @Stmt.delete _ T l, L, Δ, Δ', τ, m, hm, hw, hL => by
    simp only [wtStmt, Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨hwl, rfl⟩ := hw
    simp only [Stmt.run, compileStmt, List.append_assoc]
    rcases loc_sim l hm hwl with ⟨r, segs, s, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩
    · rw [run_append_ok hrun]
      simp only [Machine.push]
      rw [run_append_ok (zeroCode_run m m.stack s (leaves T))]
      have hnew := zero_repr hr (tyRank T + 1) (Nat.lt_succ_self _)
        (st' := zeroAt m.store s (leaves T)) (fun o ho => zeroAt_zero ⟨o, ho, rfl⟩)
        (fun x _ hx => zeroAt_other hx)
      obtain ⟨stor, hsave, hrep⟩ := save_repr hm.store hp ⟨_, hsv⟩ hnew
        (fun x hx => zeroAt_other fun o ho hxo => hx (hxo ▸ leavesF_occ _ T s o ho))
      refine .inl ⟨_, { m with store := zeroAt m.store s (leaves T) }, ?_, rfl, rfl,
        hm.storeDrop hrep⟩
      simp [hres, (State.findStorage_of_findLive hsv), hsave]
    · exact .inr ⟨by simp [hres], run_append_revert hrun⟩
  | .ite c t e, L, Δ, Δ', τ, m, hm, hw, hL => by
    have hL' : L + (pushesP t + pushesP e) ≤ Lmax := hL
    have iht : ∀ {Δ₁ : TyCtx} {m : Machine}, Sim C L Δ τ m → wtProg Δ t = some Δ₁ →
        StmtOut C (L + (pushesP t + pushesP e)) Δ₁ (Prog.run τ t) (run (compileProg t) m) m :=
      fun hm hw => (prog_sim t hm hw (by omega)).mono (by omega) hL'
    have ihe : ∀ {Δ₂ : TyCtx} {m : Machine}, Sim C L Δ τ m → wtProg Δ e = some Δ₂ →
        StmtOut C (L + (pushesP t + pushesP e)) Δ₂ (Prog.run τ e) (run (compileProg e) m) m :=
      fun hm hw => (prog_sim e hm hw (by omega)).mono (by omega) hL'
    simp only [wtStmt] at hw
    split at hw
    · rename_i hwc
      split at hw
      · rename_i Δ₁ Δ₂ ht he
        simp only [Option.some.injEq] at hw
        subst hw
        have wk₁ : ∀ x t, Δ₁.meet Δ₂ x = some t → Δ₁ x = some t := fun x t h => by
          simp only [TyCtx.meet] at h; split at h <;> simp_all
        have wk₂ : ∀ x t, Δ₁.meet Δ₂ x = some t → Δ₂ x = some t := fun x t h => by
          simp only [TyCtx.meet] at h; split at h <;> simp_all
        simp only [Stmt.run, compileStmt, List.append_assoc]
        rcases val_sim c hm hwc with ⟨vc, wc, hvc, hrc, hrunc⟩ | ⟨hvc, hrunc⟩
        · obtain ⟨x, rfl, rfl⟩ := hrc.bool_inv
          rw [run_append_ok hrunc, hvc]
          cases x
          · rw [run_append_skip (m' := m) (k := (compileProg t).length + 1) rfl,
              exec_skip_append,
              show exec ([Instr.jump (compileProg e).length] ++ compileProg e) 1 m =
                run (compileProg e) m from rfl]
            simp only [Except.ok_bind']
            rcases ihe hm he with ⟨τ', m', hτ', hrun', hst', hm'⟩ | ⟨hτ', hrun'⟩
            · exact .inl ⟨τ', m', hτ', hrun', hst', hm'.weaken wk₂⟩
            · exact .inr ⟨hτ', hrun'⟩
          · rw [run_append_skip (m' := m) (k := 0) rfl]
            rcases iht hm ht with ⟨τ', m', hτ', hrun', hst', hm'⟩ | ⟨hτ', hrun'⟩
            · refine .inl ⟨τ', m', hτ', ?_, hst', hm'.weaken wk₁⟩
              change run _ m = _
              rw [run_append_skip (k := 0) hrun']
              exact exec_length (.jump (compileProg e).length :: compileProg e) m' |>.trans rfl
            · exact .inr ⟨hτ', run_append_revert hrun'⟩
        · exact .inr ⟨by simp [hvc], run_append_revert hrunc⟩
      · cases hw
    · cases hw
  | .require c, L, Δ, Δ', τ, m, hm, hw, hL => by
    simp only [wtStmt, Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨hwc, rfl⟩ := hw
    simp only [Stmt.run, compileStmt]
    rcases val_sim c hm hwc with ⟨vc, wc, hvc, hrc, hrunc⟩ | ⟨hvc, hrunc⟩
    · obtain ⟨x, rfl, rfl⟩ := hrc.bool_inv
      cases x
      · exact .inr ⟨by simp [hvc, guardOk], by rw [run_append_skip hrunc]; rfl⟩
      · exact .inl ⟨τ, m, by simp [hvc, guardOk]; rfl, by rw [run_append_skip hrunc]; rfl, rfl,
          hm⟩
    · exact .inr ⟨by simp [hvc], run_append_revert hrunc⟩
  | .assert c, L, Δ, Δ', τ, m, hm, hw, hL => by
    simp only [wtStmt, Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨hwc, rfl⟩ := hw
    simp only [Stmt.run, compileStmt]
    rcases val_sim c hm hwc with ⟨vc, wc, hvc, hrc, hrunc⟩ | ⟨hvc, hrunc⟩
    · obtain ⟨x, rfl, rfl⟩ := hrc.bool_inv
      cases x
      · exact .inr ⟨by simp [hvc, guardOk], by rw [run_append_skip hrunc]; rfl⟩
      · exact .inl ⟨τ, m, by simp [hvc, guardOk]; rfl, by rw [run_append_skip hrunc]; rfl, rfl,
          hm⟩
    · exact .inr ⟨by simp [hvc], run_append_revert hrunc⟩
  | .revert, L, Δ, Δ', τ, m, hm, hw, hL => .inr ⟨rfl, rfl⟩
  | .call _ args _ ret body, L, Δ, Δ', τ, m, hm, hw, hL => by
    have ihb : ∀ {Δ₂ Δ₃ : TyCtx} {τ₂ : State} {m : Machine}, Sim C L Δ₂ τ₂ m →
        wtProg Δ₂ body = some Δ₃ →
          StmtOut C (L + pushesP body) Δ₃ (Prog.run τ₂ body) (run (compileProg body) m) m :=
      fun hm hw => prog_sim body hm hw hL
    simp only [wtStmt] at hw
    split at hw
    · rename_i Δ₁ hwa
      split at hw
      · rename_i Δ₂ hwe
        split at hw
        · rename_i Δ₃ hwb
          obtain ⟨hwl, hΔ⟩ := Option.ite_none_right_eq_some.1 hw
          cases hΔ
          simp only [Stmt.run, compileStmt, List.append_assoc]
          rcases args_sim args hm hwa with ⟨τ₁, m₁, hτ₁, hrun₁, hst₁, hm₁⟩ | ⟨hτ₁, hrun₁⟩
          · rw [run_append_ok hrun₁, hτ₁]
            simp only [Except.ok_bind']
            -- the return variable declared
            obtain ⟨m₂, hrun₂, hst₂, hm₂⟩ : ∃ m₂, run (retEnterCode ret) m₁ = .ok m₂ 0 ∧
                m₂.stack = m₁.stack ∧ Sim C L Δ₂ (ret.enter τ₁) m₂ := by
              cases ret with
              | none =>
                simp only [wtRetEnter, Option.some.injEq] at hwe
                subst hwe
                exact ⟨m₁, rfl, rfl, hm₁⟩
              | val p r res =>
                simp only [wtRetEnter, Option.some.injEq] at hwe
                subst hwe
                exact ⟨{ m₁ with mem := upd m₁.mem r (.val 0) }, rfl, rfl,
                  hm₁.bindVal r (ReprV.default p)⟩
            rw [run_append_ok hrun₂]
            rcases ihb hm₂ hwb with ⟨τ₃, m₃, hτ₃, hrun₃, hst₃, hm₃⟩ | ⟨hτ₃, hrun₃⟩
            · rw [run_append_ok hrun₃, hτ₃]
              simp only [Except.ok_bind']
              cases ret with
              | none =>
                exact .inl ⟨τ₃, m₃, rfl, rfl, hst₃.trans (hst₂.trans hst₁), hm₃⟩
              | val p r res =>
                cases res with
                | none => exact .inl ⟨τ₃, m₃, rfl, rfl, hst₃.trans (hst₂.trans hst₁), hm₃⟩
                | some y =>
                  simp only [wtRetLeave, Bool.and_eq_true, beq_iff_eq] at hwl
                  obtain ⟨v, henv, hv⟩ := hm₃.vals r p hwl.1
                  have hs := hm₃.bindVal y hv
                  rw [TyCtx.set_self hwl.2] at hs
                  refine .inl ⟨_, { m₃ with mem := upd m₃.mem y (m₃.mem r) }, ?_, rfl,
                    hst₃.trans (hst₂.trans hst₁), hs⟩
                  simp [CallRet.leave, Simple.eval, State.getEnv, henv]; rfl
            · exact .inr ⟨by simp [hτ₃], run_append_revert hrun₃⟩
          · exact .inr ⟨by simp [hτ₁], run_append_revert hrun₁⟩
        · cases hw
      · cases hw
    · cases hw
  | @Stmt.assign _ (.ref R) l (.copy q hq), L, Δ, Δ', τ, m, hm, hw, hL => by
    simp only [wtStmt, Bool.and_eq_true, Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨⟨⟨hst, hwq⟩, hwl⟩, rfl⟩ := hw
    exact copy_sim l q hq hst hm hwq hwl
  | .rebind _ (.push ..), _, _, _, _, _, _, hw, _ => by simp [wtStmt] at hw
  | .declStorage _ _ (some (.push ..)), _, _, _, _, _, _, hw, _ => by simp [wtStmt] at hw
  | @Stmt.incDec _ p op _ (.local x), L, Δ, Δ', τ, m, hm, hw, hL => by
    simp only [wtStmt, wtOpLoc, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
      Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨⟨hp, hx⟩, rfl⟩ := hw
    exact bumpLocal_sim hp op x hm hx
  | @Stmt.incDec _ p op _ (.root rt h), L, Δ, Δ', τ, m, hm, hw, hL => by
    simp only [wtStmt, wtOpLoc, opLocToLoc, Bool.and_eq_true, bne_iff_ne, ne_eq,
      Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨⟨hp, hwl⟩, rfl⟩ := hw
    exact bumpStore_sim hp op rfl hm hwl
  | @Stmt.incDec _ p op _ (.field b f h), L, Δ, Δ', τ, m, hm, hw, hL => by
    simp only [wtStmt, wtOpLoc, opLocToLoc, Bool.and_eq_true, bne_iff_ne, ne_eq,
      Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨⟨hp, hwl⟩, rfl⟩ := hw
    exact bumpStore_sim hp op rfl hm hwl
  | @Stmt.incDec _ p op _ (.index it b i), L, Δ, Δ', τ, m, hm, hw, hL => by
    simp only [wtStmt, wtOpLoc, opLocToLoc, Bool.and_eq_true, bne_iff_ne, ne_eq,
      Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨⟨hp, hwl⟩, rfl⟩ := hw
    exact bumpStore_sim hp op rfl hm hwl
  | .incDec _ _ (.mfield ..), _, _, _, _, _, _, hw, _ => by simp [wtStmt, wtOpLoc, opLocToLoc] at hw
  | .incDec _ _ (.mindex ..), _, _, _, _, _, _, hw, _ => by simp [wtStmt, wtOpLoc, opLocToLoc] at hw
  | @Stmt.assignIncDec _ p x op _ (.local y) _, L, Δ, Δ', τ, m, hm, hw, hL => by
    simp only [wtStmt, wtOpLoc, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
      Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨⟨⟨hp, hx⟩, hy⟩, rfl⟩ := hw
    exact assignBumpLocal_sim hp op x y hm hx hy
  | @Stmt.assignIncDec _ p x op _ (.root rt h) _, L, Δ, Δ', τ, m, hm, hw, hL => by
    simp only [wtStmt, wtOpLoc, opLocToLoc, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
      Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨⟨⟨hp, hx⟩, hwl⟩, rfl⟩ := hw
    exact assignBumpStore_sim hp op x rfl hm hx hwl
  | @Stmt.assignIncDec _ p x op _ (.field b f h) _, L, Δ, Δ', τ, m, hm, hw, hL => by
    simp only [wtStmt, wtOpLoc, opLocToLoc, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
      Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨⟨⟨hp, hx⟩, hwl⟩, rfl⟩ := hw
    exact assignBumpStore_sim hp op x rfl hm hx hwl
  | @Stmt.assignIncDec _ p x op _ (.index it b i) _, L, Δ, Δ', τ, m, hm, hw, hL => by
    simp only [wtStmt, wtOpLoc, opLocToLoc, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
      Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨⟨⟨hp, hx⟩, hwl⟩, rfl⟩ := hw
    exact assignBumpStore_sim hp op x rfl hm hx hwl
  | .assignIncDec _ _ _ (.mfield ..) _, _, _, _, _, _, _, hw, _ => by
    simp [wtStmt, wtOpLoc, opLocToLoc] at hw
  | .assignIncDec _ _ _ (.mindex ..) _, _, _, _, _, _, _, hw, _ => by
    simp [wtStmt, wtOpLoc, opLocToLoc] at hw
  | .push b v hd, L, Δ, Δ', τ, m, hm, hw, hL => by
    simp only [wtStmt, Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨hwp, rfl⟩ := hw
    exact push_sim b v hd hm hwp hL
  | .declMem .., _, _, _, _, _, _, hw, _ => by simp [wtStmt] at hw
  | .rebindMem .., _, _, _, _, _, _, hw, _ => by simp [wtStmt] at hw
  | .assignFromMem .., _, _, _, _, _, _, hw, _ => by simp [wtStmt] at hw
  | .assignMem .., _, _, _, _, _, _, hw, _ => by simp [wtStmt] at hw

/-- A block's code does what the block does. -/
theorem prog_sim : ∀ (P : List (Stmt C)) {L : Nat} {Δ Δ' : TyCtx} {τ : State} {m : Machine},
    Sim C L Δ τ m → wtProg Δ P = some Δ' → L + pushesP P ≤ Lmax →
      StmtOut C (L + pushesP P) Δ' (Prog.run τ P) (run (compileProg P) m) m
  | [], L, Δ, Δ', τ, m, hm, hw, hL => by
    simp only [wtProg, Option.some.injEq] at hw
    subst hw
    exact .inl ⟨τ, m, rfl, rfl, rfl, hm⟩
  | s :: P, L, Δ, Δ', τ, m, hm, hw, hL => by
    have hL' : L + (pushes s + pushesP P) ≤ Lmax := hL
    have ihs : ∀ {Δ₁ : TyCtx} {m : Machine}, Sim C L Δ τ m → wtStmt Δ s = some Δ₁ →
        StmtOut C (L + pushes s) Δ₁ (s.run τ) (run (compileStmt s) m) m :=
      fun hm hw => stmt_sim s hm hw (by omega)
    have ihP : ∀ {Δ₁ Δ₂ : TyCtx} {τ₁ : State} {m : Machine}, Sim C (L + pushes s) Δ₁ τ₁ m →
        wtProg Δ₁ P = some Δ₂ →
          StmtOut C (L + pushes s + pushesP P) Δ₂ (Prog.run τ₁ P) (run (compileProg P) m) m :=
      fun hm hw => prog_sim P hm hw (by omega)
    simp only [wtProg] at hw
    split at hw
    · rename_i Δ₁ hs
      simp only [Prog.run, compileProg, pushesP, ← Nat.add_assoc]
      rcases ihs hm hs with ⟨τ₁, m₁, hτ₁, hrun₁, hst₁, hm₁⟩ | ⟨hτ₁, hrun₁⟩
      · rw [run_append_ok hrun₁, hτ₁]
        rcases ihP hm₁ hw with ⟨τ₂, m₂, hτ₂, hrun₂, hst₂, hm₂⟩ | ⟨hτ₂, hrun₂⟩
        · exact .inl ⟨τ₂, m₂, by simpa using hτ₂, hrun₂, hst₂.trans hst₁, hm₂⟩
        · exact .inr ⟨by simpa using hτ₂, hrun₂⟩
      · exact .inr ⟨by simp [hτ₁], run_append_revert hrun₁⟩
    · cases hw

end

/-! ## The headline -/

/-- **The compiler is correct.**  For a program of the fragment and a machine
representing the state it starts in, the interpreter and the compiled code
agree: both succeed — the machine's stack as it was, its storage, locals,
funds and ledger representing the interpreter's final state — or both revert.

Example: from a state where `total = 3`,
```solidity
total += 1; if (total > 3) { delete alice; } else { revert(); }
```
runs in the interpreter to `total = 4` and a default `alice`, and on the
machine to slot `0` holding `4` and slots `11`–`13` holding `0`. -/
theorem compile_correct {P : Prog C} {Γ Γ' : TyCtx} {σ : State} {m : Machine}
    (hP : wtProg Γ P = some Γ') (hm : Sim C L Γ σ m) (hL : L + pushesP P ≤ Lmax) :
    (∃ σ' m', Prog.run σ P = .ok σ' ∧ run (compileProg P) m = .ok m' 0 ∧ m'.stack = m.stack ∧
      Sim C (L + pushesP P) Γ' σ' m') ∨
    (Prog.run σ P = .error .revert ∧ run (compileProg P) m = .revert) :=
  prog_sim P hm hP hL

/-- The interpreter is never stuck on the fragment: `wtProg` is a type system
for it.

Example: `x = 1;` with `x` never declared is stuck in the interpreter, and
`wtProg` rejects it (`x` is not in the context). -/
theorem not_stuck {P : Prog C} {Γ Γ' : TyCtx} {σ : State} {m : Machine}
    (hP : wtProg Γ P = some Γ') (hm : Sim C L Γ σ m) (hL : L + pushesP P ≤ Lmax) :
    Prog.run σ P ≠ .error .stuck := by
  rcases compile_correct hP hm hL with ⟨_, _, h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nofun

/-- A fresh contract: its storage at every type's default, nothing bound,
nothing sent, `balance` in funds. -/
def State.fresh (C : Contract) (balance : Nat) : State :=
  { storage := C.initStorage, selfBalance := balance }

/-- A fresh machine represents a fresh contract: every slot `0`, the funds
a word. -/
theorem Sim.init (C : Contract) (balance : Nat) (hb : balance < W) :
    Sim C 1 (fun _ => none) (State.fresh C balance) (Machine.init balance) :=
  ⟨initStorage_repr C Nat.one_pos, fun _ _ h => (by cases h), fun _ _ h => (by cases h), rfl,
    fun _ _ => by simp [State.getNet, State.fresh, lookupBy, Machine.init],
    by unfold Lmax; decide, fun _ _ h => (by cases h),
    ⟨rfl, rfl, rfl, W_pos, W_pos, W_pos, hb⟩⟩

/-- **The EVM agrees with the interpreter's storage.**  From a fresh contract,
a program of the fragment either reverts in both, or runs in both, and then
every `uint` path the interpreter reads with its indices in bounds
(`findLive`, as a program's read checks them), the machine holds at its slot.

Example: `alice.age = 10;` leaves `10` at slot `13` of `StandardExample`
(`Evm/Examples.lean` derives it from this theorem). -/
theorem compile_storage {P : Prog C} {Γ' : TyCtx} (hP : wtProg (fun _ => none) P = some Γ')
    (hL : pushesP P < Lmax) (balance : Nat) (hb : balance < W) :
    (∃ σ' m', Prog.run (State.fresh C balance) P = .ok σ' ∧
      run (compileProg P) (Machine.init balance) = .ok m' 0 ∧
      ∀ r segs s n, PathSlot C false r segs (.prim .uint) s →
        σ'.findLive r segs = .ok (.prim (.int n)) → m'.store s = n.toNat) ∨
    (Prog.run (State.fresh C balance) P = .error .revert ∧
      run (compileProg P) (Machine.init balance) = .revert) := by
  rcases compile_correct hP (Sim.init C balance hb) (by omega) with ⟨σ', m', h1, h2, _, hm⟩ | h
  · refine .inl ⟨σ', m', h1, h2, fun r segs s n hp hf => ?_⟩
    rcases find_repr hm.store hp with ⟨sv, hsv, hr⟩ | ⟨_, hsv⟩
    · rw [hf] at hsv; cases hsv
      cases hr with
      | uint _ _ h => exact h
    · rw [hf] at hsv; cases hsv
  · exact .inr h

end Evm
end Solidity
