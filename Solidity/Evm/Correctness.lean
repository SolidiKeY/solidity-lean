import Solidity.Evm.Repr

/-!
# The compiler is correct

`Sim C Γ σ m` says the machine `m` *represents* the interpreter state `σ`
(mini-solkey's `Sim`, with control flow, reverts and the ledger added):

* the storage, by `ReprStore` (`Evm/Repr.lean`);
* a local `Γ` types as a value, by its memory cell (`ReprV`);
* a storage alias, by its memory cell holding the slot of the path it is bound
  to — a path that indexes no array, so the slot stays the path's;
* the contract's funds and the `net` ledger, by the machine's.

**The headline** (`compile_correct`): for a program of the fragment
(`wtProg Γ P = some Γ'`) and a machine representing the state it starts in,
the interpreter and the compiled code *agree*: either both succeed, the machine's
stack as it was and the machine representing the interpreter's final state, or
both revert.  The interpreter is never stuck on the fragment.
`compile_storage` states it from a fresh contract, for the storage alone: every
typed `uint` path reads at its slot what the interpreter reads there.

The proof is a forward simulation by structural recursion on the syntax, one
lemma per syntactic class, each a *dichotomy*: `ValOut` (a value pushed, or
both revert), `LocOut` (a slot pushed, or both revert, possibly only at the
read), `StmtOut`.  Being total, they make the order of evaluation irrelevant
where the two disagree on it: the interpreter evaluates an `op=`'s right-hand
side before its target, the compiled code the target first, and they revert
together either way.

The machine lemmas at the top compute the guard sequences of `Compile.lean`:
`add_tail`/`sub_tail`/`mul_tail` are solc's overflow checks, exact on words
below `2^256` (`mul_ok_iff` is the arithmetic fact behind the `*` check).
-/

namespace Solidity
namespace Evm

open Semantics SemanticsProperties

/-! ## Running code in pieces -/

/-- Running two pieces of code is running the second on what the first leaves: `total = 3;`
then `age = 4;`. -/
theorem run_append_ok {c₁ c₂ : List Instr} {m m' : Machine} (h : run c₁ m = .ok m' 0) :
    run (c₁ ++ c₂) m = run c₂ m' := by
  simp only [run] at h ⊢; rw [exec_append, h]; rfl

/-- A revert in the first piece of code reverts the whole: `require(false); total = 1;` never
writes. -/
theorem run_append_revert {c₁ c₂ : List Instr} {m : Machine} (h : run c₁ m = .revert) :
    run (c₁ ++ c₂) m = .revert := by
  simp only [run] at h ⊢; rw [exec_append, h]; rfl

/-- The empty code does nothing: `if (c) { } else { }`'s branches. -/
@[simp] theorem run_nil (m : Machine) : run [] m = .ok m 0 := rfl

/-- A jump pending at the end of the first piece skips into the second: `if`'s `JUMPI` over the
`then` branch. -/
theorem run_append_skip {c₁ c₂ : List Instr} {m m' : Machine} {k : Nat} (h : run c₁ m = .ok m' k) :
    run (c₁ ++ c₂) m = exec c₂ k m' := by
  simp only [run] at h ⊢; rw [exec_append, h]; rfl

/-- Skipping a whole piece of code leaves the machine as it was: the `JUMP` over an `else`
branch. -/
theorem exec_length (c : List Instr) (m : Machine) : exec c c.length m = .ok m 0 :=
  exec_skip c 0 m

/-- Skipping past a first piece lands in the second: the `JUMPI` over the `then` branch lands in the
`else`. -/
theorem exec_skip_append (c₁ c₂ : List Instr) (k : Nat) (m : Machine) :
    exec (c₁ ++ c₂) (c₁.length + k) m = exec c₂ k m := by
  rw [exec_append, exec_skip]; rfl

/-! ## The guard sequences -/

/-- A sum below `2^256` does not wrap: `3 + 4` is `7`. -/
theorem mod_W_of_lt {x : Nat} (h : x < W) : x % W = x := Nat.mod_eq_of_lt h

/-- A sum of two words that wraps loses exactly `2^256`: `(2^256 - 1) + 1` wraps to `0`. -/
theorem mod_W_of_ge {x : Nat} (h₁ : W ≤ x) (h₂ : x < W + W) : x % W = x - W := by
  rw [Nat.mod_eq_sub_mod h₁, Nat.mod_eq_of_lt (by omega)]

/-- A comparison's word is `0` exactly when it is false: `3 < 2` pushes `0`. -/
@[simp] theorem bword_eq_zero (b : Bool) : bword b = 0 ↔ b = false := by cases b <;> decide

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
    run (binTail .add) { m with stack := .val b :: .val a :: st } =
      if a + b < W then .ok { m with stack := .val (a + b) :: st } 0 else .revert := by
  simp [run, binTail, assertTop, Instr.step, Machine.next]
  by_cases h : a + b < W
  · rw [mod_W_of_lt h]; simp [h, show ¬ a + b < a by omega, Instr.step, Machine.next]
  · rw [mod_W_of_ge (by omega) (by omega)]
    simp [h, Instr.step, show a + b - W < a by omega]

/-- `a - b` with solc's underflow check: revert when `b > a`.  `3 - 4`
reverts, `4 - 3` is `1`. -/
theorem sub_tail (m : Machine) (st : List Word) {a b : Nat} (ha : a < W) (hb : b < W) :
    run (binTail .sub) { m with stack := .val b :: .val a :: st } =
      if b ≤ a then .ok { m with stack := .val (a - b) :: st } 0 else .revert := by
  simp [run, binTail, assertTop, Instr.step, Machine.next]
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
    run (binTail .mul) { m with stack := .val b :: .val a :: st } =
      if a * b < W then .ok { m with stack := .val (a * b) :: st } 0 else .revert := by
  simp [run, binTail, assertTop, Instr.step, Machine.next]
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
    run (binTail .div) { m with stack := .val b :: .val a :: st } =
      if b = 0 then .revert else .ok { m with stack := .val (a / b) :: st } 0 := by
  by_cases h : b = 0
  · subst h; rfl
  · simp [run, binTail, assertTop, Instr.step, Machine.next, h]

/-- `a % b`, reverting on `b = 0`. -/
theorem mod_tail (m : Machine) (st : List Word) (a b : Nat) :
    run (binTail .mod) { m with stack := .val b :: .val a :: st } =
      if b = 0 then .revert else .ok { m with stack := .val (a % b) :: st } 0 := by
  by_cases h : b = 0
  · subst h; rfl
  · simp [run, binTail, assertTop, Instr.step, Machine.next, h]

/-- A comparison or an equality: one or two instructions and no guard. -/
theorem cmp_tail (m : Machine) (st : List Word) (a b : Nat) :
    run (binTail .lt) { m with stack := .val b :: .val a :: st } =
        .ok { m with stack := .val (bword (decide (a < b))) :: st } 0 ∧
    run (binTail .gt) { m with stack := .val b :: .val a :: st } =
        .ok { m with stack := .val (bword (decide (b < a))) :: st } 0 ∧
    run (binTail .le) { m with stack := .val b :: .val a :: st } =
        .ok { m with stack := .val (bword (decide (a ≤ b))) :: st } 0 ∧
    run (binTail .ge) { m with stack := .val b :: .val a :: st } =
        .ok { m with stack := .val (bword (decide (b ≤ a))) :: st } 0 ∧
    run (binTail .eqB) { m with stack := .val b :: .val a :: st } =
        .ok { m with stack := .val (bword (decide (a = b))) :: st } 0 ∧
    run (binTail .neB) { m with stack := .val b :: .val a :: st } =
        .ok { m with stack := .val (bword (!decide (a = b))) :: st } 0 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [run, binTail, Instr.step, Machine.next, bword]
  · simp [run, binTail, Instr.step, Machine.next, bword]
  · simp [run, binTail, Instr.step, Machine.next, bword]
    by_cases h : a = b <;> simp [h, eq_comm]
  · simp [run, binTail, Instr.step, Machine.next, bword]
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

/-- Nothing represents an `int`: `int x = -1;` is outside the fragment. -/
theorem ReprV.int_false {v : Value} {w : Word} (h : ReprV .int v w) : False := by
  match v, w, h with
  | .int _, .val _, h => exact h
  | .bool _, .val _, h => exact h
  | .int _, .slot _, h => exact h
  | .bool _, .slot _, h => exact h

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

/-- **The operators agree.**  On words representing its operands, an
operator's tail computes the word of the interpreter's checked result, or
reverts exactly when the interpreter does.

Example: `a + b` with `a = 2^256 - 1`, `b = 1`: `checkArith` reverts (the sum
is not a `uint256`), and so does `add_tail`'s guard. -/
theorem tail_sim {op : BinOp} {p : PrimTy} (hop : binInFrag op p = true) (hand : op ≠ .and)
    (hor : op ≠ .or) {va vb : Value} {wa wb : Word} (ha : ReprV p va wa) (hb : ReprV p vb wb)
    (m : Machine) :
    ValOut (op.ret p) (applyBinOp op va vb >>= checkArith (op.retTy (.prim p)))
      (run (binTail op) { m with stack := wb :: wa :: m.stack }) m := by
  cases p with
  | int => exact (ha.int_false).elim
  | bool =>
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

/-! ## The simulation relation -/

/-- The machine `m` represents the interpreter state `σ`, whose locals `Γ` types. -/
structure Sim (C : Contract) (Γ : TyCtx) (σ : State) (m : Machine) : Prop where
  store : ReprStore C m.store σ.storage
  vals : ∀ x p, Γ x = some (.val p) →
    ∃ v, lookupBy x σ.env = some (.val v) ∧ ReprV p v (m.mem x)
  aliases : ∀ x R, Γ x = some (.alias R) →
    ∃ r segs s, lookupBy x σ.env = some (.spath r segs) ∧ m.mem x = .slot s ∧
      PathSlot C true r segs (.ref R) s
  balance : σ.selfBalance = m.balance
  net : ∀ a : Nat, a < W → σ.getNet a = m.net a

/-- `Sim` does not look at the stack. -/
theorem Sim.stack {C : Contract} {Γ : TyCtx} {σ : State} {m : Machine} (h : Sim C Γ σ m)
    (st : List Word) : Sim C Γ σ { m with stack := st } :=
  ⟨h.store, h.vals, h.aliases, h.balance, h.net⟩

/-- Pushing a word keeps `Sim`: `total + 1` pushes `total`'s word, then `1`. -/
theorem Sim.push {C : Contract} {Γ : TyCtx} {σ : State} {m : Machine} (h : Sim C Γ σ m)
    (w : Word) : Sim C Γ σ (m.push w) := h.stack _

/-- A location's outcome: its path read and its slot pushed; or both revert
while resolving it; or it resolves, and the read reverts (an index out of
bounds) and so does the machine. -/
def LocOut (C : Contract) (σ : State) (free : Bool) (T : Ty) (res : Res (Name × List Seg))
    (out : Out) (m : Machine) : Prop :=
  (∃ r segs s sv, res = .ok (r, segs) ∧ σ.findStorage r segs = .ok sv ∧
      PathSlot C free r segs T s ∧ ReprAt m.store T s sv ∧ out = .ok (m.push (.slot s)) 0) ∨
    (res = .error .revert ∧ out = .revert) ∨
    (∃ r segs, res = .ok (r, segs) ∧ σ.findStorage r segs = .error .revert ∧ free = false ∧
      out = .revert)

/-- A path that indexes no array may be used where any path may: `folks[7]` as an alias target and
as a read. -/
theorem PathSlot.ofTrue {C : Contract} {r : Name} {segs : List Seg} {T : Ty} {s : Slot}
    (h : PathSlot C true r segs T s) : ∀ free, PathSlot C free r segs T s
  | true => h
  | false => h.weaken

variable {C : Contract} {Γ : TyCtx} {σ : State}

/-- A literal or a local pushes its value.

Example: `x` with `x = 3` is `MLOAD x`, which pushes `3`. -/
theorem simple_sim {m : Machine} (hm : Sim C Γ σ m) : ∀ {p : PrimTy} (s : Simple C p),
    wtSimple Γ s = true → ValOut p (s.eval σ) (run (compileSimple s) m) m
  | p, .lit n _, hw => by
    simp only [wtSimple, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
    obtain ⟨⟨rfl, h0⟩, h1⟩ := hw
    exact .inl ⟨.int n, .val n.toNat, rfl, ⟨h0, h1, rfl⟩, rfl⟩
  | _, .bool b, _ => .inl ⟨.bool b, .val (bword b), rfl, rfl, rfl⟩
  | p, .local x, hw => by
    have hx : Γ x = some (.val p) := by simpa [wtSimple] using hw
    obtain ⟨v, henv, hv⟩ := hm.vals x p hx
    exact .inl ⟨v, m.mem x, by simp [Simple.eval, State.getEnv, henv]; rfl, hv, rfl⟩

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
theorem spath_sim : ∀ {T : Ty} (b : SPath C T) {free : Bool} {m : Machine}, Sim C Γ σ m →
    wtSPath Γ free b = true → LocOut C σ free T (b.resolve σ) (run (compileSPath b) m) m
  | _, @SPath.alias _ R x, free, m, hm, hw => by
    have hx : Γ x = some (.alias R) := by simpa [wtSPath] using hw
    obtain ⟨r, segs, s, henv, hmem, hp⟩ := hm.aliases x R hx
    rcases find_repr hm.store hp with ⟨sv, hsv, hr⟩ | ⟨h, _⟩
    · refine .inl ⟨r, segs, s, sv, ?_, hsv, hp.ofTrue free, hr, ?_⟩
      · simp [SPath.resolve, aliasPath, State.getEnv, henv]; rfl
      · simp [compileSPath, run, Instr.step, Machine.next, hmem]; rfl
    · cases h
  | _, .loc l, free, m, hm, hw => by
    simp only [SPath.resolve, compileSPath]
    exact loc_sim l hm (by simpa [wtSPath] using hw)

/-- A location pushes its slot, checking every array index against the
length on the way.

Example: `folks[7].age` pushes `keccak(7, 7) + 2`; `persons[5].age` with three
persons reverts at the bounds check, as the interpreter's read does. -/
theorem loc_sim : ∀ {T : Ty} (l : Loc C T) {free : Bool} {m : Machine}, Sim C Γ σ m →
    wtLoc Γ free l = true → LocOut C σ free T (l.resolve σ) (run (compileLoc l) m) m
  | _, .root r h, free, m, hm, _ => by
    obtain ⟨sv, hl, hr⟩ := hm.store r _ h
    exact .inl ⟨r, [], rootSlot C r, sv, rfl, by simp [State.findStorage, hl], .root h, hr, rfl⟩
  | _, @Loc.field _ s T b f h, free, m, hm, hw => by
    have hwb : wtSPath Γ free b = true := by simpa [wtLoc] using hw
    have h' : lookupBy f (structDef s) = some T := h
    simp only [Loc.resolve, compileLoc]
    rcases spath_sim b hm hwb with ⟨r, segs, s₀, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩ |
        ⟨r, segs, hres, hsv, hfree, hrun⟩
    · cases hr with
      | struct hex hall =>
        obtain ⟨v, hv⟩ := hex f T h'
        refine .inl ⟨r, segs ++ [.field f], s₀.add (offset s f), v, ?_, ?_, .field hp h,
          hall f T v h' hv, ?_⟩
        · simp [hres]; rfl
        · rw [findStorage_append, hsv]; simp [bind, Except.bind, SVal.find, hv]
        · rw [run_append_ok hrun]; simp [run, Instr.step, Machine.next, Machine.push]
    · exact .inr (.inl ⟨by simp [hres]; rfl, run_append_revert hrun⟩)
    · exact .inr (.inr ⟨r, segs ++ [.field f], by simp [hres]; rfl,
        by rw [findStorage_append, hsv]; rfl, hfree, run_append_revert hrun⟩)
  | _, @Loc.index _ _ k V .map b i, free, m, hm, hw => by
    have ihb : ∀ {m : Machine}, Sim C Γ σ m → wtSPath Γ free b = true →
        LocOut C σ free _ (b.resolve σ) (run (compileSPath b) m) m := fun hm hw => spath_sim b hm hw
    have ihi : ∀ {m : Machine}, Sim C Γ σ m → wtVal Γ i = true →
        ValOut _ (i.eval σ) (run (compileVal i) m) m := fun hm hw => val_sim i hm hw
    simp only [wtLoc, Bool.and_eq_true, beq_iff_eq] at hw
    obtain ⟨⟨rfl, hwb⟩, hwi⟩ := hw
    simp only [Loc.resolve, compileLoc, List.append_assoc]
    rcases ihb hm hwb with ⟨r, segs, s₀, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩ |
        ⟨r, segs, hres, hsv, hfree, hrun⟩
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
          · simp [hres, hv, Value.asInt]; rfl
          · rw [findStorage_append, hsv]
            simp only [bind, Except.bind, SVal.find]
            cases lookupBy (n : Int) entries <;> simp
          · rw [run_append_ok hrun']; simp [run, Instr.step, Machine.next, Machine.push]
        · exact .inr (.inl ⟨by simp [hres, hv]; rfl, run_append_revert hrun'⟩)
    · exact .inr (.inl ⟨by simp [hres]; rfl, run_append_revert hrun⟩)
    · rcases ihi hm hwi with ⟨v, w, hv, hrep, _⟩ | ⟨hv, _⟩
      · obtain ⟨n, hn, rfl, rfl⟩ := hrep.uint_inv
        exact .inr (.inr ⟨r, segs ++ [.at n], by simp [hres, hv, Value.asInt]; rfl,
          by rw [findStorage_append, hsv]; rfl, hfree, run_append_revert hrun⟩)
      · exact .inr (.inl ⟨by simp [hres, hv]; rfl, run_append_revert hrun⟩)
  | _, @Loc.index _ _ _ E .arr b i, free, m, hm, hw => by
    have ihb : ∀ {m : Machine}, Sim C Γ σ m → wtSPath Γ free b = true →
        LocOut C σ free _ (b.resolve σ) (run (compileSPath b) m) m := fun hm hw => spath_sim b hm hw
    have ihi : ∀ {m : Machine}, Sim C Γ σ m → wtVal Γ i = true →
        ValOut _ (i.eval σ) (run (compileVal i) m) m := fun hm hw => val_sim i hm hw
    simp only [wtLoc, Bool.and_eq_true, Bool.not_eq_true'] at hw
    obtain ⟨⟨rfl, hwb⟩, hwi⟩ := hw
    simp only [Loc.resolve, compileLoc, List.append_assoc]
    rcases ihb hm hwb with ⟨r, segs, s₀, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩ |
        ⟨r, segs, hres, hsv, hfree, hrun⟩
    · cases hr with
      | array hl hW hall =>
        rename_i elems shadow
        rw [run_append_ok hrun]
        rcases ihi (hm.push _) hwi with ⟨v, w, hv, hrep, hrun'⟩ | ⟨hv, hrun'⟩
        · obtain ⟨n, hn, rfl, rfl⟩ := hrep.uint_inv
          rw [run_append_ok hrun']
          have hres' : (do
              let (r, segs) ← b.resolve σ
              let i ← (← i.eval σ).asInt
              pure (r, segs ++ [Seg.at i]) : Res (Name × List Seg)) = .ok (r, segs ++ [.at n]) := by
            simp [hres, hv, Value.asInt]; rfl
          rw [hres']
          have hb := boundsCheck_run m m.stack (elemSlot (size E)) n s₀
          simp only [Machine.push] at hb ⊢
          rw [hb, hl]
          by_cases hin : n < elems.length
          · rw [if_pos hin]
            have hp' := PathSlot.elem hp (Int.natCast_nonneg n) (by omega)
            rw [Int.toNat_natCast] at hp'
            refine .inl ⟨r, segs ++ [.at n], .data s₀ (n * size E), elems[n], rfl, ?_, hp',
              hall n hin, elemSlot_run m m.stack n (size E) s₀⟩
            rw [findStorage_append, hsv]
            simp [bind, Except.bind, SVal.find, hin]
          · rw [if_neg hin]
            refine .inr (.inr ⟨r, segs ++ [.at n], rfl, ?_, rfl, rfl⟩)
            rw [findStorage_append, hsv]
            simp [bind, Except.bind, SVal.find, hin]
        · exact .inr (.inl ⟨by simp [hres, hv]; rfl, run_append_revert hrun'⟩)
    · exact .inr (.inl ⟨by simp [hres]; rfl, run_append_revert hrun⟩)
    · rcases ihi hm hwi with ⟨v, w, hv, hrep, _⟩ | ⟨hv, _⟩
      · obtain ⟨n, hn, rfl, rfl⟩ := hrep.uint_inv
        exact .inr (.inr ⟨r, segs ++ [.at n], by simp [hres, hv, Value.asInt]; rfl,
          by rw [findStorage_append, hsv]; rfl, hfree, run_append_revert hrun⟩)
      · exact .inr (.inl ⟨by simp [hres, hv]; rfl, run_append_revert hrun⟩)

/-- An expression pushes its value, or reverts where the interpreter does.

Example: `total * 2` pushes twice `total`'s word, and reverts with the
interpreter when that overflows; `c ? a : b` runs only the branch `c` picks. -/
theorem val_sim : ∀ {p : PrimTy} (e : Val C p) {m : Machine}, Sim C Γ σ m →
    wtVal Γ e = true → ValOut p (e.eval σ) (run (compileVal e) m) m
  | _, .simple s, m, hm, hw => by
    simp only [Val.eval, compileVal]
    exact simple_sim hm s (by simpa [wtVal] using hw)
  | p, .read l, m, hm, hw => by
    simp only [wtVal, Bool.and_eq_true] at hw
    obtain ⟨hp, hwl⟩ := hw
    simp only [Val.eval, compileVal]
    rcases loc_sim l hm hwl with ⟨r, segs, s, sv, hres, hsv, _, hr, hrun⟩ | ⟨hres, hrun⟩ |
        ⟨r, segs, hres, hsv, _, hrun⟩
    · rw [run_append_ok hrun]
      cases p with
      | int => simp [primInFrag] at hp
      | uint =>
        cases hr with
        | uint h0 h1 h2 =>
          rename_i n
          refine .inl ⟨.int n, .val n.toNat, ?_, ⟨h0, h1, rfl⟩, ?_⟩
          · simp [hres, hsv, SVal.asValue, bind, Except.bind]
          · simp [run, Instr.step, Machine.next, Machine.push, h2]
      | bool =>
        cases hr with
        | bool h =>
          rename_i b
          refine .inl ⟨.bool b, .val (bword b), ?_, rfl, ?_⟩
          · simp [hres, hsv, SVal.asValue, bind, Except.bind]
          · simp [run, Instr.step, Machine.next, Machine.push, h]
    · exact .inr ⟨by simp [hres]; rfl, run_append_revert hrun⟩
    · exact .inr ⟨by simp [hres, hsv, bind, Except.bind], run_append_revert hrun⟩
  | _, @Val.binop _ p q op hacc hq a b, m, hm, hw => by
    have iha : ∀ {m : Machine}, Sim C Γ σ m → wtVal Γ a = true →
        ValOut p (a.eval σ) (run (compileVal a) m) m := fun hm hw => val_sim a hm hw
    have ihb : ∀ {m : Machine}, Sim C Γ σ m → wtVal Γ b = true →
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
        compileVal (.binop op hacc rfl a b) = compileVal a ++ compileVal b ++ binTail op := by
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
    have iha : ∀ {m : Machine}, Sim C Γ σ m → wtVal Γ a = true →
        ValOut p (a.eval σ) (run (compileVal a) m) m := fun hm hw => val_sim a hm hw
    subst hq
    simp only [wtVal, Bool.and_eq_true, beq_iff_eq] at hw
    obtain ⟨rfl, hwa⟩ := hw
    obtain rfl : p = .bool := by cases p <;> simp [UnOp.accepts] at hacc ⊢
    simp only [Val.eval, compileVal]
    rcases iha hm hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
    · obtain ⟨x, rfl, rfl⟩ := hra.bool_inv
      rw [run_append_ok hruna, hva]
      refine .inl ⟨.bool !x, .val (bword !x), ?_, rfl, ?_⟩
      · simp [applyUnOp, Value.asBool, unopCheck, bind, Except.bind]; rfl
      · cases x <;> rfl
    · exact .inr ⟨by simp [hva, bind, Except.bind], run_append_revert hruna⟩
  | p, .ternary c a b, m, hm, hw => by
    have ihc : ∀ {m : Machine}, Sim C Γ σ m → wtVal Γ c = true →
        ValOut .bool (c.eval σ) (run (compileVal c) m) m := fun hm hw => val_sim c hm hw
    have iha : ∀ {m : Machine}, Sim C Γ σ m → wtVal Γ a = true →
        ValOut p (a.eval σ) (run (compileVal a) m) m := fun hm hw => val_sim a hm hw
    have ihb : ∀ {m : Machine}, Sim C Γ σ m → wtVal Γ b = true →
        ValOut p (b.eval σ) (run (compileVal b) m) m := fun hm hw => val_sim b hm hw
    simp only [wtVal, Bool.and_eq_true] at hw
    obtain ⟨⟨⟨_, hwc⟩, hwa⟩, hwb⟩ := hw
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
  | _, .readMem _, _, _, hw => by simp [wtVal] at hw

end

/-! ## Statements -/

/-- A statement's outcome: both succeed, the machine's stack as it was and the
states related, or both revert. -/
def StmtOut (C : Contract) (Γ' : TyCtx) (res : Res State) (out : Out) (m : Machine) : Prop :=
  (∃ σ' m', res = .ok σ' ∧ out = .ok m' 0 ∧ m'.stack = m.stack ∧ Sim C Γ' σ' m') ∨
    (res = .error .revert ∧ out = .revert)

/-- Forgetting locals keeps `Sim`: after `if`, only what both branches agree on. -/
theorem Sim.weaken {Γ' : TyCtx} {m : Machine} (h : Sim C Γ σ m)
    (hΓ : ∀ x t, Γ' x = some t → Γ x = some t) : Sim C Γ' σ m :=
  ⟨h.store, fun x p hx => h.vals x p (hΓ x _ hx), fun x R hx => h.aliases x R (hΓ x _ hx),
    h.balance, h.net⟩

/-- `uint x = e;`: the cell of `x` and the binding of `x` change together. -/
theorem Sim.bindVal {m : Machine} (h : Sim C Γ σ m) (x : Var) {p : PrimTy} {v : Value} {w : Word}
    (hv : ReprV p v w) :
    Sim C (Γ.set x (some (.val p))) (σ.setEnv x (.val v)) { m with mem := upd m.mem x w } := by
  refine ⟨h.store, fun y q hy => ?_, fun y R hy => ?_, h.balance, h.net⟩
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

/-- `Person storage p = alice;`: the cell of `p` holds `alice`'s slot. -/
theorem Sim.bindAlias {m : Machine} (h : Sim C Γ σ m) (x : Var) {R : RefTy} {r : Name}
    {segs : List Seg} {s : Slot} (hp : PathSlot C true r segs (.ref R) s) :
    Sim C (Γ.set x (some (.alias R))) (σ.setEnv x (.spath r segs))
      { m with mem := upd m.mem x (.slot s) } := by
  refine ⟨h.store, fun y q hy => ?_, fun y R' hy => ?_, h.balance, h.net⟩
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

/-- A storage write: the new storage represented by the new machine storage. -/
theorem Sim.store' {m : Machine} (h : Sim C Γ σ m) {st' : Slot → Nat} {stor : List (Name × SVal)}
    (hs : ReprStore C st' stor) : Sim C Γ { σ with storage := stor } { m with store := st' } :=
  ⟨hs, h.vals, h.aliases, h.balance, h.net⟩

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

/-- The operators with an `op=` form are compiled with their checks. -/
theorem compound_frag {op : BinOp} (h : op.hasCompoundAssign = true) :
    binInFrag op .uint = true ∧ op ≠ .and ∧ op ≠ .or ∧ op.ret .uint = .uint ∧
      op.retTy (.prim .uint) = .prim .uint := by
  cases op <;> simp_all [BinOp.hasCompoundAssign, binInFrag, BinOp.ret, BinOp.retTy, BinOp.isArith]

/-- An `op=` on a storage target resolves the target once: `folks[k].age += 1;` evaluates `k`
once. -/
theorem opLoc_store {p : PrimTy} {l : OpLoc C p} {loc : Loc C (.prim p)}
    (h : opLocToLoc l = some loc)
    (op : BinOp) (v : Value) :
    l.store σ op v = (loc.resolve σ >>= fun rs => opStore σ op p rs.1 rs.2 v) := by
  cases l <;> simp [opLocToLoc] at h <;> subst h <;> rfl

/-- A successful step goes on: `uint x = 1;` then the next statement. -/
@[simp] theorem Except.ok_bind' {ε α β : Type} (x : α) (f : α → Except ε β) :
    (Except.ok x >>= f) = f x := rfl
/-- A revert stops the rest: `revert(); total = 1;` never writes. -/
@[simp] theorem Except.error_bind' {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl

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

/-- A `bool` or `uint` value written to a slot is represented there. -/
theorem repr_write {p : PrimTy} (hp : primInFrag p = true) {v : Value} {w : Word}
    (hv : ReprV p v w) (st : Slot → Nat) (s : Slot) :
    ∃ a, w = .val a ∧ ReprAt (upd st s a) (.prim p) s v.toSVal := by
  cases p with
  | uint =>
    obtain ⟨a, ha, rfl, rfl⟩ := hv.uint_inv
    exact ⟨a, rfl, .uint (Int.natCast_nonneg a) (by omega) (by simp)⟩
  | bool =>
    obtain ⟨b, rfl, rfl⟩ := hv.bool_inv
    exact ⟨_, rfl, .bool (by simp)⟩
  | int => simp [primInFrag] at hp

/-- `Person storage p = folks[7];` binds the alias to the path's slot. -/
theorem alias_sim {Δ : TyCtx} {τ : State} {m : Machine} {R : RefTy} (q : SPath C (.ref R))
    (x : Var) (hm : Sim C Δ τ m) (hw : wtSPath Δ true q = true) :
    StmtOut C (Δ.set x (some (.alias R))) (ARhs.bind τ x (.path q))
      (run (compileSPath q ++ [.mstore x]) m) m := by
  rcases spath_sim q hm hw with ⟨r, segs, s, sv, hres, _, hp, _, hrun⟩ | ⟨hres, hrun⟩ |
      ⟨r, segs, hres, hsv, hfree, hrun⟩
  · refine .inl ⟨_, { m with mem := upd m.mem x (.slot s) }, ?_, ?_, rfl, hm.bindAlias x hp⟩
    · simp [ARhs.bind, hres, bind, Except.bind]; rfl
    · rw [run_append_ok hrun]; rfl
  · exact .inr ⟨by simp [ARhs.bind, hres, bind, Except.bind], run_append_revert hrun⟩
  · cases hfree

/-- `total += e;` and its siblings on a storage target: the target resolved
and read once, the right-hand side, the checked operator, the write back.

Example: with `total = 2^256 - 1`, `total += 1;` reverts in both; with
`total = 3` it writes `4` to slot `0`. -/
theorem opStore_sim {Δ : TyCtx} {τ : State} {m : Machine} {op : BinOp}
    (hop : op.hasCompoundAssign = true) {l : OpLoc C .uint} {loc : Loc C (.prim .uint)}
    (hl : opLocToLoc l = some loc) (r : Val C .uint) (hm : Sim C Δ τ m)
    (hwl : wtLoc Δ false loc = true) (hwr : wtVal Δ r = true) :
    StmtOut C Δ (do l.store τ op (← r.eval τ))
      (run (compileLoc loc ++ [.dup 1, .sload] ++ compileVal r ++ binTail op ++
        [.swap 1, .sstore]) m)
      m := by
  obtain ⟨hfrag, hand, hor, hret, hretTy⟩ := compound_frag hop
  simp only [opLoc_store hl, List.append_assoc]
  rcases loc_sim loc hm hwl with ⟨rt, segs, s, sv, hres, hsv, hp, hr, hrunl⟩ | ⟨hres, hrunl⟩ |
      ⟨rt, segs, hres, hsv, _, hrunl⟩
  · cases hr with
    | uint h0 h1 h2 =>
      rename_i n
      obtain ⟨a, rfl⟩ : ∃ a : Nat, n = a := ⟨n.toNat, (Int.toNat_of_nonneg h0).symm⟩
      simp only [Int.toNat_natCast] at h2
      rw [run_append_ok hrunl,
        run_append_ok (m' := { m with stack := .val a :: .slot s :: m.stack })
        (by simp [run, Instr.step, Machine.next, Machine.push, h2])]
      rcases val_sim r (hm.stack _) hwr with ⟨vr, wr, hvr, hrv, hrunr⟩ | ⟨hvr, hrunr⟩
      · rw [run_append_ok hrunr]
        have ht := tail_sim hfrag hand hor (ReprV.uint (a := a) (by omega)) hrv
          { m with stack := .slot s :: m.stack }
        rw [hret, hretTy] at ht
        rcases ht with ⟨vn, wn, hvn, hrn, hrunt⟩ | ⟨hvn, hrunt⟩
        · obtain ⟨an, rfl, hnew⟩ := repr_write rfl hrn m.store s
          obtain ⟨stor, hsave, hrep⟩ := save_repr hm.store hp ⟨_, hsv⟩ hnew
            (fun x hx => upd_other _ _ fun he => hx (he ▸ Occ.prim))
          refine .inl ⟨_, { m with store := upd m.store s an }, ?_, ?_, rfl, hm.store' hrep⟩
          · simp only [hvr, hres, Except.ok_bind', opStore, hsv, SVal.asValue]
            rw [bind_bind_ok hvn]; exact hsave
          · change run (binTail op ++ _) { m with stack := wr :: .val a :: .slot s :: m.stack } = _
            rw [run_append_ok hrunt]; rfl
        · refine .inr ⟨?_, ?_⟩
          · simp only [hvr, hres, Except.ok_bind', opStore, hsv, SVal.asValue]
            rw [bind_bind_error hvn]
          · change run (binTail op ++ _) { m with stack := wr :: .val a :: .slot s :: m.stack } = _
            rw [run_append_revert hrunt]
      · exact .inr ⟨by simp [hvr, bind, Except.bind], run_append_revert hrunr⟩
  · rcases val_sim r hm hwr with ⟨vr, wr, hvr, _, _⟩ | ⟨hvr, _⟩
    · exact .inr ⟨by simp [hvr, hres, bind, Except.bind], run_append_revert hrunl⟩
    · exact .inr ⟨by simp [hvr, bind, Except.bind], run_append_revert hrunl⟩
  · rcases val_sim r hm hwr with ⟨vr, wr, hvr, _, _⟩ | ⟨hvr, _⟩
    · exact .inr ⟨by simp [hvr, hres, bind, Except.bind, opStore, hsv], run_append_revert hrunl⟩
    · exact .inr ⟨by simp [hvr, bind, Except.bind], run_append_revert hrunl⟩

/-- `x += e;` on a `uint` local: its cell read, the checked operator, the cell
written. -/
theorem opLocal_sim {Δ : TyCtx} {τ : State} {m : Machine} {op : BinOp}
    (hop : op.hasCompoundAssign = true) (x : Var) (r : Val C .uint) (hm : Sim C Δ τ m)
    (hx : Δ x = some (.val .uint)) (hwr : wtVal Δ r = true) :
    StmtOut C Δ (do (OpLoc.local (C := C) (p := .uint) x).store τ op (← r.eval τ))
      (run ([.mload x] ++ compileVal r ++ binTail op ++ [.mstore x]) m) m := by
  obtain ⟨hfrag, hand, hor, hret, hretTy⟩ := compound_frag hop
  obtain ⟨old, henv, hrold⟩ := hm.vals x .uint hx
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
      · change run (binTail op ++ _) { m with stack := wr :: m.mem x :: m.stack } = _
        rw [run_append_ok hrunt]; rfl
    · refine .inr ⟨?_, ?_⟩
      · simp only [hvr, Except.ok_bind', OpLoc.store, opLocal, State.getEnv, henv, pure_bind]
        rw [bind_bind_error hvn]
      · change run (binTail op ++ _) { m with stack := wr :: m.mem x :: m.stack } = _
        rw [run_append_revert hrunt]
  · exact .inr ⟨by simp [hvr, bind, Except.bind], run_append_revert hrunr⟩

/-- `x++` and `x--` are `x += 1` and `x -= 1`, checked the same way. -/
theorem bump_src (op : IncDec) (a : Nat) :
    checkArith (.prim .uint) (.int (if op.isIncrement then (a : Int) + 1 else (a : Int) - 1)) =
      (applyBinOp op.binOp (.int a) (.int ((1 : Nat) : Int)) >>=
        checkArith (op.binOp.retTy (.prim .uint))) := by
  have hadd : applyBinOp .add (.int a) (.int ((1 : Nat) : Int)) = .ok (.int ((a : Int) + 1)) := rfl
  have hsub : applyBinOp .sub (.int a) (.int ((1 : Nat) : Int)) = .ok (.int ((a : Int) - 1)) := rfl
  have radd : BinOp.add.retTy (.prim .uint) = .prim .uint := rfl
  have rsub : BinOp.sub.retTy (.prim .uint) = .prim .uint := rfl
  cases op
  · rw [show IncDec.binOp .preInc = .add from rfl, hadd, Except.ok_bind', radd]; rfl
  · rw [show IncDec.binOp .preDec = .sub from rfl, hsub, Except.ok_bind', rsub]; rfl
  · rw [show IncDec.binOp .postInc = .add from rfl, hadd, Except.ok_bind', radd]; rfl
  · rw [show IncDec.binOp .postDec = .sub from rfl, hsub, Except.ok_bind', rsub]; rfl

/-- `++` and `--` are the `+=`/`-=` of the fragment: `x++;` is checked as `x += 1;`. -/
theorem bump_frag (op : IncDec) : op.binOp.hasCompoundAssign = true := by
  cases op <;> rfl

/-- `++` on a storage target resolves it once: `folks[k].age++;` evaluates `k` once. -/
theorem opLoc_bump {p : PrimTy} {l : OpLoc C p} {loc : Loc C (.prim p)}
    (h : opLocToLoc l = some loc)
    (op : IncDec) :
    l.bump σ op = (loc.resolve σ >>= fun rs => bumpStore σ op p rs.1 rs.2) := by
  cases l <;> simp [opLocToLoc] at h <;> subst h <;> rfl

/-- `total++;` on a storage target: read once, the checked increment, the write
back.  With `total = 2^256 - 1` both revert; with `total = 3`, slot `0` holds
`4`. -/
theorem bumpStore_sim {Δ : TyCtx} {τ : State} {m : Machine} (op : IncDec) {l : OpLoc C .uint}
    {loc : Loc C (.prim .uint)} (hl : opLocToLoc l = some loc) (hm : Sim C Δ τ m)
    (hwl : wtLoc Δ false loc = true) :
    StmtOut C Δ (do pure (← l.bump τ op).1)
      (run (compileLoc loc ++ [.dup 1, .sload, .push (.val 1)] ++ binTail op.binOp ++
        [.swap 1, .sstore]) m) m := by
  obtain ⟨hfrag, hand, hor, hret, hretTy⟩ := compound_frag (bump_frag op)
  simp only [opLoc_bump hl, List.append_assoc]
  rcases loc_sim loc hm hwl with ⟨rt, segs, s, sv, hres, hsv, hp, hr, hrunl⟩ | ⟨hres, hrunl⟩ |
      ⟨rt, segs, hres, hsv, _, hrunl⟩
  · cases hr with
    | uint h0 h1 h2 =>
      rename_i n
      obtain ⟨a, rfl⟩ : ∃ a : Nat, n = a := ⟨n.toNat, (Int.toNat_of_nonneg h0).symm⟩
      simp only [Int.toNat_natCast] at h2
      rw [run_append_ok hrunl, run_append_ok
        (m' := { m with stack := .val 1 :: .val a :: .slot s :: m.stack })
        (by simp [run, Instr.step, Machine.next, Machine.push, h2])]
      have ht := tail_sim hfrag hand hor (ReprV.uint (a := a) (by omega))
        (ReprV.uint (a := 1) (by have := W_pos; unfold W at this ⊢; omega))
        { m with stack := .slot s :: m.stack }
      rw [hret, hretTy] at ht
      rcases ht with ⟨vn, wn, hvn, hrn, hrunt⟩ | ⟨hvn, hrunt⟩
      · obtain ⟨an, rfl, hnew⟩ := repr_write rfl hrn m.store s
        obtain ⟨stor, hsave, hrep⟩ := save_repr hm.store hp ⟨_, hsv⟩ hnew
          (fun x hx => upd_other _ _ fun he => hx (he ▸ Occ.prim))
        refine .inl ⟨_, { m with store := upd m.store s an }, ?_, ?_, rfl, hm.store' hrep⟩
        · simp only [hres, Except.ok_bind', bumpStore, hsv, SVal.asValue, Value.asInt]
          rw [bump_src, hretTy, hvn, Except.ok_bind', hsave]; rfl
        · change run (binTail op.binOp ++ _)
            { m with stack := .val 1 :: .val a :: .slot s :: m.stack } = _
          rw [run_append_ok hrunt]; rfl
      · refine .inr ⟨?_, ?_⟩
        · simp only [hres, Except.ok_bind', bumpStore, hsv, SVal.asValue, Value.asInt]
          rw [bump_src, hretTy, hvn]; rfl
        · change run (binTail op.binOp ++ _)
            { m with stack := .val 1 :: .val a :: .slot s :: m.stack } = _
          rw [run_append_revert hrunt]
  · exact .inr ⟨by simp [hres] <;> rfl, run_append_revert hrunl⟩
  · exact .inr ⟨by simp [hres, bumpStore, hsv] <;> rfl, run_append_revert hrunl⟩

/-- `x++;` on a `uint` local. -/
theorem bumpLocal_sim {Δ : TyCtx} {τ : State} {m : Machine} (op : IncDec) (x : Var)
    (hm : Sim C Δ τ m) (hx : Δ x = some (.val .uint)) :
    StmtOut C Δ (do pure (← (OpLoc.local (C := C) (p := .uint) x).bump τ op).1)
      (run ([.mload x, .push (.val 1)] ++ binTail op.binOp ++ [.mstore x]) m) m := by
  obtain ⟨hfrag, hand, hor, hret, hretTy⟩ := compound_frag (bump_frag op)
  obtain ⟨old, henv, hrold⟩ := hm.vals x .uint hx
  obtain ⟨a, ha, rfl, hw⟩ := hrold.uint_inv
  rw [List.append_assoc, run_append_ok (m' := { m with stack := .val 1 :: .val a :: m.stack })
    (by simp [run, Instr.step, Machine.next, hw])]
  have ht := tail_sim hfrag hand hor (ReprV.uint ha)
    (ReprV.uint (a := 1) (by have := W_pos; unfold W at this ⊢; omega)) m
  rw [hret, hretTy] at ht
  rcases ht with ⟨vn, wn, hvn, hrn, hrunt⟩ | ⟨hvn, hrunt⟩
  · have hs := hm.bindVal x hrn
    rw [TyCtx.set_self hx] at hs
    refine .inl ⟨_, { m with mem := upd m.mem x wn }, ?_, ?_, rfl, hs⟩
    · simp only [OpLoc.bump, bumpLocal, State.getEnv, henv, Except.ok_bind', pure_bind,
        Value.asInt]
      rw [bump_src, hretTy, hvn]; rfl
    · rw [run_append_ok hrunt]; rfl
  · refine .inr ⟨?_, run_append_revert hrunt⟩
    simp only [OpLoc.bump, bumpLocal, State.getEnv, henv, Except.ok_bind', pure_bind, Value.asInt]
    rw [bump_src, hretTy, hvn]; rfl

mutual

/-- **A statement's code does what the statement does**: both succeed, the
machine's stack as it was and the states related, or both revert.

Example: `alice.age = 10;` is `PUSH 10; PUSH @11; PUSH 2; ADD; SSTORE`, which
writes slot `13`; `require(total > 3);` with `total = 2` reverts in both. -/
theorem stmt_sim : ∀ (s : Stmt C) {Δ Δ' : TyCtx} {τ : State} {m : Machine}, Sim C Δ τ m →
    wtStmt Δ s = some Δ' → StmtOut C Δ' (s.run τ) (run (compileStmt s) m) m
  | @Stmt.assign _ (.prim p) l (.val v), Δ, Δ', τ, m, hm, hw => by
    simp only [wtStmt, Bool.and_eq_true, Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨⟨⟨hp, hwl⟩, hwv⟩, rfl⟩ := hw
    simp only [Stmt.run, Src.value, compileStmt, List.append_assoc]
    rcases val_sim v hm hwv with ⟨vv, w, hvv, hrv, hrun⟩ | ⟨hvv, hrun⟩
    · rw [run_append_ok hrun]
      rcases loc_sim l (hm.push w) hwl with ⟨r, segs, s, sv, hres, hsv, hps, _, hrunl⟩ |
          ⟨hres, hrunl⟩ | ⟨r, segs, hres, hsv, _, hrunl⟩
      · rw [run_append_ok hrunl]
        obtain ⟨a, rfl, hnew⟩ := repr_write hp hrv m.store s
        obtain ⟨stor, hsave, hrep⟩ := save_repr hm.store hps ⟨sv, hsv⟩ hnew
          (fun x hx => upd_other _ _ fun he => hx (he ▸ Occ.prim))
        refine .inl ⟨_, { m with store := upd m.store s a }, ?_, rfl, rfl, hm.store' hrep⟩
        simp [hvv, hres, hsave]
      · exact .inr ⟨by simp [hvv, hres], run_append_revert hrunl⟩
      · refine .inr ⟨?_, run_append_revert hrunl⟩
        have := saveStorage_error hsv [] vv.toSVal
        simp only [List.append_nil] at this
        simp [hvv, hres, this]
    · exact .inr ⟨by simp [hvv], run_append_revert hrun⟩
  | .rebind x (.path q), Δ, Δ', τ, m, hm, hw => by
    simp only [wtStmt, Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨hwq, rfl⟩ := hw
    exact alias_sim q x hm hwq
  | .assignLocal x r, Δ, Δ', τ, m, hm, hw => by
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
  | .declLocal p x none, Δ, Δ', τ, m, hm, hw => by
    simp only [wtStmt, Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨hp, rfl⟩ := hw
    have hrv : ReprV p (PrimTy.default p) (.val 0) := by
      cases p with
      | uint => exact ReprV.uint (a := 0) W_pos
      | bool => exact ReprV.bool false
      | int => simp [primInFrag] at hp
    exact .inl ⟨_, { m with mem := upd m.mem x (.val 0) }, rfl, rfl, rfl, hm.bindVal x hrv⟩
  | .declLocal p x (some e), Δ, Δ', τ, m, hm, hw => by
    simp only [wtStmt, Bool.and_eq_true, Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨⟨_, hwe⟩, rfl⟩ := hw
    simp only [Stmt.run, compileStmt]
    rcases val_sim e hm hwe with ⟨v, w, hv, hrv, hrun⟩ | ⟨hv, hrun⟩
    · refine .inl ⟨_, { m with mem := upd m.mem x w }, by simp [hv]; rfl, ?_, rfl,
        hm.bindVal x hrv⟩
      rw [run_append_ok hrun]; rfl
    · exact .inr ⟨by rw [hv]; rfl, run_append_revert hrun⟩
  | .declStorage R x none, Δ, Δ', τ, m, hm, hw => by
    simp only [wtStmt, Option.some.injEq] at hw
    subst hw
    refine .inl ⟨τ, m, rfl, rfl, rfl, hm.weaken fun y t hy => ?_⟩
    by_cases hyx : y = x
    · subst hyx; simp [TyCtx.set] at hy
    · simpa [TyCtx.set, upd_other _ _ hyx] using hy
  | .declStorage R x (some (.path q)), Δ, Δ', τ, m, hm, hw => by
    simp only [wtStmt, Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨hwq, rfl⟩ := hw
    exact alias_sim q x hm hwq
  | .opAssign op hop _ (.local x) r, Δ, Δ', τ, m, hm, hw => by
    simp only [wtStmt, wtOpLoc, Bool.and_eq_true, beq_iff_eq, Option.ite_none_right_eq_some,
      Option.some.injEq] at hw
    obtain ⟨⟨⟨rfl, hx⟩, hwr⟩, rfl⟩ := hw
    exact opLocal_sim hop x r hm hx hwr
  | .opAssign op hop _ (.root rt h) r, Δ, Δ', τ, m, hm, hw => by
    simp only [wtStmt, wtOpLoc, opLocToLoc, Bool.and_eq_true, beq_iff_eq,
      Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨⟨⟨rfl, hwl⟩, hwr⟩, rfl⟩ := hw
    exact opStore_sim hop rfl r hm hwl hwr
  | .opAssign op hop _ (.field b f h) r, Δ, Δ', τ, m, hm, hw => by
    simp only [wtStmt, wtOpLoc, opLocToLoc, Bool.and_eq_true, beq_iff_eq,
      Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨⟨⟨rfl, hwl⟩, hwr⟩, rfl⟩ := hw
    exact opStore_sim hop rfl r hm hwl hwr
  | .opAssign op hop _ (.index it b i) r, Δ, Δ', τ, m, hm, hw => by
    simp only [wtStmt, wtOpLoc, opLocToLoc, Bool.and_eq_true, beq_iff_eq,
      Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨⟨⟨rfl, hwl⟩, hwr⟩, rfl⟩ := hw
    exact opStore_sim hop rfl r hm hwl hwr
  | .opAssign _ _ _ (.mfield ..) _, _, _, _, _, _, hw => by
    simp [wtStmt, wtOpLoc, opLocToLoc] at hw
  | .opAssign _ _ _ (.mindex ..) _, _, _, _, _, _, hw => by
    simp [wtStmt, wtOpLoc, opLocToLoc] at hw
  | .pop b, Δ, Δ', τ, m, hm, hw => by
    simp only [wtStmt, Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨hwb, rfl⟩ := hw
    simp only [Stmt.run, compileStmt]
    rcases spath_sim b hm hwb with ⟨r, segs, s, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩ |
        ⟨r, segs, hres, hsv, _, hrun⟩
    · have hr' := hr
      cases hr with
      | array hl hW hall =>
        rename_i elems shadow
        rw [run_append_ok hrun]
        have hpc := popCode_run m m.stack s (by rw [hl]; exact hW)
        simp only [Machine.push] at hpc ⊢
        rw [hpc, hl]
        by_cases h0 : elems.length = 0
        · rw [if_pos h0]
          have : elems = [] := List.eq_nil_of_length_eq_zero h0
          subst this
          exact .inr ⟨by simp [hres, popAt, hsv], rfl⟩
        · rw [if_neg h0]
          obtain ⟨last, restRev, hrev⟩ : ∃ last restRev, elems.reverse = last :: restRev := by
            cases h : elems.reverse with
            | nil => simp at h; exact absurd (by simp [h]) h0
            | cons last restRev => exact ⟨last, restRev, rfl⟩
          have hnew := pop_repr hr' hrev
          obtain ⟨stor, hsave, hrep⟩ := save_repr hm.store hp ⟨_, hsv⟩ hnew
            (fun x hx => upd_other _ _ fun he => hx (he ▸ Occ.len))
          refine .inl ⟨_, _, ?_, rfl, rfl, hm.store' hrep⟩
          simp [hres, popAt, hsv, hrev, hsave]
    · exact .inr ⟨by simp [hres], run_append_revert hrun⟩
    · exact .inr ⟨by simp [hres, popAt, hsv], run_append_revert hrun⟩
  | .transfer r a, Δ, Δ', τ, m, hm, hw => by
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
          · refine ⟨hm.store, hm.vals, hm.aliases, ?_, fun a' ha' => ?_⟩
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
      · exact .inr ⟨by simp [hvr, hva, Value.asInt], run_append_revert hruna⟩
    · exact .inr ⟨by simp [hvr], run_append_revert hrunr⟩
  | @Stmt.delete _ T l, Δ, Δ', τ, m, hm, hw => by
    simp only [wtStmt, Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨hwl, rfl⟩ := hw
    simp only [Stmt.run, compileStmt, List.append_assoc]
    rcases loc_sim l hm hwl with ⟨r, segs, s, sv, hres, hsv, hp, hr, hrun⟩ | ⟨hres, hrun⟩ |
        ⟨r, segs, hres, hsv, _, hrun⟩
    · rw [run_append_ok hrun]
      simp only [Machine.push]
      rw [run_append_ok (zeroCode_run m m.stack s (leaves T))]
      have hnew := zero_repr hr (tyRank T + 1) (Nat.lt_succ_self _)
        (st' := zeroAt m.store s (leaves T)) (fun o ho => zeroAt_zero ⟨o, ho, rfl⟩)
        (fun x _ hx => zeroAt_other hx)
      obtain ⟨stor, hsave, hrep⟩ := save_repr hm.store hp ⟨_, hsv⟩ hnew
        (fun x hx => zeroAt_other fun o ho hxo => hx (hxo ▸ leavesF_occ _ T s o ho))
      refine .inl ⟨_, { m with store := zeroAt m.store s (leaves T) }, ?_, rfl, rfl,
        hm.store' hrep⟩
      simp [hres, hsv, hsave]
    · exact .inr ⟨by simp [hres], run_append_revert hrun⟩
    · exact .inr ⟨by simp [hres, hsv], run_append_revert hrun⟩
  | .ite c t e, Δ, Δ', τ, m, hm, hw => by
    have iht : ∀ {Δ₁ : TyCtx} {m : Machine}, Sim C Δ τ m → wtProg Δ t = some Δ₁ →
        StmtOut C Δ₁ (Prog.run τ t) (run (compileProg t) m) m := fun hm hw => prog_sim t hm hw
    have ihe : ∀ {Δ₂ : TyCtx} {m : Machine}, Sim C Δ τ m → wtProg Δ e = some Δ₂ →
        StmtOut C Δ₂ (Prog.run τ e) (run (compileProg e) m) m := fun hm hw => prog_sim e hm hw
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
  | .require c, Δ, Δ', τ, m, hm, hw => by
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
  | .assert c, Δ, Δ', τ, m, hm, hw => by
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
  | .revert, Δ, Δ', τ, m, hm, hw => .inr ⟨rfl, rfl⟩
  | .assign _ (.copy ..), _, _, _, _, _, hw => by simp [wtStmt] at hw
  | .rebind _ (.push ..), _, _, _, _, _, hw => by simp [wtStmt] at hw
  | .declStorage _ _ (some (.push ..)), _, _, _, _, _, hw => by simp [wtStmt] at hw
  | .incDec op _ (.local x), Δ, Δ', τ, m, hm, hw => by
    simp only [wtStmt, wtOpLoc, Bool.and_eq_true, beq_iff_eq, Option.ite_none_right_eq_some,
      Option.some.injEq] at hw
    obtain ⟨⟨rfl, hx⟩, rfl⟩ := hw
    exact bumpLocal_sim op x hm hx
  | .incDec op _ (.root rt h), Δ, Δ', τ, m, hm, hw => by
    simp only [wtStmt, wtOpLoc, opLocToLoc, Bool.and_eq_true, beq_iff_eq,
      Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨⟨rfl, hwl⟩, rfl⟩ := hw
    exact bumpStore_sim op rfl hm hwl
  | .incDec op _ (.field b f h), Δ, Δ', τ, m, hm, hw => by
    simp only [wtStmt, wtOpLoc, opLocToLoc, Bool.and_eq_true, beq_iff_eq,
      Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨⟨rfl, hwl⟩, rfl⟩ := hw
    exact bumpStore_sim op rfl hm hwl
  | .incDec op _ (.index it b i), Δ, Δ', τ, m, hm, hw => by
    simp only [wtStmt, wtOpLoc, opLocToLoc, Bool.and_eq_true, beq_iff_eq,
      Option.ite_none_right_eq_some, Option.some.injEq] at hw
    obtain ⟨⟨rfl, hwl⟩, rfl⟩ := hw
    exact bumpStore_sim op rfl hm hwl
  | .incDec _ _ (.mfield ..), _, _, _, _, _, hw => by simp [wtStmt, wtOpLoc, opLocToLoc] at hw
  | .incDec _ _ (.mindex ..), _, _, _, _, _, hw => by simp [wtStmt, wtOpLoc, opLocToLoc] at hw
  | .assignIncDec .., _, _, _, _, _, hw => by simp [wtStmt] at hw
  | .push .., _, _, _, _, _, hw => by simp [wtStmt] at hw
  | .declMem .., _, _, _, _, _, hw => by simp [wtStmt] at hw
  | .rebindMem .., _, _, _, _, _, hw => by simp [wtStmt] at hw
  | .assignFromMem .., _, _, _, _, _, hw => by simp [wtStmt] at hw
  | .assignMem .., _, _, _, _, _, hw => by simp [wtStmt] at hw

/-- A block's code does what the block does. -/
theorem prog_sim : ∀ (P : List (Stmt C)) {Δ Δ' : TyCtx} {τ : State} {m : Machine}, Sim C Δ τ m →
    wtProg Δ P = some Δ' → StmtOut C Δ' (Prog.run τ P) (run (compileProg P) m) m
  | [], Δ, Δ', τ, m, hm, hw => by
    simp only [wtProg, Option.some.injEq] at hw
    subst hw
    exact .inl ⟨τ, m, rfl, rfl, rfl, hm⟩
  | s :: P, Δ, Δ', τ, m, hm, hw => by
    have ihs : ∀ {Δ₁ : TyCtx} {m : Machine}, Sim C Δ τ m → wtStmt Δ s = some Δ₁ →
        StmtOut C Δ₁ (s.run τ) (run (compileStmt s) m) m := fun hm hw => stmt_sim s hm hw
    have ihP : ∀ {Δ₁ Δ₂ : TyCtx} {τ₁ : State} {m : Machine}, Sim C Δ₁ τ₁ m →
        wtProg Δ₁ P = some Δ₂ → StmtOut C Δ₂ (Prog.run τ₁ P) (run (compileProg P) m) m :=
      fun hm hw => prog_sim P hm hw
    simp only [wtProg] at hw
    split at hw
    · rename_i Δ₁ hs
      simp only [Prog.run, compileProg]
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
    (hP : wtProg Γ P = some Γ') (hm : Sim C Γ σ m) :
    (∃ σ' m', Prog.run σ P = .ok σ' ∧ run (compileProg P) m = .ok m' 0 ∧ m'.stack = m.stack ∧
      Sim C Γ' σ' m') ∨
    (Prog.run σ P = .error .revert ∧ run (compileProg P) m = .revert) :=
  prog_sim P hm hP

/-- The interpreter is never stuck on the fragment: `wtProg` is a type system
for it.

Example: `x = 1;` with `x` never declared is stuck in the interpreter, and
`wtProg` rejects it (`x` is not in the context). -/
theorem not_stuck {P : Prog C} {Γ Γ' : TyCtx} {σ : State} {m : Machine}
    (hP : wtProg Γ P = some Γ') (hm : Sim C Γ σ m) : Prog.run σ P ≠ .error .stuck := by
  rcases compile_correct hP hm with ⟨_, _, h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nofun

/-- A fresh contract: its storage at every type's default, nothing bound,
nothing sent, `balance` in funds. -/
def State.fresh (C : Contract) (balance : Nat) : State :=
  { storage := C.initStorage, selfBalance := balance }

/-- A fresh machine represents a fresh contract: every slot `0`. -/
theorem Sim.init (C : Contract) (balance : Nat) :
    Sim C (fun _ => none) (State.fresh C balance) (Machine.init balance) :=
  ⟨initStorage_repr C, fun _ _ h => (by cases h), fun _ _ h => (by cases h), rfl,
    fun _ _ => by simp [State.getNet, State.fresh, lookupBy, Machine.init]⟩

/-- **The EVM agrees with the interpreter's storage.**  From a fresh contract,
a program of the fragment either reverts in both, or runs in both, and then
every `uint` path the interpreter reads, the machine holds at its slot.

Example: `alice.age = 10;` leaves `10` at slot `13` of `StandardExample`
(`Evm/Examples.lean` derives it from this theorem). -/
theorem compile_storage {P : Prog C} {Γ' : TyCtx} (hP : wtProg (fun _ => none) P = some Γ')
    (balance : Nat) :
    (∃ σ' m', Prog.run (State.fresh C balance) P = .ok σ' ∧
      run (compileProg P) (Machine.init balance) = .ok m' 0 ∧
      ∀ r segs s n, PathSlot C false r segs (.prim .uint) s →
        σ'.findStorage r segs = .ok (.prim (.int n)) → m'.store s = n.toNat) ∨
    (Prog.run (State.fresh C balance) P = .error .revert ∧
      run (compileProg P) (Machine.init balance) = .revert) := by
  rcases compile_correct hP (Sim.init C balance) with ⟨σ', m', h1, h2, _, hm⟩ | h
  · refine .inl ⟨σ', m', h1, h2, fun r segs s n hp hf => ?_⟩
    rcases find_repr hm.store hp with ⟨sv, hsv, hr⟩ | ⟨_, hsv⟩
    · rw [hf] at hsv; cases hsv
      cases hr with
      | uint _ _ h => exact h
    · rw [hf] at hsv; cases hsv
  · exact .inr h

end Evm
end Solidity
