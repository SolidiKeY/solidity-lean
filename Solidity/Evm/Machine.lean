import Solidity.Semantics

/-!
# An EVM-style stack machine

The target of `Evm/Compile.lean`: mini-solkey's `Ch08_EVM` machine with the
control flow, the arithmetic and the value transfer the typed fragment
needs.  Instruction meanings follow the EVM as Nethermind's
[EVMYulLean](https://github.com/NethermindEth/EVMYulLean) formalises it:

* arithmetic words are numbers below `2^256` and `ADD`/`SUB`/`MUL` wrap;
  `DIV a 0 = MOD a 0 = 0`;
* `LT`/`GT`/`EQ`/`ISZERO` push `1` or `0`; `OR`, `AND`, `XOR` and `NOT` are
  bitwise; `SHL`/`SHR` take the shift on top and give `0` from `256` on;
  `EXP` takes the base on top and wraps;
* `SLT`/`SGT`/`SDIV`/`SMOD` read words as two's complement (`sgn`):
  `SDIV` truncates (and `-2^255 / -1` wraps to `-2^255`), `SMOD` takes the
  dividend's sign, both give `0` on a zero divisor;
* `DUP n` copies the `n`-th item, `SWAP n` swaps the top with the `(n+1)`-th;
* `SLOAD`/`SSTORE` read and write storage, and a fresh contract's storage is
  all zeroes;
* `JUMPI` jumps iff the popped word is non-zero, `REVERT` aborts;
* `CALL` fails and pushes `0` when the contract cannot cover the value or
  the recipient refuses it (`accepts`), else moves the value from the
  contract's account to the recipient's and pushes `1` (solc's `transfer`
  reverts on the `0`); a payment to the contract itself moves nothing.

**What is simplified, on purpose.**

* **A storage slot is a term, not a number** (mini-solkey's choice):
  `root off` for the contract's own slots, `hash k s off` for
  `keccak256(k ‖ s) + off` (a mapping entry), `data s off` for
  `keccak256(s) + off` (an array's elements).  Two slots are equal only if
  they are the same term, so keccak never collides: the assumption solc makes,
  written into the type.  Adding to a slot adds to its offset, unbounded.
* **Jumps are relative and forward**: `JUMP n`/`JUMPI n` skip the next `n`
  instructions.  The fragment has no loops, so no backward jump is needed, and
  `exec` is structural: it carries the number of instructions still to skip.
  Absolute targets with `JUMPDEST` are an assembler's business.  The one loop
  solc emits for the fragment, `checked_exp_helper`'s, runs at most `255`
  times and is unrolled (`expLoop`, `Compile.lean`).
* `KECCAK256` takes its inputs from the stack (real code first `MSTORE`s them),
  in two forms: `keccakMap` for a mapping entry, `keccakArr` for array data.
* **Locals live in memory**, one cell per variable, addressed by the variable
  itself (as Vyper does); solc keeps them on the stack.
* **The world is the accounts' balances** (the Yellow Paper's `σ[a].b`):
  `bal a` for every address `a`, the contract's own at `self`
  (`SELFBALANCE` reads it).  There is no ledger: KeY's `net` is a ghost of
  the interpreter, related to how the balances moved since the transaction
  began, `bal₀` (`Sim.net`, `Evm/Correctness.lean`).  A recipient's code is
  not run; whether it accepts a payment is `accepts`, which no instruction
  changes, and the compiler theorem holds for every one.  `caller`,
  `callvalue`, `timestamp` are the transaction's (`CALLER`, `CALLVALUE`,
  `TIMESTAMP`).  `CALL` takes only an address and a value — no gas, no
  calldata — and an address is a word, not cut to 160 bits.
* No gas, no stack-depth limit.
-/

namespace Solidity
namespace Evm

/-- `2^256`: words are the numbers below it. -/
def W : Nat := 2 ^ 256

/-- Words are not empty: `0` is a word. -/
theorem W_pos : 0 < W := Nat.pow_pos (by decide)

/-- `2^255`: an `int256` is in `[-2^255, 2^255)`, and a word at or above it
reads as negative. -/
def H : Nat := 2 ^ 255

/-- A word is two halves: `2^256 = 2 · 2^255`. -/
theorem W_eq : W = 2 * H := by unfold W H; rw [Nat.pow_succ, Nat.mul_comm]

/-- The signed reading of a word, two's complement: `2^256 - 1` is `-1`. -/
def sgn (a : Nat) : Int := if a < H then (a : Int) else (a : Int) - W

/-- The word of an integer in `[-2^256, 2^256)`, two's complement: `-1` is
`2^256 - 1`. -/
def toWord (n : Int) : Nat := if 0 ≤ n then n.toNat else (n + W).toNat

/-- `0` reads as `0`. -/
@[simp] theorem sgn_zero : sgn 0 = 0 := by simp [sgn, H]

/-- solc's maximum length of a storage array, `2^64` (`push` reverts at it
with `Panic(0x41)`). -/
def Lmax : Nat := 2 ^ 64

/-- The array bound is below the word bound. -/
theorem Lmax_lt_W : Lmax < W := by unfold Lmax W; decide

/-- A storage slot: `root off`, `keccak256(k ‖ s) + off`, or `keccak256(s) + off`. -/
inductive Slot where
  | root (off : Nat)
  | hash (k : Nat) (s : Slot) (off : Nat)
  | data (s : Slot) (off : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Adding to a slot adds to its offset. -/
def Slot.add : Slot → Nat → Slot
  | .root o, i => .root (o + i)
  | .hash k s o, i => .hash k s (o + i)
  | .data s o, i => .data s (o + i)

def Slot.toStr : Slot → String
  | .root o => toString o
  | .hash k s 0 => s!"keccak({k}, {s.toStr})"
  | .hash k s o => s!"keccak({k}, {s.toStr}) + {o}"
  | .data s 0 => s!"keccak({s.toStr})"
  | .data s o => s!"keccak({s.toStr}) + {o}"

instance : ToString Slot := ⟨Slot.toStr⟩

/-- A stack or memory word: a number or a slot. -/
inductive Word where
  | val (n : Nat)
  | slot (s : Slot)
  deriving DecidableEq, Repr, Inhabited

instance : ToString Word where
  toString
    | .val n => toString n
    | .slot s => s!"@{s}"

/-- A comparison's result word. -/
def bword (b : Bool) : Nat := if b then 1 else 0

inductive Instr where
  | push (w : Word)
  | pop
  | dup (n : Nat)
  | swap (n : Nat)
  | add | sub | mul | div | mod
  | lt | gt | eq | iszero | or | and
  /-- The signed comparisons and division: `SLT`, `SGT`, `SDIV`, `SMOD`. -/
  | slt | sgt | sdiv | smod
  | keccakMap
  | keccakArr
  | sload
  | sstore
  | mload (x : Var)
  | mstore (x : Var)
  | jump (n : Nat)
  | jumpi (n : Nat)
  | call
  | revert
  /-- The bitwise and exponentiation opcodes of the `uint` operators with no
  overflow check: `XOR`, `NOT`, `SHL`, `SHR`, `EXP`. -/
  | xor | not | shl | shr | exp
  /-- The transaction's environment: `CALLER` (`msg.sender`), `CALLVALUE`
  (`msg.value`), `TIMESTAMP` (`block.timestamp`), `SELFBALANCE`
  (`address(this).balance`). -/
  | caller | callvalue | timestamp | selfbalance
  deriving DecidableEq, Repr, Inhabited

instance : ToString Instr where
  toString
    | .push w => s!"PUSH {w}"
    | .pop => "POP"
    | .dup n => s!"DUP{n}"
    | .swap n => s!"SWAP{n}"
    | .add => "ADD" | .sub => "SUB" | .mul => "MUL" | .div => "DIV" | .mod => "MOD"
    | .lt => "LT" | .gt => "GT" | .eq => "EQ" | .iszero => "ISZERO" | .or => "OR"
    | .and => "AND" | .slt => "SLT" | .sgt => "SGT" | .sdiv => "SDIV" | .smod => "SMOD"
    | .keccakMap => "KECCAK256" | .keccakArr => "KECCAK256"
    | .sload => "SLOAD"
    | .sstore => "SSTORE"
    | .mload x => s!"MLOAD {x}"
    | .mstore x => s!"MSTORE {x}"
    | .jump n => s!"JUMP +{n}"
    | .jumpi n => s!"JUMPI +{n}"
    | .call => "CALL"
    | .revert => "REVERT"
    | .xor => "XOR" | .not => "NOT" | .shl => "SHL" | .shr => "SHR" | .exp => "EXP"
    | .caller => "CALLER" | .callvalue => "CALLVALUE" | .timestamp => "TIMESTAMP"
    | .selfbalance => "SELFBALANCE"

/-- `f` with `x` sent to `v`. -/
def upd {α : Type} {β : Type} [DecidableEq α] (f : α → β) (x : α) (v : β) : α → β :=
  fun y => if y = x then v else f y

/-- A cell just written holds what was written: `MSTORE x` then `MLOAD x`. -/
@[simp] theorem upd_same {α β : Type} [DecidableEq α] (f : α → β) (x : α) (v : β) :
    upd f x v x = v := by simp [upd]

/-- Writing one cell leaves the others: `SSTORE` at `alice.age` leaves `bob.age`. -/
theorem upd_other {α β : Type} [DecidableEq α] (f : α → β) {x y : α} (v : β) (h : y ≠ x) :
    upd f x v y = f y := by simp [upd, h]

structure Machine where
  stack : List Word
  store : Slot → Nat
  mem : Var → Word
  /-- Every account's balance. -/
  bal : Nat → Nat
  /-- The balances when the transaction began: a ghost, which no
  instruction reads or writes. -/
  bal₀ : Nat → Nat
  /-- The contract's own address. -/
  self : Nat := 0
  /-- Whether the account at `a` accepts a payment of `v`: one whose code
  reverts, or runs out of the 2300 gas `transfer` forwards, does not. -/
  accepts : Nat → Nat → Bool := fun _ _ => true
  /-- The transaction's sender, value and block time, as `CALLER`,
  `CALLVALUE`, `TIMESTAMP` push them. -/
  caller : Nat := 0
  callvalue : Nat := 0
  timestamp : Nat := 0

/-- A fresh contract at `self` in a world whose balances are `bal`: empty
stack, storage and memory all zeroes, nothing moved yet, called by `0` with
nothing at time `0`, every payment accepted. -/
def Machine.init (bal : Nat → Nat := fun _ => 0) (self : Nat := 0) : Machine :=
  { stack := [], store := fun _ => 0, mem := fun _ => .val 0, bal, bal₀ := bal, self }

/-- `v` moved from `s`'s account to `a`'s, another. -/
def pay (bal : Nat → Nat) (s a v : Nat) : Nat → Nat :=
  upd (upd bal s (bal s - v)) a (bal a + v)

section Ledger
open Semantics

/-- The addresses KeY's ledger is compared at, against the balances: the words,
but the contract's own. -/
def Payee (self : Nat) (a : Int) : Prop := 0 ≤ a ∧ a < W ∧ a ≠ self

instance (self : Nat) : DecidablePred (Payee self) := fun _ => by unfold Payee; infer_instance

/-- What the ledger `l` sums over the addresses `p` admits, each once, at its
first entry, where `lookupBy` reads it. -/
def netSum (p : Int → Prop) [DecidablePred p] : List (Int × Int) → Int
  | [] => 0
  | (a, n) :: l => (if p a then n else 0) + netSum (fun b => p b ∧ b ≠ a) l

/-- Booking `v` at `k` changes the sum by the change at `k`, if `p` admits it. -/
theorem netSum_setBy (k v : Int) : ∀ (l : List (Int × Int)) (p : Int → Prop) [DecidablePred p],
    netSum p (setBy k v l) = netSum p l + (if p k then v - (lookupBy k l).getD 0 else 0)
  | [], p, _ => by simp only [setBy, netSum, lookupBy, Option.getD_none]; split <;> omega
  | (a, n) :: l, p, _ => by
    simp only [setBy]
    by_cases hk : k = a
    · subst hk
      simp only [if_true, netSum, lookupBy, Option.getD_some]
      split <;> omega
    · simp only [hk, if_false, netSum, lookupBy]
      rw [netSum_setBy k v l]
      by_cases hp : p k <;> simp only [hp, hk, ne_eq, not_false_eq_true, and_self, and_true,
        if_true, if_false] <;> omega

end Ledger

def Machine.push (m : Machine) (w : Word) : Machine := { m with stack := w :: m.stack }

/-- A run's outcome: a machine and the number of instructions still to skip
(a pending jump), a `REVERT`, or a fault (stack underflow, a word of the wrong
kind) — which compiled code of the fragment never reaches. -/
inductive Out where
  | ok (m : Machine) (skip : Nat)
  | revert
  | fault

def Out.bind : Out → (Machine → Nat → Out) → Out
  | .ok m k, f => f m k
  | .revert, _ => .revert
  | .fault, _ => .fault

/-- A step that succeeded runs the rest: `PUSH 10` then `SSTORE`. -/
@[simp] theorem Out.ok_bind (m : Machine) (k : Nat) (f : Machine → Nat → Out) :
    (Out.ok m k).bind f = f m k := rfl
/-- After `REVERT` nothing runs: `require(false); total = 1;`. -/
@[simp] theorem Out.revert_bind (f : Machine → Nat → Out) : Out.revert.bind f = .revert := rfl
/-- After a fault nothing runs (compiled code never faults). -/
@[simp] theorem Out.fault_bind (f : Machine → Nat → Out) : Out.fault.bind f = .fault := rfl

/-- Running three pieces is running the first, then the other two: `a; b; c;`. -/
theorem Out.bind_assoc (o : Out) (f g : Machine → Nat → Out) :
    (o.bind f).bind g = o.bind (fun m k => (f m k).bind g) := by
  cases o <;> rfl

/-- One step with the stack's top replaced: `ok` with nothing to skip. -/
@[inline] def Machine.next (m : Machine) (st : List Word) : Out := .ok { m with stack := st } 0

/-- One instruction. -/
def Instr.step : Instr → Machine → Out
  | .push w, m => m.next (w :: m.stack)
  | .pop, m => match m.stack with
    | _ :: st => m.next st
    | [] => .fault
  | .dup n, m => match n, m.stack[n - 1]? with
    | 0, _ => .fault
    | _, some w => m.next (w :: m.stack)
    | _, none => .fault
  | .swap n, m => match n, m.stack with
    | 0, _ => .fault
    | n + 1, a :: st => match st[n]? with
      | some b => m.next (b :: st.set n a)
      | none => .fault
    | _, [] => .fault
  | .add, m => match m.stack with
    | .val a :: .val b :: st => m.next (.val ((a + b) % W) :: st)
    | .val i :: .slot s :: st => m.next (.slot (s.add i) :: st)
    | .slot s :: .val i :: st => m.next (.slot (s.add i) :: st)
    | _ => .fault
  | .sub, m => match m.stack with
    | .val a :: .val b :: st => m.next (.val ((a + (W - b)) % W) :: st)
    | _ => .fault
  | .mul, m => match m.stack with
    | .val a :: .val b :: st => m.next (.val (a * b % W) :: st)
    | _ => .fault
  | .div, m => match m.stack with
    | .val a :: .val b :: st => m.next (.val (if b = 0 then 0 else a / b) :: st)
    | _ => .fault
  | .mod, m => match m.stack with
    | .val a :: .val b :: st => m.next (.val (if b = 0 then 0 else a % b) :: st)
    | _ => .fault
  | .lt, m => match m.stack with
    | .val a :: .val b :: st => m.next (.val (bword (decide (a < b))) :: st)
    | _ => .fault
  | .gt, m => match m.stack with
    | .val a :: .val b :: st => m.next (.val (bword (decide (b < a))) :: st)
    | _ => .fault
  | .eq, m => match m.stack with
    | .val a :: .val b :: st => m.next (.val (bword (decide (a = b))) :: st)
    | _ => .fault
  | .iszero, m => match m.stack with
    | .val a :: st => m.next (.val (bword (decide (a = 0))) :: st)
    | _ => .fault
  | .or, m => match m.stack with
    | .val a :: .val b :: st => m.next (.val (a ||| b) :: st)
    | _ => .fault
  | .and, m => match m.stack with
    | .val a :: .val b :: st => m.next (.val (a &&& b) :: st)
    | _ => .fault
  | .slt, m => match m.stack with
    | .val a :: .val b :: st => m.next (.val (bword (decide (sgn a < sgn b))) :: st)
    | _ => .fault
  | .sgt, m => match m.stack with
    | .val a :: .val b :: st => m.next (.val (bword (decide (sgn b < sgn a))) :: st)
    | _ => .fault
  | .sdiv, m => match m.stack with
    | .val a :: .val b :: st =>
      m.next (.val (if b = 0 then 0 else toWord (Int.tdiv (sgn a) (sgn b))) :: st)
    | _ => .fault
  | .smod, m => match m.stack with
    | .val a :: .val b :: st =>
      m.next (.val (if b = 0 then 0 else toWord (Int.tmod (sgn a) (sgn b))) :: st)
    | _ => .fault
  | .keccakMap, m => match m.stack with
    | .val k :: .slot s :: st => m.next (.slot (.hash k s 0) :: st)
    | _ => .fault
  | .keccakArr, m => match m.stack with
    | .slot s :: st => m.next (.slot (.data s 0) :: st)
    | _ => .fault
  | .sload, m => match m.stack with
    | .slot s :: st => m.next (.val (m.store s) :: st)
    | _ => .fault
  | .sstore, m => match m.stack with
    | .slot s :: .val v :: st => .ok { m with stack := st, store := upd m.store s v } 0
    | _ => .fault
  | .mload x, m => m.next (m.mem x :: m.stack)
  | .mstore x, m => match m.stack with
    | w :: st => .ok { m with stack := st, mem := upd m.mem x w } 0
    | [] => .fault
  | .jump n, m => .ok m n
  | .jumpi n, m => match m.stack with
    | .val c :: st => .ok { m with stack := st } (if c = 0 then 0 else n)
    | _ => .fault
  | .call, m => match m.stack with
    | .val v :: .val a :: st =>
      if m.bal m.self < v ∨ m.accepts a v = false then m.next (.val 0 :: st)
      else if a = m.self then m.next (.val 1 :: st)
      else .ok { m with stack := .val 1 :: st, bal := pay m.bal m.self a v } 0
    | _ => .fault
  | .revert, _ => .revert
  | .xor, m => match m.stack with
    | .val a :: .val b :: st => m.next (.val (a ^^^ b) :: st)
    | _ => .fault
  | .not, m => match m.stack with
    | .val a :: st => m.next (.val (W - 1 - a) :: st)
    | _ => .fault
  | .shl, m => match m.stack with
    | .val n :: .val a :: st => m.next (.val (if n < 256 then a * 2 ^ n % W else 0) :: st)
    | _ => .fault
  | .shr, m => match m.stack with
    | .val n :: .val a :: st => m.next (.val (if n < 256 then a / 2 ^ n else 0) :: st)
    | _ => .fault
  | .exp, m => match m.stack with
    | .val a :: .val b :: st => m.next (.val (a ^ b % W) :: st)
    | _ => .fault
  | .caller, m => m.next (.val m.caller :: m.stack)
  | .callvalue, m => m.next (.val m.callvalue :: m.stack)
  | .timestamp, m => m.next (.val m.timestamp :: m.stack)
  | .selfbalance, m => m.next (.val (m.bal m.self) :: m.stack)

/-- Run code, skipping `k` instructions first (a jump still pending). -/
def exec : List Instr → Nat → Machine → Out
  | [], k, m => .ok m k
  | _ :: c, k + 1, m => exec c k m
  | i :: c, 0, m => (i.step m).bind (fun m' k' => exec c k' m')

/-- Run code from its first instruction. -/
def run (c : List Instr) (m : Machine) : Out := exec c 0 m

/-- At the end of the code the machine stops, with any pending skip: the end of an `if`. -/
@[simp] theorem exec_nil (k : Nat) (m : Machine) : exec [] k m = .ok m k := rfl
/-- A pending jump skips one instruction: `JUMPI +2` over `PUSH 1; SSTORE`. -/
@[simp] theorem exec_cons_succ (i : Instr) (c : List Instr) (k : Nat) (m : Machine) :
    exec (i :: c) (k + 1) m = exec c k m := rfl
/-- With nothing to skip the next instruction runs: `PUSH 10`. -/
@[simp] theorem exec_cons_zero (i : Instr) (c : List Instr) (m : Machine) :
    exec (i :: c) 0 m = (i.step m).bind (fun m' k' => exec c k' m') := rfl

/-- Running two pieces of code in sequence is running their concatenation,
and a jump still pending at the end of the first skips into the second.

Example: `total = 3; age = 4;` compiles to the code of `total = 3;` followed
by that of `age = 4;`, so it runs as the first, then the second on the machine
the first leaves; `if (c) { total = 3; }`'s `JUMPI` skips over the branch
into whatever follows it. -/
theorem exec_append (c₁ c₂ : List Instr) (k : Nat) (m : Machine) :
    exec (c₁ ++ c₂) k m = (exec c₁ k m).bind (fun m' k' => exec c₂ k' m') := by
  induction c₁ generalizing k m with
  | nil => rfl
  | cons i c ih =>
    cases k with
    | succ k => exact ih k m
    | zero =>
      simp only [List.cons_append, exec_cons_zero, Out.bind_assoc]
      congr 1; funext m' k'; exact ih k' m'

/-- Skipping as many instructions as the code has jumps over all of it.

Example: in `if (c) { total = 3; } else { age = 4; }` the `JUMP` at the end of
the `then` branch skips exactly the code of the `else` branch. -/
theorem exec_skip (c : List Instr) (k : Nat) (m : Machine) :
    exec c (c.length + k) m = .ok m k := by
  induction c with
  | nil => simp
  | cons i c ih => rw [List.length_cons, Nat.add_right_comm]; exact ih

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

end Evm
end Solidity
