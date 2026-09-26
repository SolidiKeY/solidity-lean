import Solidity.Semantics

/-!
# An EVM-style stack machine

The target of `Evm/Compile.lean`: mini-solkey's `Ch08_EVM` machine with the
control flow, the arithmetic and the value transfer the typed fragment
needs.  Instruction meanings follow the EVM as Nethermind's
[EVMYulLean](https://github.com/NethermindEth/EVMYulLean) formalises it:

* arithmetic words are numbers below `2^256` and `ADD`/`SUB`/`MUL` wrap;
  `DIV a 0 = MOD a 0 = 0`;
* `LT`/`GT`/`EQ`/`ISZERO` push `1` or `0`; `OR` is bitwise;
* `DUP n` copies the `n`-th item, `SWAP n` swaps the top with the `(n+1)`-th;
* `SLOAD`/`SSTORE` read and write storage, and a fresh contract's storage is
  all zeroes;
* `JUMPI` jumps iff the popped word is non-zero, `REVERT` aborts;
* `CALL` with a value the contract cannot cover fails and pushes `0`, else
  moves the value and pushes `1` (solc's `transfer` reverts on the `0`).

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
  Absolute targets with `JUMPDEST` are an assembler's business.
* `KECCAK256` takes its inputs from the stack (real code first `MSTORE`s them),
  in two forms: `keccakMap` for a mapping entry, `keccakArr` for array data.
* **Locals live in memory**, one cell per variable, addressed by the variable
  itself (as Vyper does); solc keeps them on the stack.
* **The world is one ledger**: `net a` is what KeY's `net` records for address
  `a`, the value the contract has sent there, negated; `balance` is
  `address(this).balance`.  `CALL` takes only an address and a value — no gas,
  no calldata, no callee code.
* No gas, no stack-depth limit.
-/

namespace Solidity
namespace Evm

/-- `2^256`: words are the numbers below it. -/
def W : Nat := 2 ^ 256

/-- Words are not empty: `0` is a word. -/
theorem W_pos : 0 < W := Nat.pow_pos (by decide)

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
  | lt | gt | eq | iszero | or
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
  deriving DecidableEq, Repr, Inhabited

instance : ToString Instr where
  toString
    | .push w => s!"PUSH {w}"
    | .pop => "POP"
    | .dup n => s!"DUP{n}"
    | .swap n => s!"SWAP{n}"
    | .add => "ADD" | .sub => "SUB" | .mul => "MUL" | .div => "DIV" | .mod => "MOD"
    | .lt => "LT" | .gt => "GT" | .eq => "EQ" | .iszero => "ISZERO" | .or => "OR"
    | .keccakMap => "KECCAK256" | .keccakArr => "KECCAK256"
    | .sload => "SLOAD"
    | .sstore => "SSTORE"
    | .mload x => s!"MLOAD {x}"
    | .mstore x => s!"MSTORE {x}"
    | .jump n => s!"JUMP +{n}"
    | .jumpi n => s!"JUMPI +{n}"
    | .call => "CALL"
    | .revert => "REVERT"

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
  balance : Nat
  net : Nat → Int

/-- A fresh contract holding `balance`: empty stack, storage and memory all
zeroes, nothing sent anywhere. -/
def Machine.init (balance : Nat := 0) : Machine :=
  ⟨[], fun _ => 0, fun _ => .val 0, balance, fun _ => 0⟩

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
      if m.balance < v then m.next (.val 0 :: st)
      else .ok { m with stack := .val 1 :: st, balance := m.balance - v,
                        net := upd m.net a (m.net a - v) } 0
    | _ => .fault
  | .revert, _ => .revert

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

end Evm
end Solidity
