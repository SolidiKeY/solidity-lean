import Solidity.Backend.Scalar.Slice
import Solidity.Backend.Creation.Execution

/-!
# Byte-PC execution of the numeric control-flow slice

A control layer over the exact byte fetch and
numeric instruction semantics. Words remain intrinsic BitVec256 values;
PUSH and numeric/stack effects are reused, not reimplemented. JUMPI pops
its destination and condition and tests the destination only when taken.

This gasless slice has no storage, memory, account, terminal or EVM stack-cap
semantics. `none` means no supported next step (including bad targets or
underflow), not an EVM error/revert classification. Finite iteration below
counts exact instruction steps, not gas or a source evaluation horizon.
Pinned-EVM and whole structured/source correctness are separate obligations.
-/
namespace Solidity.Backend.LabelExec

structure State where
  pc : Nat
  stack : Scalar.Stack
  deriving DecidableEq, Repr

/-- One decoded instruction's exact control effect. -/
def effect (code : List UInt8) (i : Instr) (s : State) : Option State :=
  match i, s.stack with
  | .op .JUMP, target :: tail =>
      if validJumpdest code target.toNat then some ⟨target.toNat, tail⟩ else none
  | .op .JUMPI, target :: condition :: tail =>
      if condition == 0 then some ⟨s.pc + 1, tail⟩
      else if validJumpdest code target.toNat then some ⟨target.toNat, tail⟩ else none
  | .op .JUMPDEST, _ => some ⟨s.pc + 1, s.stack⟩
  | _, _ => (Scalar.step i s.stack).map fun stack => ⟨s.pc + i.size, stack⟩

/-- Fetch at the actual byte PC, retaining the whole code for destination scan. -/
def step (code : List UInt8) (s : State) : Option State :=
  (Creation.fetch (code.drop s.pc)).bind fun (i, _) => effect code i s

/-- Exactly n supported byte steps. Zero steps do not assert termination. -/
def advance : Nat → List UInt8 → State → Option State
  | 0, _, s => some s
  | n + 1, code, s => (step code s).bind (advance n code)

end Solidity.Backend.LabelExec
