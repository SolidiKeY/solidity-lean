import Solidity.Backend.Scalar.Casts
import Solidity.RevertBytes

/-!
# Failure-test interface for scalar slices

A test leaves a failure flag above the original operands. `guarded` is the
component boundary consumed by a future control/payload emitter: it chooses
between independently executed numeric slices and existing failure bytes.
It is not a bytecode interpreter or a proof of generic payload emission.
-/
namespace Solidity.Backend.Scalar

/-- The existing panic byte constructors remain the single data authority. -/
def divisionFailure : List UInt8 := Semantics.encodePanic 0x12
def overflowFailure : List UInt8 := Semantics.encodePanic 0x11

/-- A nonzero test result selects the supplied failure class. -/
def guarded (test body : Program) (failure : List UInt8) (st : Stack) :
    Option (Except (List UInt8) Stack) := do
  let tested ← run test st
  match tested with
  | flag :: operands =>
      if flag == 0 then (run body operands).map Except.ok else some (.error failure)
  | [] => none

/-- DUP uses its real zero-based opcode index; the tested operand is retained. -/
def zeroTest (n : Fin 16) : Program := [.op (.DUP n), .op .ISZERO]

theorem zeroTest_correct (n : Fin 16) (st : Stack) (a : Word)
    (ha : st[n.val]? = some a) :
    run (zeroTest n) st = some (flag (a == 0) :: st) := by
  simp only [zeroTest, run, step, numericStep, duplicate, ha, Option.map_some,
    unary, applyUnary, Option.bind_some]

/-- Failure and success are different observations even when the EVM body
would have returned zero at a zero divisor. -/
theorem guarded_zero (n : Fin 16) (st : Stack) (a : Word) (body : Program)
    (failure : List UInt8) (ha : st[n.val]? = some a) :
    guarded (zeroTest n) body failure st =
      if a == 0 then some (.error failure) else (run body st).map Except.ok := by
  unfold guarded
  rw [zeroTest_correct n st a ha]
  cases h : a == 0 <;> rfl

/-- Neither Panic selector is erased or confused with the other code. -/
example : divisionFailure ≠ overflowFailure := by decide +kernel
example : guarded (zeroTest ⟨1, by decide⟩) [.op .DIV] divisionFailure [7, 0, 99] =
    some (.error divisionFailure) := rfl
example : guarded (zeroTest ⟨1, by decide⟩) [.op .DIV] divisionFailure [7, 2, 99] =
    some (.ok [3, 99]) := rfl

/-- info: 'Solidity.Backend.Scalar.zeroTest_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms zeroTest_correct
/-- info: 'Solidity.Backend.Scalar.guarded_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms guarded_zero

end Solidity.Backend.Scalar
