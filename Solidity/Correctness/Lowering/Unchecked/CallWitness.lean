import Solidity.Syntax.Splice
import Solidity.Semantics.Run

/-!
# An elaborated unchecked caller with a checked callee

Guards unchecked-mode leakage from a caller into an internal function. This
control uses the actual quotation elaborator and the emitted intrinsic run,
not a hand-built replacement program. The caller starts one below the largest
uint256; its unchecked increment reaches the maximum, then the callee's
checked addition must fail. The bare intrinsic run reports `.revert`, not
the full Source panic bytes; this witness does not identify those outcomes. This finite model witness does not prove Source
agreement, general validator soundness, or either solc pipeline's behaviour.
-/
namespace Solidity.Correctness.Lowering.Unchecked.CallWitness

/-- The addition belongs to the callee, outside the caller's unchecked block. -/
def Example : Contract := contract!{
  function f(uint x) returns (uint r) { r = x + 1; }
}

/-- The assigned worked example, elaborated by the production entry point. -/
def emitted := sol[Example]{
  uint x = 115792089237316195423570985008687907853269984665640564039457584007913129639934;
  unchecked { x++; f(x); };
}

/-- Exercises checked addition in a callee reached from an unchecked caller.
The initial increment does not overflow, so this control does not test caller
wrapping itself. The final halt alone does not localize an arbitrary failure. -/
theorem checkedCallee_reverts :
    (Prog.run (State.init Example) emitted).halt? = some .revert := by
  rfl

#print axioms checkedCallee_reverts

end Solidity.Correctness.Lowering.Unchecked.CallWitness
