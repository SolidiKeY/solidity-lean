import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.Close
import Solidity.Calculus.SolkeyFragment
import Solidity.Syntax.Splice

/-!
# Native modular arithmetic

Intermediate sums and products are unbounded. Zero modulus uses the model's
arithmetic-failure result; the frozen upstream calculus has no native rule.
-/

namespace Solidity.Examples.Tactics.ModularArithmetic

open Semantics
open scoped Scoped

local instance : InContract := ⟨StandardExample⟩

private def initial : State StandardExample [] := State.ofStorage Storage.standardExample

private def basic : Prog StandardExample [] [] := sol{
  assert(addmod(10, 5, 7) == 1);
  assert(mulmod(3, 5, 7) == 1);
  assert(addmod(115792089237316195423570985008687907853269984665640564039457584007913129639935, 1, 3) == 1);
  assert(mulmod(57896044618658097711785492504343953926634992332820282019728792003956564819968, 2, 3) == 1);
}

example : (Prog.run initial basic).toOption.isSome = true := by decide +kernel

example : ⊢ dl!{ ⟨
  assert(addmod(10, 5, 7) == 1);
  assert(mulmod(3, 5, 7) == 1);
  assert(addmod(115792089237316195423570985008687907853269984665640564039457584007913129639935, 1, 3) == 1);
  assert(mulmod(57896044618658097711785492504343953926634992332820282019728792003956564819968, 2, 3) == 1);
⟩ true } := by
  sol_prove (steps := 256)

private def zeroAdd := sol[StandardExample]{
  uint k = 0; uint r = addmod(10, 5, k);
}
private def zeroMul := sol[StandardExample]{
  uint k = 0; uint r = mulmod(10, 5, k);
}
private def zeroDiscarded := sol[StandardExample]{
  uint k = 0; addmod(10, 5, k);
}

example : (Prog.run initial zeroAdd).halt? = some .revert := by decide +kernel
example : (Prog.run initial zeroMul).halt? = some .revert := by decide +kernel
example : (Prog.run initial zeroDiscarded).halt? = some .revert := by decide +kernel

private def short := sol[StandardExample]{
  uint k = 0;
  assert(true || addmod(1, 2, k) == 0);
  assert(!(false && mulmod(1, 2, k) == 0));
  uint r = true ? 9 : addmod(1, 2, k);
  assert(r == 9);
}
example : (Prog.run initial short).toOption.isSome = true := by decide +kernel

/-- Legacy codegen evaluates the arguments right to left. -/
private def ordered := sol[StandardExample]{
  uint i = 3; uint r = addmod(i++, i++, i++); assert(i == 6); assert(r == 0);
}
example : (Prog.run initial ordered).toOption.isSome = true := by decide +kernel

/-- A pure read of the modulus must be saved before another argument changes it. -/
private def captured := sol[StandardExample]{
  uint i = 3; uint r = addmod(i++, 2, i); assert(i == 4); assert(r == 2);
}
example : (Prog.run initial captured).toOption.isSome = true := by decide +kernel

private def falseAssertion := sol[StandardExample]{ assert(mulmod(3, 5, 7) == 2); }
example : (Prog.run initial falseAssertion).toOption.isNone = true := by decide +kernel

/- Nested values, declarations, paths and branches are outside the stable fragment. -/
#guard basic.inSolkey .box == false
#guard (sol[StandardExample]{ uint x = 1 + addmod(10, 5, 7); }).inSolkey .box == false
#guard (sol[StandardExample]{ balances[addmod(10, 5, 7)] = 2; }).inSolkey .box == false
#guard (sol[StandardExample]{ balances[addmod(10, 5, 7)] += 2; }).inSolkey .box == false
#guard (sol[StandardExample]{ balances[addmod(10, 5, 7)]++; }).inSolkey .box == false
#guard (sol[StandardExample]{ if (true) { uint x = mulmod(3, 5, 7); }; }).inSolkey .box == false
#guard (sol[StandardExample]{ uint x = 1 + 2; balances[x] = 2; }).inSolkey .box

/-- error: Solidity elaboration failed: addmod takes three uint arguments -/
#guard_msgs in
#check sol[StandardExample]{ uint r = addmod(1, 2); }

/-- error: Solidity elaboration failed: a bool where a uint is expected -/
#guard_msgs in
#check sol[StandardExample]{ uint r = mulmod(true, 2, 3); }

/-- error: Solidity elaboration failed: addmod: arithmetic modulo zero -/
#guard_msgs in
#check sol[StandardExample]{ uint i = 1; uint r = addmod(i++, 2, 0); }

/-- error: Solidity elaboration failed: mulmod: arithmetic modulo zero -/
#guard_msgs in
#check sol[StandardExample]{ uint i = 1; mulmod(i++, 2, 0); }

namespace FailurePriority

def C : Contract := contract!{
  function bad() returns (uint) { assert(false); return 1; }
}

private def add := sol[C]{ uint k = 0; uint r = addmod(bad(), 2, k); }
private def mul := sol[C]{ uint k = 0; uint r = mulmod(1, bad(), k); }
private def positive := sol[C]{ uint k = 3; uint r = addmod(bad(), 2, k); }
private def modulus := sol[C]{ uint r = mulmod(1, 2, bad()); }

/- A zero modulus suppresses the other operands' effects; a positive modulus
and the modulus expression itself still execute their failing helper. -/
example : (Prog.run (State.init C) add).halt? = some .revert := by decide +kernel
example : (Prog.run (State.init C) mul).halt? = some .revert := by decide +kernel
example : (Prog.run (State.init C) positive).halt? = some .panic := by decide +kernel
example : (Prog.run (State.init C) modulus).halt? = some .panic := by decide +kernel

end FailurePriority

namespace Shadow

def C : Contract := contract!{
  function addmod(uint a, uint b, uint k) returns (uint) { return 99; }
}

local instance : InContract := ⟨C⟩

/-- An ordinary declared function takes precedence over the builtin spelling. -/
example : ⊢ dl!{ ⟨ uint r = addmod(1, 2, 3); assert(r == 99); ⟩ true } := by
  sol_prove (steps := 128)

end Shadow
end Solidity.Examples.Tactics.ModularArithmetic
