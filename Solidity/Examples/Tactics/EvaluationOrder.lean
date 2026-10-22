import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.Close
import Solidity.Frontend.Import

/-!
# Configurable expression evaluation order

The same capture machinery reads legacy and IR codegen schedules. These
runs distinguish operand sequencing without changing their argument positions.
-/

namespace Solidity.Examples.Tactics.EvaluationOrder

open Semantics
open scoped Scoped

def Legacy : Contract := contract!{
  function sum(uint a, uint b) returns (uint) { return a + b; }
  function bump(uint a) returns (uint) { return ++a + a; }
  function bad() returns (uint) { assert(false); return 1; }
}

def IR : Contract := { Legacy with evalOrder := .viaIR }

/-- The default preserves legacy's right operand read before the increment. -/
example : (Prog.run (State.init Legacy) (sol[Legacy]{
    uint i = 1; uint r = ++i + i; assert(r == 3);
  })).isOk = true := by decide +kernel

/-- IR reads the left operand first, including a read held before a later effect. -/
example : (Prog.run (State.init IR) (sol[IR]{
    uint i = 1; uint r = ++i + i; assert(r == 4);
    uint s = i + ++i; assert(s == 5);
    uint t = ++i - i++; assert(t == 0);
    assert(i == 5);
  })).isOk = true := by decide +kernel

/-- The schedule reaches inlined bodies and arguments with nested expressions. -/
example : (Prog.run (State.init IR) (sol[IR]{
    uint i = 1; uint r = sum(++i + i, i++); assert(r == 6);
    uint s = bump(1); assert(s == 4);
  })).isOk = true := by decide +kernel

/-- IR's native modular arguments are read left to right, with a saved first read. -/
example : (Prog.run (State.init IR) (sol[IR]{
    uint i = 3; uint r = addmod(++i, ++i, i); assert(r == 4);
    uint s = mulmod(++i, ++i, i); assert(s == 0);
    uint t = addmod(i, i++, 10); assert(t == 4);
  })).isOk = true := by decide +kernel

/-- Under IR, the first argument's panic precedes the dynamic zero modulus. -/
example : (Prog.run (State.init IR) (sol[IR]{
    uint k = 0; uint r = addmod(bad(), 2, k);
  })).halt? = some .panic := by decide +kernel

/-- Legacy still checks a dynamic zero modulus before the other arguments. -/
example : (Prog.run (State.init Legacy) (sol[Legacy]{
    uint k = 0; uint r = addmod(bad(), 2, k);
  })).halt? = some .revert := by decide +kernel

/-- Short-circuit operators and conditional branches keep conditional evaluation. -/
example : (Prog.run (State.init IR) (sol[IR]{
    uint i = 1;
    assert(true || bad() == 0); assert(!(false && bad() == 0));
    uint r = true ? ++i + i : bad(); assert(r == 4);
  })).isOk = true := by decide +kernel

/-- The formula reader uses the contract's schedule too. -/
theorem sourceOrder : ⊢ dl[IR]{ ⟨ uint i = 1; uint r = ++i + i; ⟩ r == 4 } := by
  sol_prove

/-- A failing first read precedes a later narrow overflow guard in IR mode. -/
example : (Prog.run (State.init IR) (sol[IR]{
    checked {
      uint[] memory a = new uint[](0); uint8 x = 255;
      uint r = a[0] + (x + 1);
    };
  })).halt? = some .revert := by decide +kernel

/-- Modular arguments use the same capture policy before explicit guards. -/
example : (Prog.run (State.init IR) (sol[IR]{
    checked {
      uint[] memory a = new uint[](0); uint8 x = 255;
      uint r = addmod(a[0], x + 1, 3);
    };
  })).halt? = some .revert := by decide +kernel

/-- An earlier failed read also precedes an ignored overflow. -/
example : (Prog.run (State.init IR) (sol[IR]{
    ignoringOverflow {
      uint[] memory a = new uint[](0); uint8 x = 255;
      uint r = a[0] + (x + 1);
    };
  })).halt? = some .revert := by decide +kernel

/-- The shared guard-order repair applies in legacy's operand direction too. -/
example : (Prog.run (State.init Legacy) (sol[Legacy]{
    checked {
      uint[] memory a = new uint[](0); uint8 x = 255;
      uint r = (x + 1) + a[0];
    };
  })).halt? = some .revert := by decide +kernel

solc_import "../../../tests/solc/MemoryPush.ast.json" hash 0x0477c52e82f8eb49
  as Imported.MemoryPush testing evalOrder .viaIR

/-- Imported contracts retain the chosen configuration and elaborate every body. -/
example : Imported.MemoryPush.evalOrder.binaryLeftToRight = true := rfl
example : (Imported.MemoryPush.report.all fun r => decide (r.status = .elaborated)) = true := by
  decide +kernel

end Solidity.Examples.Tactics.EvaluationOrder
