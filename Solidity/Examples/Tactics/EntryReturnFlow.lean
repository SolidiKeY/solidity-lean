import Solidity.Examples.Tactics.EntryReturn

/-! Extra source-frame controls: default memory, alias identity, early return
inside a loop, modifier continuation, and exact metadata/order. -/
namespace Solidity.Examples.Tactics.EntryReturnFlow
open Solidity.Examples.Tactics.EntryReturn
open Semantics ReadRealization

def Flow : Contract := contract!{
  uint executions;
  modifier afterStep() { _; executions += 10; }
  function f(bool b) afterStep returns (uint x, uint y, bytes memory txt) {
    executions++;
    while (b) {
      bytes memory a = hex"05";
      bytes memory alias_ = a;
      txt = a;
      alias_[0] = bytes1(0x09);
      return (1, 2, txt);
    }
    x = 3; y = 4;
  }
}

def start : State Flow [] := State.init Flow
def counter (s : Storage Flow) : Int :=
  ((⟨.uint, SRef.ofRoot "executions" rfl, .nil⟩ : Ref Flow).read s).val

def taken := entry_return[Flow, "f", (wordBytes 1).map UInt8.toNat]
def empty := entry_return[Flow, "f", (wordBytes 0).map UInt8.toNat]

/-- Returning from a loop still executes one modifier continuation; mutation
through the alias is observed through the actual returned object. -/
theorem loop_alias_modifier : snapshot start counter taken = some (expected 1 2 [9], 11) := by decide +kernel

/-- An unassigned memory return retains its empty default, not the last call's object. -/
theorem default_empty : snapshot start counter empty = some (expected 3 4 [], 11) := by decide +kernel

/-- This loop/alias/modifier witness also belongs to the ordinary run. -/
theorem ordinary_taken : taken.runR start = taken.runF 1000 start :=
  Solidity.EntryReturn.bounded_exact taken start 1000
    (snapshot_normal start counter taken _ loop_alias_modifier)

end Solidity.Examples.Tactics.EntryReturnFlow
