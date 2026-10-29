import Solidity.Examples.Tactics.EntryReturn

/-! Source width and fixed-byte metadata stay attached to actual return locals. -/
namespace Solidity.Examples.Tactics.EntryReturnMetadata
open Solidity.Examples.Tactics.EntryReturn
open Semantics ReadRealization

def Narrow : Contract := contract!{
  uint executions;
  function f() returns (int8 a, bytes2 b, string memory txt) {
    executions++;
    return (-1, hex"ab00", "");
  }
}
def start : State Narrow [] := State.init Narrow
def counter (s : Storage Narrow) : Int :=
  ((⟨.uint, SRef.ofRoot "executions" rfl, .nil⟩ : Ref Narrow).read s).val

def actual := entry_return[Narrow, "f", ([] : List Nat)]

/-- The signed result is sign-extended, fixed bytes left-aligned, the dynamic
result empty, and source execution once. None is inferred from reference bytes. -/
theorem signed_fixed_bytes : snapshot start counter actual =
    some (expected (2^256 - 1) (43776 * 2^240) [], 1) := by decide +kernel

/-- The checked metadata-sensitive result also has ordinary execution meaning. -/
theorem ordinary : actual.runR start = actual.runF 1000 start :=
  Solidity.EntryReturn.bounded_exact actual start 1000
    (snapshot_normal start counter actual _ signed_fixed_bytes)

end Solidity.Examples.Tactics.EntryReturnMetadata
