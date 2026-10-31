import Solidity.Examples.Tactics.EntryReturnFlow

/-! The same actual-return controls in the existing viaIR evaluation mode. -/
namespace Solidity.Examples.Tactics.EntryReturnFlowIR
open Solidity.Examples.Tactics.EntryReturn
open Semantics ReadRealization

def Flow : Contract := { EntryReturnFlow.Flow with evalOrder := .viaIR }
def start : State Flow [] := State.init Flow
def counter (s : Storage Flow) : Int :=
  ((⟨.uint, SRef.ofRoot "executions" rfl, .nil⟩ : Ref Flow).read s).val

#entry_return taken := Flow, "f", (wordBytes 1).map UInt8.toNat
#entry_return empty := Flow, "f", (wordBytes 0).map UInt8.toNat

/-- ViaIR modifier frames also preserve the actual memory alias and return order. -/
theorem loop_alias_modifier : snapshot start counter taken = some (expected 1 2 [9], 11) := by decide +kernel
/-- Default memory remains empty under viaIR modifier frames. -/
theorem default_empty : snapshot start counter empty = some (expected 3 4 [], 11) := by decide +kernel
/-- This separate-mode witness agrees with the ordinary run in that same mode. -/
theorem ordinary_taken : taken.runR start = taken.runF 1000 start :=
  Solidity.EntryReturn.bounded_exact taken start 1000
    (snapshot_normal start counter taken _ loop_alias_modifier)

end Solidity.Examples.Tactics.EntryReturnFlowIR
