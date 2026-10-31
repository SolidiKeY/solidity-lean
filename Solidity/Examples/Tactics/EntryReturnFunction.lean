import Solidity.Examples.Tactics.EntryReturn

/-! Return-only external-function metadata: no function input, invocation,
lazy calldata or world execution is introduced. -/
namespace Solidity.Examples.Tactics.EntryReturnFunction
open Solidity.Examples.Tactics.EntryReturn
open Semantics ReadRealization

def Probe : Contract := contract!{
  uint executions;
  function «fun»() { }
  function g() returns (uint a, function() external h, uint b) {
    a = 1; h = address(0x1234).«fun»; b = 9;
  }
  function f() returns (uint x, function() external target, uint y) {
    executions++;
    try this.g() returns (uint a, function() external h, uint b) {
      x = a; target = h; y = b;
    } catch { }
  }
}
def start : State Probe [] := { State.init Probe with tx := { selfAddress := PrimTy.ofIntD .uint 7 } }
def counter (s : Storage Probe) : Int :=
  ((⟨.uint, SRef.ofRoot "executions" rfl, .nil⟩ : Ref Probe).read s).val

def actual := entry_return[Probe, "f", ([] : List Nat)]
def packed : Nat := 0x1234 * 2^32 + 0x946644cd
def expected : List Nat := (wordBytes 1 ++ wordBytes (packed * 2^64) ++ wordBytes 9).map UInt8.toNat

/-- The actual returned function keeps address/selector identity and eight
trailing ABI zero bytes, between both primitive results, with entry executed once. -/
theorem packed_return : snapshot start counter actual = some (expected, 1) := by decide +kernel

/-- The checked return tuple also has unchanged ordinary execution meaning. -/
theorem ordinary : actual.runR start = actual.runF 1000 start :=
  Solidity.EntryReturn.bounded_exact actual start 1000
    (snapshot_normal start counter actual _ packed_return)

def ProbeIR : Contract := { Probe with evalOrder := .viaIR }
def startIR : State ProbeIR [] := { State.init ProbeIR with tx := { selfAddress := PrimTy.ofIntD .uint 7 } }
def counterIR (s : Storage ProbeIR) : Int :=
  ((⟨.uint, SRef.ofRoot "executions" rfl, .nil⟩ : Ref ProbeIR).read s).val
def actualIR := entry_return[ProbeIR, "f", ([] : List Nat)]

/-- The returned function's address, selector, padding and order agree in viaIR too. -/
theorem packed_return_ir : snapshot startIR counterIR actualIR = some (expected, 1) := by decide +kernel
/-- This separate-mode snapshot also certifies ordinary execution. -/
theorem ordinary_ir : actualIR.runR startIR = actualIR.runF 1000 startIR :=
  Solidity.EntryReturn.bounded_exact actualIR startIR 1000
    (snapshot_normal startIR counterIR actualIR _ packed_return_ir)

/- Function-input marker parsing is an explicit runtime negative; the universal
Boolean refusal implication is Tools.EntryReturn.function_arguments_refused. -/
/-- info: false -/
#guard_msgs in #eval Tools.EntryReturn.functionTupleAdmitted Probe "f"
  { params := [("arg", .prim .uint)], body := [],
    rets := [("x", .prim .uint), ("h", .prim .uint), ("y", .prim .uint)],
    widths := [("arg#function()external", 1), ("h#function()external", 1)] }
/-- info: false -/
#guard_msgs in #eval Tools.EntryReturn.functionTupleAdmitted Probe "f"
  { params := [], body := [],
    rets := [("x", .prim .uint), ("h", .prim .uint), ("y", .prim .uint)],
    widths := [("h#function()", 1)] }

end Solidity.Examples.Tactics.EntryReturnFunction
