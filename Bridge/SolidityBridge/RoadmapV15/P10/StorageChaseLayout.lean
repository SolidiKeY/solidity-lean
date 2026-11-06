import SolidityBridge.RoadmapV15.P10.StorageWarmTransport
import SolidityBridge.RoadmapV15.P10.LogicalShiftLayout

/-! Actual Backend two-SLOAD code and value-directed native State observations.
This is numeric-reference composition, not compiler symbolic-path admission. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

def storageChaseCode : Backend.Program := [.op .SLOAD,.op .SLOAD]
def storageChaseInput (seed : EVM.State) (before after : Backend.Program)
    (key : UInt256) (tail : List UInt256) : EVM.State :=
  {seed with
    pc := .ofNat (Backend.encode before).length,stack := key::tail
    executionEnv := {seed.executionEnv with code :=
      ⟨(Backend.encode (before ++ storageChaseCode ++ after)).toArray⟩}}
def storageChaseValue (seed : EVM.State) (before after : Backend.Program)
    (key : UInt256) (tail : List UInt256) : UInt256 :=
  (EvmYul.State.sload (storageChaseInput seed before after key tail).toState key).2
def storageChaseFirst (seed : EVM.State) (before after : Backend.Program)
    (key : UInt256) (tail : List UInt256) : EVM.State :=
  let input := storageChaseInput seed before after key tail
  let read := EvmYul.State.sload input.toState key
  ({Assembly.chargedPrepare input (EVM.C' input .SLOAD) with toState := read.1}).replaceStackAndIncrPC (read.2::tail)
def storageChaseOutput (seed : EVM.State) (before after : Backend.Program)
    (key : UInt256) (tail : List UInt256) : EVM.State :=
  let first := storageChaseFirst seed before after key tail
  let value := storageChaseValue seed before after key tail
  let read := EvmYul.State.sload first.toState value
  ({Assembly.chargedPrepare first (EVM.C' first .SLOAD) with toState := read.1}).replaceStackAndIncrPC (read.2::tail)
def storageChaseCharge (seed : EVM.State) (before after : Backend.Program)
    (key : UInt256) (tail : List UInt256) : Nat :=
  EVM.C' (storageChaseInput seed before after key tail) .SLOAD +
    EVM.C' (storageChaseFirst seed before after key tail) .SLOAD
def storageChaseTailSite (seed : EVM.State) (before after : Backend.Program)
    (fits : (Backend.encode (before ++ [.op .SLOAD])).length < UInt256.size) : Site .SLOAD :=
  ⟨seed,before ++ [.op .SLOAD],after,fits⟩

theorem storage_chase_code (seed : EVM.State) (before after : Backend.Program) (key : UInt256) (tail : List UInt256) :
    (storageChaseInput seed before after key tail).executionEnv.code.data.toList =
      Backend.encode (before ++ storageChaseCode ++ after) := by rfl

theorem storage_chase_prefix_length (before : Backend.Program) :
    (Backend.encode (before ++ [.op .SLOAD])).length = (Backend.encode before).length+1 := by
  simp only [Backend.encode_append,Backend.encode_cons,Backend.encode_nil,
    Instr.encode,List.length_append,List.length_cons,List.length_nil]

theorem storage_chase_tail_alignment (seed : EVM.State) (before after : Backend.Program)
    (key : UInt256) (tail : List UInt256)
    (fits : (Backend.encode (before ++ [.op .SLOAD])).length < UInt256.size) :
    (slotReadSite (storageChaseTailSite (storageChaseFirst seed before after key tail) before after fits)
      (storageChaseValue seed before after key tail) tail).state = storageChaseFirst seed before after key tail := by
  simp only [slotReadSite,storageChaseTailSite,Site.state,storageChaseFirst,storageChaseInput,
    storageChaseCode,storageChaseValue,Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,
    EVM.State.incrPC,EvmYul.State.sload,EvmYul.State.addAccessedStorageKey,
    List.append_assoc,List.cons_append,List.nil_append,Backend.encode_append,Backend.encode_cons,
    Backend.encode_nil,Instr.encode,List.length_append,List.length_cons,List.length_nil,logical_shift_pc_increment]

theorem storage_chase_cost_bounds (seed : EVM.State) (before after : Backend.Program) (key : UInt256) (tail : List UInt256) :
    EVM.C' (storageChaseInput seed before after key tail) .SLOAD ≤ 2100 ∧
    EVM.C' (storageChaseFirst seed before after key tail) .SLOAD ≤ 2100 := by
  constructor <;> change (if _ then 100 else 2100) ≤ 2100 <;> split <;> decide


#print axioms storage_chase_code
#print axioms storage_chase_prefix_length
#print axioms storage_chase_tail_alignment
#print axioms storage_chase_cost_bounds
end SolidityBridge.RoadmapV15.P10
