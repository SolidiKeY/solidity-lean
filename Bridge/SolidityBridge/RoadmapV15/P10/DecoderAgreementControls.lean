import SolidityBridge.RoadmapV15.P10.DecoderAgreement
namespace SolidityBridge.RoadmapV15.P10.DecoderAgreementControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External DecoderAgreement
private def seed : EVM.State :=
  {(default : EVM.State) with
    execLength := 41, gasAvailable := .ofNat 2600
    memory := ⟨#[0xaa,0xbb]⟩, returnData := ⟨#[0xcc,0xdd]⟩, H_return := ⟨#[0xee,0xff]⟩
    stack := [.ofNat 258,.ofNat 513]
    executionEnv := {(default : EVM.State).executionEnv with
      codeOwner := .ofNat 7, source := .ofNat 11, perm := false
      calldata := ⟨#[0x11,0x22,0x33]⟩}}
private def site (op : Backend.Op) : Site op :=
  ⟨seed,[.push ⟨1,by decide⟩ #v[0x1e],.op .POP],[.op .CALL,.op .JUMPDEST],by decide⟩

theorem all_populated_opcodes (op : Backend.Op) :
    EVM.decode (site op).state.executionEnv.code (site op).state.pc =
      some (referenceOp op,none) := decode_all _
theorem all_dup (n : Fin 16) :
    EVM.decode (site (.DUP n)).state.executionEnv.code (site (.DUP n)).state.pc =
      some (dupCode n,none) := decode_all _
theorem all_swap (n : Fin 16) :
    EVM.decode (site (.SWAP n)).state.executionEnv.code (site (.SWAP n)).state.pc =
      some (swapCode n,none) := decode_all _
theorem all_log (n : Fin 5) :
    EVM.decode (site (.LOG n)).state.executionEnv.code (site (.LOG n)).state.pc =
      some ((match n.val with
        | 0 => .LOG0 | 1 => .LOG1 | 2 => .LOG2 | 3 => .LOG3 | _ => .LOG4),none) :=
  decode_all _

theorem ordered_code : (site .ADD).state.executionEnv.code.data.toList =
    [0x60,0x1e,0x50,0x01,0xf1,0x5b] := rfl

theorem state_observations :
    (site .ADD).state.stack = [.ofNat 258,.ofNat 513] ∧
    (site .ADD).state.gasAvailable = .ofNat 2600 ∧
    (site .ADD).state.execLength = 41 ∧
    (site .ADD).state.memory.data.toList = [0xaa,0xbb] ∧
    (site .ADD).state.returnData.data.toList = [0xcc,0xdd] ∧
    (site .ADD).state.H_return.data.toList = [0xee,0xff] ∧
    (site .ADD).state.executionEnv.calldata.data.toList = [0x11,0x22,0x33] ∧
    (site .ADD).state.executionEnv.codeOwner = .ofNat 7 ∧
    (site .ADD).state.executionEnv.source = .ofNat 11 ∧
    (site .ADD).state.executionEnv.perm = false ∧
    (site .ADD).state.pc.toNat = 3 := by decide +kernel

theorem add_populated :
    EVM.decode (site .ADD).state.executionEnv.code (site .ADD).state.pc =
      some (.ADD,none) := decode_all _
theorem wrong_opcode :
    EVM.decode (site .ADD).state.executionEnv.code (site .ADD).state.pc ≠
      some (.SUB,none) := by rw [add_populated]; intro h; cases h

/-- Real Backend admission versus native INVALID; never a profile exclusion. -/
theorem backend_clz_accepts : Backend.decode [0x1e] = some [.op .CLZ] := Backend.decode_encode [.op .CLZ]

theorem reference_clz_invalid :
    EVM.decode (site .CLZ).state.executionEnv.code (site .CLZ).state.pc =
      some (.INVALID,none) := clz_invalid _
theorem reference_clz_fetch :
    EVM.fetchInstr (site .CLZ).state.executionEnv (site .CLZ).state.pc =
      .ok (.INVALID,none) := by
  simp only [EVM.fetchInstr,reference_clz_invalid,Option.option]

theorem data_is_not_site :
    EVM.decode (site .ADD).state.executionEnv.code (.ofNat 1) =
      some (.INVALID,none) := by decide +kernel

theorem embedded_clz_is_push_data :
    EVM.decode (site .ADD).state.executionEnv.code (.ofNat 0) =
      some (.PUSH1,some (.ofNat 30,1)) := by decide +kernel

theorem undefined_byte_invalid : EVM.decode ⟨#[0x0c]⟩ (.ofNat 0) =
    some (.INVALID,none) := by decide +kernel

theorem empty_is_not_decoded_stop : EVM.decode ⟨#[]⟩ (.ofNat 0) ≠ some (.STOP,none) := by decide +kernel

theorem arbitrary_fuel_cost_dispatch (fuel cost : Nat) :
    EVM.step (fuel+1) cost none (site .BALANCE).state =
      EVM.step (fuel+1) cost (some (.BALANCE,none)) (site .BALANCE).state :=
  fetched_dispatch _ fuel cost

#print axioms all_populated_opcodes
#print axioms all_dup
#print axioms all_swap
#print axioms all_log
#print axioms ordered_code
#print axioms state_observations
#print axioms add_populated
#print axioms wrong_opcode
#print axioms backend_clz_accepts
#print axioms reference_clz_invalid
#print axioms reference_clz_fetch
#print axioms data_is_not_site
#print axioms embedded_clz_is_push_data
#print axioms undefined_byte_invalid
#print axioms empty_is_not_decoded_stop
#print axioms arbitrary_fuel_cost_dispatch
end SolidityBridge.RoadmapV15.P10.DecoderAgreementControls
