import SolidityBridge.RoadmapV15.EnvironmentReference

/-! Distinct nonzero accounts, absent accounts, timestamp wrap, full ordered
observations and negative controls. These are reference supplied-opcode checks,
not arbitrary-account execution or transaction/resource/Osaka adequacy. -/
namespace SolidityBridge.RoadmapV15.EnvironmentReferenceControls
open Solidity Solidity.Backend
private def frame : EvmYul.EVM.State :=
  { (default : EvmYul.EVM.State) with
    executionEnv := { (default : EvmYul.ExecutionEnv .EVM) with
      codeOwner := .ofNat 7, source := .ofNat 11, weiValue := .ofNat 13
      header := { (default : EvmYul.BlockHeader) with timestamp := 2 ^ 256 + 17 } }
    accountMap := ((∅ : EvmYul.AccountMap .EVM).insert (.ofNat 7)
      { (default : EvmYul.Account .EVM) with balance := .ofNat 29 }).insert (.ofNat 11)
      { (default : EvmYul.Account .EVM) with balance := .ofNat 31 }
    stack := [.ofNat 258, .ofNat 513] }
private def keys : List EnvKey := [.msgSender, .msgValue, .timestamp, .selfBalance, .selfAddress]
private def observations (s : EvmYul.EVM.State) : List Nat :=
  keys.map (fun k => (environmentReferenceValue s k).toNat)

example : observations frame = [11, 13, 17, 29, 7] := by decide +kernel
example : keys.map (fun k => (Solidity.Backend.Environment.observe
    (environmentReferenceFrame frame) k).1.toNat) = [11, 13, 17, 29, 7] := by
  simp only [environment_observe_reference]
  decide +kernel
example : observations frame ≠ [11, 13, 17, 31, 7] := by decide +kernel
example : observations frame ≠ (observations frame).reverse := by decide +kernel
example : observations {frame with accountMap := ∅} = [11, 13, 17, 0, 7] := by decide +kernel
example : observations {frame with executionEnv := {frame.executionEnv with source := .ofNat 19}} =
    [19, 13, 17, 29, 7] := by decide +kernel
example : observations {frame with accountMap := (frame.accountMap.insert (.ofNat 7)
    { (default : EvmYul.Account .EVM) with balance := .ofNat 37 })} = [11, 13, 17, 37, 7] := by decide +kernel
example (k : EnvKey) (fuel : Nat) :
    EvmYul.EVM.step (fuel + 1) 0 (some (environmentReferenceOp k, none)) frame = .ok
      ((Solidity.Evm.External.Memory.prepare frame).replaceStackAndIncrPC
        (Solidity.Evm.External.encode (Scalar.encodeValue .uint
          (Solidity.Backend.Environment.observe (environmentReferenceFrame frame) k)).toFin :: frame.stack)) :=
  environment_selected_reference frame k frame.stack fuel
example (k : EnvKey) :
    EvmYul.EVM.step 0 0 (some (environmentReferenceOp k, none)) frame = .error .OutOfFuel := rfl
example : (Solidity.Evm.External.Memory.encoding (environmentReferenceValue frame .selfBalance)).toList =
    List.replicate 31 0 ++ [29] := by
  rw [reference_encoding_bytes]; decide +kernel
example : (Solidity.Evm.External.Memory.encoding (environmentReferenceValue frame .selfBalance)).toList ≠
    [29] ++ List.replicate 31 0 := by
  rw [reference_encoding_bytes]; decide +kernel
example : (Solidity.Evm.External.Memory.encoding (environmentReferenceValue frame .selfBalance)).toList ≠
    List.replicate 30 0 ++ [29] := by
  rw [reference_encoding_bytes]; decide +kernel

private def C : Contract := { vars := [] }
private def u (n : Nat) (h : n < 2 ^ 256 := by decide) : PrimTy.uint.Denote := lenU n h
private def sourceState : State C [] :=
  { State.init C with
    selfBalance := u 29
    tx := { msgSender := u 11, msgValue := u 13, timestamp := u 17, selfAddress := u 7 } }
private theorem sourceRepresents :
    Solidity.Backend.Environment.Represents (environmentReferenceFrame frame) sourceState := by
  constructor <;> decide +kernel
example : ¬ Solidity.Backend.Environment.Represents (environmentReferenceFrame frame)
    {sourceState with selfBalance := u 31} := by
  intro h
  have hb := h.balance
  have hn : (u 31) ≠ (environmentReferenceFrame frame).funds (environmentReferenceFrame frame).self := by decide +kernel
  exact hn hb
example (k : EnvKey) :
    Solidity.Evm.External.encode (Scalar.encodeValue .uint (sourceState.envVal k)).toFin =
      environmentReferenceValue frame k :=
  environment_source_observation sourceState frame sourceRepresents k

#print axioms environment_address_word
#print axioms environment_address_roundtrip
#print axioms environment_word_encode
#print axioms environment_observe_reference
#print axioms environment_selected_backend
#print axioms environment_selected_reference
#print axioms environment_reference_bytes
#print axioms environment_source_observation
end SolidityBridge.RoadmapV15.EnvironmentReferenceControls
