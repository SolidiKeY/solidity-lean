import SolidityBridge.RoadmapV15.P10.WordPushConsumer
import Solidity.Backend.Environment.Metadata

/-! Actual fetched consumption of the published G31 bounded metadata constant.
Width zero uses PUSH0/cost two; positive widths use the actual payload/cost three.
No allocator, source resolution, scanner, driver or Osaka adequacy is assumed. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

def metadataPushCost (width : Fin 33) : Nat := if width.val = 0 then 2 else 3

def metadataPushInput (seed : EVM.State) (before after : Backend.Program)
    (width : Fin 33) (value : Fin (256^width.val)) (tail : List Backend.Environment.Word) : EVM.State :=
  {seed with
    pc := UInt256.ofNat (Backend.encode before).length
    stack := tail.map (fun w => UInt256.mk (Scalar.encodeValue .uint w).toFin)
    executionEnv := {seed.executionEnv with code :=
      ⟨(Backend.encode (before ++ Backend.Environment.constant width value :: after)).toArray⟩}}

theorem metadata_payload_value (width : Fin 33) (value : Fin (256^width.val)) :
    uInt256OfByteArray ⟨(toBytesBE width.val value.val).toArray⟩ = UInt256.ofNat value.val := by
  have reader : uInt256OfByteArray ⟨(toBytesBE width.val value.val).toArray⟩ =
      UInt256.ofNat (ofBytesBE (toBytesBE width.val value.val).toList) := by
    exact congrArg UInt256.ofNat (reference_big_reader (toBytesBE width.val value.val).toList)
  rw [reader,ofBytesBE_toBytesBE width.val value.val value.isLt]

theorem metadata_source_word (width : Fin 33) (value : Fin (256^width.val)) :
    UInt256.ofNat value.val = UInt256.mk (Scalar.encodeValue .uint
      (lenU value.val (Backend.Environment.constant_bound width value))).toFin := by
  apply congrArg UInt256.mk
  apply Fin.ext
  change value.val % UInt256.size = (Scalar.encodeValue .uint
    (lenU value.val (Backend.Environment.constant_bound width value))).toNat
  rw [Scalar.encode_uint_toNat]
  exact Nat.mod_eq_of_lt (Backend.Environment.constant_bound width value)

private theorem facts (width : Fin 33) (s : EVM.State) :
    EVM.memoryExpansionCost s (DecoderAgreement.pushOp width) = 0 ∧
    EVM.C' s (DecoderAgreement.pushOp width) = metadataPushCost width ∧
    EVM.δ (DecoderAgreement.pushOp width) = some 0 ∧
    EVM.α (DecoderAgreement.pushOp width) = some 1 := by
  fin_cases width <;> refine ⟨?_,rfl,rfl,rfl⟩ <;>
    change EVM.Cₘ s.activeWords - EVM.Cₘ s.activeWords = 0
  all_goals exact Nat.sub_self _

private theorem gate (valid : Array UInt256) (s : EVM.State) (width : Fin 33)
    (gas : metadataPushCost width ≤ s.gasAvailable.toNat) (room : s.stack.length+1 ≤ 1024) :
    Assembly.driverGate valid s (DecoderAgreement.pushOp width) = .ok (s,metadataPushCost width) := by
  have f := facts width s
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  simp only [Assembly.driverGate]
  rw [f.1,charge]
  simp only [f.2.1,f.2.2.1,f.2.2.2,Option.getD_some,Nat.sub_zero,
    if_neg (Nat.not_lt_zero _),if_neg (Nat.not_lt_of_ge gas),if_neg (Nat.not_lt_of_ge room)]
  fin_cases width <;> cases s.executionEnv.perm <;> rfl

private theorem dispatch (s : EVM.State) (width : Fin 33) (word : UInt256) (fuel cost : Nat)
    (zero : width.val = 0 → word = UInt256.ofNat 0) :
    EVM.step (fuel+1) cost (some (DecoderAgreement.pushOp width,
      if width.val = 0 then none else some (word,width.val))) s =
      .ok ((Assembly.chargedPrepare s cost).replaceStackAndIncrPC (word::s.stack) (width.val+1)) := by
  fin_cases width
  all_goals first | rfl | (have z := zero rfl;subst word;rfl)

/-- Actual typed metadata PUSH meaning, complete charged State and X continuation. -/
theorem metadata_constant_execution (valid : Array UInt256) (seed : EVM.State)
    (before after : Backend.Program) (width : Fin 33) (value : Fin (256^width.val))
    (tail : List Backend.Environment.Word) (fits : (Backend.encode before).length < UInt256.size)
    (gas : metadataPushCost width ≤ seed.gasAvailable.toNat) (room : tail.length+1 ≤ 1024) (fuel : Nat) :
    let input := metadataPushInput seed before after width value tail
    let next := (Assembly.chargedPrepare input (metadataPushCost width)).replaceStackAndIncrPC
      (UInt256.ofNat value.val::input.stack) (width.val+1)
    Backend.Environment.pushStep (Backend.Environment.constant width value) tail =
      some (lenU value.val (Backend.Environment.constant_bound width value)::tail) ∧
    Assembly.driverSteps 1 (fuel+2) valid input = .ok next ∧
    EVM.X (fuel+2) valid input = EVM.X (fuel+1) valid next ∧
    next.stack = (lenU value.val (Backend.Environment.constant_bound width value)::tail).map
      (fun w => UInt256.mk (Scalar.encodeValue .uint w).toFin) := by
  dsimp only
  let input := metadataPushInput seed before after width value tail
  have decoded : EVM.decode input.executionEnv.code input.pc =
      some (DecoderAgreement.pushOp width,
        if width.val = 0 then none else some (UInt256.ofNat value.val,width.val)) := by
    have h := DecoderAgreement.decode_push before after width (toBytesBE width.val value.val) fits
    rw [metadata_payload_value] at h
    exact h
  have enough : input.stack.length+1 ≤ 1024 := by
    change (tail.map (fun w => UInt256.mk (Scalar.encodeValue .uint w).toFin)).length+1 ≤ 1024
    simpa only [List.length_map] using room
  have checked := gate valid input width gas enough
  have step := dispatch input width (UInt256.ofNat value.val) fuel (metadataPushCost width) (by
    intro zero
    have bound : value.val < 1 := by simpa only [zero,pow_zero] using value.isLt
    have vzero : value.val = 0 := by omega
    rw [vzero])
  have nonhalting : Assembly.NonhaltingOpcode (DecoderAgreement.pushOp width) := by
    fin_cases width <;> unfold Assembly.NonhaltingOpcode <;> decide
  refine ⟨Backend.Environment.constant_correct width value tail,?_,?_,?_⟩
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [checked]
    dsimp only
    rw [step]
  · exact Assembly.X_continue fuel valid input input _
      (DecoderAgreement.pushOp width,if width.val=0 then none else some (UInt256.ofNat value.val,width.val))
      (metadataPushCost width) decoded checked step nonhalting
  · simp only [EVM.State.replaceStackAndIncrPC,List.map_cons]
    rw [←metadata_source_word width value]
    rfl

/-- Full legal input stack refusal, after the actual width-dependent gas check. -/
theorem metadata_constant_full_stack (valid : Array UInt256) (seed : EVM.State)
    (before after : Backend.Program) (width : Fin 33) (value : Fin (256^width.val))
    (tail : List Backend.Environment.Word) (fits : (Backend.encode before).length < UInt256.size)
    (gas : metadataPushCost width ≤ seed.gasAvailable.toNat) (full : tail.length = 1024) (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) valid (metadataPushInput seed before after width value tail) =
      .error .StackOverflow := by
  let input := metadataPushInput seed before after width value tail
  have f := facts width input
  have charge : input.gasAvailable-UInt256.ofNat 0 = input.gasAvailable := by
    change UInt256.mk (input.gasAvailable.val-0) = input.gasAvailable
    rw [sub_zero]
  have count : input.stack.length = 1024 := by
    change (tail.map (fun w => UInt256.mk (Scalar.encodeValue .uint w).toFin)).length = 1024
    simpa only [List.length_map] using full
  have budget : metadataPushCost width ≤ input.gasAvailable.toNat := gas
  have refused : Assembly.driverGate valid input (DecoderAgreement.pushOp width) = .error .StackOverflow := by
    simp only [Assembly.driverGate]
    rw [f.1,charge]
    simp only [f.2.1,f.2.2.1,f.2.2.2,Option.getD_some,Nat.sub_zero,count,
      if_neg (Nat.not_lt_zero _),if_neg (Nat.not_lt_of_ge budget)]
    fin_cases width <;> rfl
  have decoded := DecoderAgreement.decode_push before after width (toBytesBE width.val value.val) fits
  change Assembly.driverSteps 1 (fuel+2) valid input = _
  simp only [Assembly.driverSteps]
  rw [show EVM.decode input.executionEnv.code input.pc = _ from decoded]
  dsimp only [Option.option,bind,Except.bind]
  rw [refused]

#print axioms metadata_payload_value
#print axioms metadata_source_word
#print axioms metadata_constant_execution
#print axioms metadata_constant_full_stack
end SolidityBridge.RoadmapV15.P10
