import SolidityBridge.RoadmapV15.P10.PushDecoderAgreement
import SolidityBridge.RoadmapV15.P10.Modular
import SolidityBridge.RoadmapV15.ReferenceReader

/-! Charged fetched consumption of the existing concrete Scalar.pushWord emitter.
The represented input is constructed explicitly; source/frame origin, prefix
execution, full code/resource adequacy and Osaka approval remain separate. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

private theorem word_array_reader (arr : Array UInt8) :
    uInt256OfByteArray ⟨arr⟩ = UInt256.ofNat (ofBytesBE arr.toList) := by
  exact congrArg UInt256.ofNat (reference_big_reader arr.toList)

/-- Exact existing Backend big-endian payload, read by the actual native reader. -/
theorem push_word_value (w : Scalar.Word) :
    uInt256OfByteArray ⟨(toBytesBE 32 w.toNat).toArray⟩ = UInt256.mk w.toFin := by
  rw [word_array_reader,Vector.toList_toArray]
  have roundtrip : ofBytesBE (toBytesBE 32 w.toNat).toList = w.toNat :=
    ofBytesBE_toBytesBE 32 w.toNat w.isLt
  rw [roundtrip]
  apply congrArg UInt256.mk
  apply Fin.ext
  exact Nat.mod_eq_of_lt w.isLt

/-- Existing emitted program, selected PC and explicit represented stack. -/
def wordPushInput (seed : EVM.State) (before after : Backend.Program)
    (w : Scalar.Word) (words : Scalar.Stack) : EVM.State :=
  {seed with
    pc := .ofNat (Backend.encode before).length
    stack := words.map (fun x => UInt256.mk x.toFin)
    executionEnv := {seed.executionEnv with
      code := ⟨(Backend.encode (before ++ Scalar.pushWord w :: after)).toArray⟩}}

theorem decode_word_push (seed : EVM.State) (before after : Backend.Program)
    (w : Scalar.Word) (words : Scalar.Stack)
    (fits : (Backend.encode before).length < UInt256.size) :
    EVM.decode (wordPushInput seed before after w words).executionEnv.code
      (wordPushInput seed before after w words).pc =
      some (.Push .PUSH32,some (UInt256.mk w.toFin,32)) := by
  have decoded := DecoderAgreement.decode_push before after ⟨32,by decide⟩ (toBytesBE 32 w.toNat) fits
  have tag : DecoderAgreement.pushOp ⟨32,by decide⟩ = .Push .PUSH32 := rfl
  rw [tag] at decoded
  simp only [show ¬(32 : Nat)=0 from by decide,if_false] at decoded
  rw [push_word_value] at decoded
  exact decoded

private theorem word_push_gate (s : EVM.State) (gas : 3 ≤ s.gasAvailable.toNat)
    (room : s.stack.length+1 ≤ 1024) :
    Assembly.driverGate #[] s (.Push .PUSH32) = .ok (s,3) := by
  have expansion : EVM.memoryExpansionCost s (.Push .PUSH32) = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  have cost : EVM.C' s (.Push .PUSH32) = 3 := rfl
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [cost,EVM.δ,EVM.α,Option.getD_some,Nat.sub_zero,if_neg (Nat.not_lt_zero _),
    if_neg (Nat.not_lt_of_ge gas),if_neg (Nat.not_lt_of_ge room)]
  cases s.executionEnv.perm <;> rfl

private theorem word_push_dispatch (s : EVM.State) (w : UInt256) (fuel : Nat) :
    EVM.step (fuel+1) 3 (some (.Push .PUSH32,some (w,32))) s =
      .ok ((Assembly.chargedPrepare s 3).replaceStackAndIncrPC (w::s.stack) 33) := by
  rfl

/-- Scalar output, complete charged native State and actual X continuation.
PC addition is the native word operation; no subsequent-PC or source-origin
claim is inferred from the explicitly represented split code image. -/
theorem word_push_agreement (seed : EVM.State) (before after : Backend.Program)
    (w : Scalar.Word) (words : Scalar.Stack)
    (fits : (Backend.encode before).length < UInt256.size)
    (gas : 3 ≤ seed.gasAvailable.toNat) (room : words.length+1 ≤ 1024) (fuel : Nat) :
    let input := wordPushInput seed before after w words
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((w::words).map (fun x => UInt256.mk x.toFin)) 33
    Scalar.step (Scalar.pushWord w) words = some (w::words) ∧
    Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
    EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  dsimp only
  refine ⟨Scalar.step_pushWord w words,?_⟩
  let input := wordPushInput seed before after w words
  have capacity : input.stack.length+1 ≤ 1024 := by
    change (words.map (fun x => UInt256.mk x.toFin)).length+1 ≤ 1024
    simpa only [List.length_map] using room
  have gate := word_push_gate input gas capacity
  have decoded := decode_word_push seed before after w words fits
  have step := word_push_dispatch input (UInt256.mk w.toFin) fuel
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    exact step
  · exact Assembly.X_continue fuel #[] input input _ (.Push .PUSH32,some (UInt256.mk w.toFin,32)) 3
      decoded gate step (by change Assembly.NonhaltingOpcode (.Push .PUSH32); unfold Assembly.NonhaltingOpcode;decide)

/-- A valid full input stack cannot admit another PUSH. Gas is checked first;
both the counted driver and actual X return the pinned overflow outcome. -/
theorem word_push_full_stack (seed : EVM.State) (before after : Backend.Program)
    (w : Scalar.Word) (words : Scalar.Stack)
    (fits : (Backend.encode before).length < UInt256.size)
    (gas : 3 ≤ seed.gasAvailable.toNat) (full : words.length = 1024) (fuel : Nat) :
    let input := wordPushInput seed before after w words
    Assembly.driverSteps 1 (fuel+2) #[] input = .error .StackOverflow ∧
    EVM.X (fuel+2) #[] input = .error .StackOverflow := by
  dsimp only
  let input := wordPushInput seed before after w words
  have expansion : EVM.memoryExpansionCost input (.Push .PUSH32) = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : input.gasAvailable-UInt256.ofNat 0 = input.gasAvailable := by
    change UInt256.mk (input.gasAvailable.val-0) = input.gasAvailable
    rw [sub_zero]
  have count : input.stack.length = 1024 := by
    change (words.map (fun x => UInt256.mk x.toFin)).length = 1024
    simpa only [List.length_map] using full
  have budget : 3 ≤ input.gasAvailable.toNat := gas
  have gate : Assembly.driverGate #[] input (.Push .PUSH32) = .error .StackOverflow := by
    simp only [Assembly.driverGate]
    rw [expansion,charge]
    have cost : EVM.C' input (.Push .PUSH32) = 3 := rfl
    simp only [cost,EVM.δ,EVM.α,Option.getD_some,Nat.sub_zero,count,
      if_neg (Nat.not_lt_zero _),if_neg (Nat.not_lt_of_ge budget)]
    rfl
  have decoded := decode_word_push seed before after w words fits
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
  · rw [Assembly.X_unfold,decoded]
    dsimp only [Option.getD]
    rw [gate]

#print axioms word_push_full_stack
#print axioms push_word_value
#print axioms decode_word_push
#print axioms word_push_agreement
end SolidityBridge.RoadmapV15.P10
