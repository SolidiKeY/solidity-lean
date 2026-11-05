import SolidityBridge.RoadmapV15.P10.EqualityConsumer
import SolidityBridge.RoadmapV15.P10.BooleanNotConsumer
import SolidityBridge.RoadmapV15.P10.NegationBody

/-! Two actual fetched instructions of the published typed inequality emitter.
The existing semantics/certificates are consumed, not replaced by a machine. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

def inequalityInput (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  {seed with
    executionEnv := {seed.executionEnv with
      code := ⟨(Backend.encode (before ++ [.op .EQ,.op .ISZERO] ++ after)).toArray⟩}
    pc := UInt256.ofNat (Backend.encode before).length
    stack := (a::b::tail).map (fun w => UInt256.mk w.toFin)}
def inequalityEqual (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (inequalityInput seed before after a b tail) 3).replaceStackAndIncrPC
    ((Scalar.flag (a == b)::tail).map (fun w => UInt256.mk w.toFin))
def inequalityOutput (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (inequalityEqual seed before after a b tail) 3).replaceStackAndIncrPC
    ((Scalar.flag (!(a == b))::tail).map (fun w => UInt256.mk w.toFin))

private theorem pc_one (n : Nat) : UInt256.ofNat n + UInt256.ofNat 1 = UInt256.ofNat (n+1) := by
  apply congrArg UInt256.mk
  apply Fin.ext
  exact (Nat.add_mod n 1 UInt256.size).symm

private theorem first_alignment (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack) (fits : (Backend.encode before).length < UInt256.size) :
    (modularSite (⟨seed,before,.op .ISZERO::after,fits⟩ : Site .EQ) (a::b::tail)).state =
      inequalityInput seed before after a b tail := by
  simp only [modularSite,Site.state,inequalityInput,List.append_assoc,List.cons_append,List.nil_append]

private theorem second_alignment (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack)
    (fits : (Backend.encode (before ++ [.op .EQ])).length < UInt256.size) :
    (modularSite (⟨inequalityEqual seed before after a b tail,before ++ [.op .EQ],after,fits⟩ :
      Site .ISZERO) (Scalar.flag (a == b)::tail)).state = inequalityEqual seed before after a b tail := by
  simp only [modularSite,Site.state,inequalityEqual,inequalityInput,Assembly.chargedPrepare,
    EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,List.map_cons,List.append_assoc,List.cons_append,
    List.nil_append,Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Instr.encode,
    List.length_append,List.length_cons,List.length_nil,List.append_nil,pc_one,Nat.zero_add]

theorem inequality_execution (valid : Array UInt256) (seed : EVM.State)
    (before after : Backend.Program) (a b : Scalar.Word) (tail : Scalar.Stack)
    (fits : (Backend.encode (before ++ [.op .EQ])).length < UInt256.size)
    (room : tail.length+2 ≤ 1024) (gas : 6 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Scalar.run [.op .EQ,.op .ISZERO] (a::b::tail) = some (Scalar.flag (!(a == b))::tail) ∧
    Assembly.driverSteps 2 (fuel+3) valid (inequalityInput seed before after a b tail) =
      .ok (inequalityOutput seed before after a b tail) ∧
    EVM.X (fuel+3) valid (inequalityInput seed before after a b tail) =
      EVM.X (fuel+1) valid (inequalityOutput seed before after a b tail) := by
  have initialFits : (Backend.encode before).length < UInt256.size := by
    simp only [Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Instr.encode,
      List.length_append,List.length_cons,List.length_nil] at fits
    omega
  have first := equality_agreement valid (⟨seed,before,.op .ISZERO::after,initialFits⟩)
    a b tail room (by change 3 ≤ seed.gasAvailable.toNat;omega) (fuel+1)
  dsimp only at first
  rw [first_alignment] at first
  have debit : (inequalityEqual seed before after a b tail).gasAvailable.toNat =
      seed.gasAvailable.toNat-3 := reference_gas_debit seed.gasAvailable 3 (by omega)
  have second := iszero_agreement valid
    (⟨inequalityEqual seed before after a b tail,before ++ [.op .EQ],after,fits⟩)
    (Scalar.flag (a == b)) tail (by omega)
    (by change 3 ≤ (inequalityEqual seed before after a b tail).gasAvailable.toNat;rw [debit];omega) fuel
  dsimp only at second
  rw [second_alignment,Scalar.flag_iszero] at second
  have firstDriver : Assembly.driverSteps 1 (fuel+3) valid (inequalityInput seed before after a b tail) =
      .ok (inequalityEqual seed before after a b tail) := first.2.1
  refine ⟨?_,?_,first.2.2.trans second.2.2⟩
  · change some (Scalar.flag (Scalar.flag (a == b) == 0)::tail) = _
    rw [Scalar.flag_iszero]
  · rw [fetched_steps_append 1 1 (fuel+1),firstDriver]
    exact second.2.1

/-- Actual typed certificate and native two-step result for the same operands. -/
theorem selected_inequality_execution (valid : Array UInt256) (seed : EVM.State)
    (before after : Backend.Program) (p : PrimTy) (a b : p.Denote) (tail : Scalar.Stack)
    (fits : (Backend.encode (before ++ [.op .EQ])).length < UInt256.size)
    (room : tail.length+2 ≤ 1024) (gas : 6 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Scalar.run (Scalar.scalarNe p).code (Scalar.encodeValue p a::Scalar.encodeValue p b::tail) =
      (BinOp.neB.evalT (p := p) (by cases p <;> rfl) a b).map
        (fun result => Scalar.encodeValue .bool result::tail) ∧
    Assembly.driverSteps 2 (fuel+3) valid
      (inequalityInput seed before after (Scalar.encodeValue p a) (Scalar.encodeValue p b) tail) =
      .ok (inequalityOutput seed before after (Scalar.encodeValue p a) (Scalar.encodeValue p b) tail) ∧
    EVM.X (fuel+3) valid
      (inequalityInput seed before after (Scalar.encodeValue p a) (Scalar.encodeValue p b) tail) =
      EVM.X (fuel+1) valid
        (inequalityOutput seed before after (Scalar.encodeValue p a) (Scalar.encodeValue p b) tail) := by
  exact ⟨(Scalar.scalarNe p).correct a b tail,
    (inequality_execution valid seed before after (Scalar.encodeValue p a)
      (Scalar.encodeValue p b) tail fits room gas fuel).2⟩

theorem inequality_debit (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack) (gas : 6 ≤ seed.gasAvailable.toNat) :
    (inequalityOutput seed before after a b tail).gasAvailable.toNat = seed.gasAvailable.toNat-6 := by
  have first := reference_gas_debit seed.gasAvailable 3 (by omega)
  have second := reference_gas_debit (seed.gasAvailable-UInt256.ofNat 3) 3 (by rw [first];omega)
  change ((seed.gasAvailable-UInt256.ofNat 3)-UInt256.ofNat 3).toNat = _
  rw [second,first,Nat.sub_sub]

theorem inequality_frame (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack) :
    (inequalityOutput seed before after a b tail).toState = (inequalityInput seed before after a b tail).toState ∧
    (inequalityOutput seed before after a b tail).memory = seed.memory ∧
    (inequalityOutput seed before after a b tail).returnData = seed.returnData ∧
    (inequalityOutput seed before after a b tail).H_return = seed.H_return ∧
    (inequalityOutput seed before after a b tail).stack =
      (Scalar.flag (!(a == b))::tail).map (fun w => UInt256.mk w.toFin) ∧
    (inequalityOutput seed before after a b tail).execLength = seed.execLength+2 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms inequality_execution
#print axioms selected_inequality_execution
#print axioms inequality_debit
#print axioms inequality_frame
end SolidityBridge.RoadmapV15.P10
