import SolidityBridge.RoadmapV15.P10.NonbranchTables
import SolidityBridge.RoadmapV15.P10.WrappingArithmeticConsumer
import SolidityBridge.RoadmapV15.P10.UnsignedCleanupLayout
import SolidityBridge.RoadmapV15.P10.CountedAppend
import Solidity.Backend.Scalar.Negation

/-! Actual two-instruction G25 negation body, not the checked guard/panic path.
The minimum signed input wraps in this body; no successful source negation,
compiler origin, Osaka approval or physical frame is assumed or concluded. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

def negationBodyInput (seed : EVM.State) (before after : Backend.Program)
    (a : PrimTy.int.Denote) (tail : Scalar.Stack) : EVM.State :=
  wordPushInput seed before (.op .SUB::after) 0 (Scalar.encodeValue .int a::tail)
def negationBodyPushed (seed : EVM.State) (before after : Backend.Program)
    (a : PrimTy.int.Denote) (tail : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (negationBodyInput seed before after a tail) 3).replaceStackAndIncrPC
    ((0::Scalar.encodeValue .int a::tail).map (fun w => UInt256.mk w.toFin)) 33
def negationBodySite (seed : EVM.State) (before after : Backend.Program)
    (fits : (Backend.encode (before ++ [Scalar.pushWord 0])).length < UInt256.size) : Site .SUB :=
  ⟨seed,before ++ [Scalar.pushWord 0],after,fits⟩
def negationBodyOutput (seed : EVM.State) (before after : Backend.Program)
    (a : PrimTy.int.Denote) (tail : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (negationBodyPushed seed before after a tail) 3).replaceStackAndIncrPC
    ((BitVec.ofInt 256 (-a.val)::tail).map (fun w => UInt256.mk w.toFin))

theorem negation_body_selection :
    Scalar.selectCheckedUnary .neg .int rfl = some Scalar.checkedIntNeg ∧
    Scalar.checkedIntNeg.test = Scalar.negationTest ∧ Scalar.checkedIntNeg.body = Scalar.negationBody := by
  exact ⟨rfl,rfl,rfl⟩

/-- Extract the actual word equation from the published typed body theorem. -/
theorem negation_body_word (a : PrimTy.int.Denote) :
    (0 : Scalar.Word)-Scalar.encodeValue .int a = BitVec.ofInt 256 (-a.val) := by
  have h := Scalar.negationBody_typed a []
  rw [Scalar.negationBody,Scalar.run,Scalar.step_pushWord] at h
  change some (((0 : Scalar.Word)-Scalar.encodeValue .int a)::[]) =
    some (BitVec.ofInt 256 (-a.val)::[]) at h
  exact (List.cons.inj (Option.some.inj h)).1

theorem negation_body_code (seed : EVM.State) (before after : Backend.Program)
    (a : PrimTy.int.Denote) (tail : Scalar.Stack) :
    (negationBodyInput seed before after a tail).executionEnv.code.data.toList =
      Backend.encode (before ++ Scalar.negationBody ++ after) := by
  simp only [negationBodyInput,wordPushInput,Scalar.negationBody,List.append_assoc,
    List.cons_append,List.nil_append,List.toList_toArray]

theorem negation_body_alignment (seed : EVM.State) (before after : Backend.Program)
    (a : PrimTy.int.Denote) (tail : Scalar.Stack)
    (fits : (Backend.encode (before ++ [Scalar.pushWord 0])).length < UInt256.size) :
    (modularSite (negationBodySite (negationBodyPushed seed before after a tail) before after fits)
      (0::Scalar.encodeValue .int a::tail)).state = negationBodyPushed seed before after a tail := by
  simp only [negationBodySite,modularSite,Site.state,negationBodyPushed,negationBodyInput,
    wordPushInput,Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,
    List.map_cons,List.append_assoc,List.cons_append,List.nil_append,Backend.encode_append,
    Backend.encode_cons,Backend.encode_nil,List.length_append,List.length_cons,List.length_nil,
    Scalar.encode_pushWord,Vector.length_toList,signed_push_pc]

/-- Both fetched steps and the Scalar body result, without a decoder/run/frame premise. -/
theorem negation_body_execution (valid : Array UInt256) (seed : EVM.State)
    (before after : Backend.Program) (a : PrimTy.int.Denote) (tail : Scalar.Stack)
    (fits : (Backend.encode (before ++ [Scalar.pushWord 0])).length < UInt256.size)
    (room : tail.length+2 ≤ 1024) (gas : 6 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Scalar.run Scalar.negationBody (Scalar.encodeValue .int a::tail) =
      some (BitVec.ofInt 256 (-a.val)::tail) ∧
    Assembly.driverSteps 2 (fuel+3) valid (negationBodyInput seed before after a tail) =
      .ok (negationBodyOutput seed before after a tail) ∧
    EVM.X (fuel+3) valid (negationBodyInput seed before after a tail) =
      EVM.X (fuel+1) valid (negationBodyOutput seed before after a tail) := by
  have length : (Backend.encode (before ++ [Scalar.pushWord 0])).length =
      (Backend.encode before).length+33 := by
    simp only [Backend.encode_append,Backend.encode_cons,Backend.encode_nil,
      Scalar.encode_pushWord,List.length_append,List.length_cons,Vector.length_toList,List.length_nil]
  have initialFits : (Backend.encode before).length < UInt256.size := by rw [length] at fits;omega
  have initialGas : 3 ≤ seed.gasAvailable.toNat := by omega
  have initialRoom : (Scalar.encodeValue .int a::tail).length+1 ≤ 1024 := by
    simp only [List.length_cons];omega
  have first := word_push_table_agreement valid seed before (.op .SUB::after) 0
    (Scalar.encodeValue .int a::tail) initialFits initialGas initialRoom (fuel+1)
  have remaining : 3 ≤ (negationBodyPushed seed before after a tail).gasAvailable.toNat := by
    change 3 ≤ (seed.gasAvailable-UInt256.ofNat 3).toNat
    rw [reference_gas_debit seed.gasAvailable 3 initialGas]
    omega
  have second := wrapping_sub_agreement valid
    (negationBodySite (negationBodyPushed seed before after a tail) before after fits)
    0 (Scalar.encodeValue .int a) tail room remaining fuel
  dsimp only at first second
  rw [negation_body_alignment,negation_body_word] at second
  have firstDriver : Assembly.driverSteps 1 (fuel+1+1+1) valid
      (negationBodyInput seed before after a tail) =
      .ok (negationBodyPushed seed before after a tail) := first.2.1
  refine ⟨Scalar.negationBody_typed a tail,?_,?_⟩
  · rw [fetched_steps_append 1 1 (fuel+1),firstDriver]
    exact second.2.1
  · exact first.2.2.trans second.2.2

theorem negation_body_debit (seed : EVM.State) (before after : Backend.Program)
    (a : PrimTy.int.Denote) (tail : Scalar.Stack) (gas : 6 ≤ seed.gasAvailable.toNat) :
    (negationBodyOutput seed before after a tail).gasAvailable.toNat = seed.gasAvailable.toNat-6 := by
  have firstGas : 3 ≤ seed.gasAvailable.toNat := by omega
  have first := reference_gas_debit seed.gasAvailable 3 firstGas
  have remaining : 3 ≤ (seed.gasAvailable-UInt256.ofNat 3).toNat := by rw [first];omega
  have second := reference_gas_debit (seed.gasAvailable-UInt256.ofNat 3) 3 remaining
  change ((seed.gasAvailable-UInt256.ofNat 3)-UInt256.ofNat 3).toNat = _
  rw [second,first,Nat.sub_sub]

theorem negation_body_frame (seed : EVM.State) (before after : Backend.Program)
    (a : PrimTy.int.Denote) (tail : Scalar.Stack) :
    (negationBodyOutput seed before after a tail).toState = (negationBodyInput seed before after a tail).toState ∧
    (negationBodyOutput seed before after a tail).memory = seed.memory ∧
    (negationBodyOutput seed before after a tail).activeWords = seed.activeWords ∧
    (negationBodyOutput seed before after a tail).returnData = seed.returnData ∧
    (negationBodyOutput seed before after a tail).H_return = seed.H_return ∧
    (negationBodyOutput seed before after a tail).stack =
      (BitVec.ofInt 256 (-a.val)::tail).map (fun w => UInt256.mk w.toFin) ∧
    (negationBodyOutput seed before after a tail).execLength = seed.execLength+2 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms negation_body_selection
#print axioms negation_body_word
#print axioms negation_body_code
#print axioms negation_body_alignment
#print axioms negation_body_execution
#print axioms negation_body_debit
#print axioms negation_body_frame
end SolidityBridge.RoadmapV15.P10
