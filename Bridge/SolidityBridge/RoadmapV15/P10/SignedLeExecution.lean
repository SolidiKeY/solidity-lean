import SolidityBridge.RoadmapV15.P10.SignedLeLayout
import SolidityBridge.RoadmapV15.P10.ExponentConsumer

/-! Actual selected signed <= code: SGT then ISZERO, both fetched and charged.
The intermediate predicate, State, PC and remaining gas are derived. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

theorem signed_le_execution (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack)
    (fits : (Backend.encode (before ++ [.op .SGT])).length < UInt256.size)
    (room : tail.length+2 ≤ 1024) (gas : 6 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    let input := signedLeInput seed before after (a::b::tail)
    let compared := signedLeCompared seed before after a b tail
    let next := (Assembly.chargedPrepare compared 3).replaceStackAndIncrPC
      ((Scalar.flag (decide (a.toInt ≤ b.toInt))::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.run Scalar.intLe.code (a::b::tail) = some (Scalar.flag (decide (a.toInt ≤ b.toInt))::tail) ∧
    Assembly.driverSteps 2 (fuel+3) #[] input = .ok next ∧
    EVM.X (fuel+3) #[] input = EVM.X (fuel+1) #[] next := by
  dsimp only
  have initialFits : (Backend.encode before).length < UInt256.size := by
    rw [signed_le_prefix_length] at fits
    omega
  have initialGas : 3 ≤ seed.gasAvailable.toNat := by omega
  let firstSite : Site .SGT := ⟨seed,before,.op .ISZERO::after,initialFits⟩
  have first := signed_gt_agreement firstSite a b tail room initialGas (fuel+1)
  have firstDriver : Assembly.driverSteps 1 (fuel+3) #[] (signedLeInput seed before after (a::b::tail)) =
      .ok (signedLeCompared seed before after a b tail) := by
    simpa only [firstSite,signedLeCompared,signedLeInput,modularSite,Site.state] using first.2.1
  have firstX : EVM.X (fuel+3) #[] (signedLeInput seed before after (a::b::tail)) =
      EVM.X (fuel+2) #[] (signedLeCompared seed before after a b tail) := by
    simpa only [firstSite,signedLeCompared,signedLeInput,modularSite,Site.state] using first.2.2
  have remaining : 3 ≤ (signedLeCompared seed before after a b tail).gasAvailable.toNat := by
    change 3 ≤ (seed.gasAvailable-UInt256.ofNat 3).toNat
    rw [reference_gas_debit seed.gasAvailable 3 initialGas]
    omega
  have second := iszero_agreement #[]
    (signedLeTailSite (signedLeCompared seed before after a b tail) before after fits)
    (Scalar.flag (decide (b.toInt < a.toInt))) tail (by omega) remaining fuel
  dsimp only at second
  rw [signed_le_tail_alignment,Scalar.flag_not_lt] at second
  refine ⟨?_,?_,firstX.trans second.2.2⟩
  · change some (Scalar.flag (Scalar.flag (decide (b.toInt < a.toInt)) == 0)::tail) = _
    rw [Scalar.flag_not_lt]
  · rw [fetched_steps_cons 1 (fuel+1),firstDriver]
    exact second.2.1

theorem selected_signed_le_execution (seed : EVM.State) (before after : Backend.Program)
    (a b : PrimTy.int.Denote) (tail : Scalar.Stack)
    (fits : (Backend.encode (before ++ [.op .SGT])).length < UInt256.size)
    (room : tail.length+2 ≤ 1024) (gas : 6 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    let x := Scalar.encodeValue .int a
    let y := Scalar.encodeValue .int b
    let input := signedLeInput seed before after (x::y::tail)
    let compared := signedLeCompared seed before after x y tail
    let next := (Assembly.chargedPrepare compared 3).replaceStackAndIncrPC
      ((Scalar.flag (decide (x.toInt ≤ y.toInt))::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.run Scalar.intLe.code (x::y::tail) =
      (BinOp.le.evalT (p := .int) rfl a b).map (fun r => Scalar.encodeValue .bool r::tail) ∧
    Assembly.driverSteps 2 (fuel+3) #[] input = .ok next ∧
    EVM.X (fuel+3) #[] input = EVM.X (fuel+1) #[] next := by
  exact ⟨Scalar.intLe.correct a b tail,
    (signed_le_execution seed before after (Scalar.encodeValue .int a) (Scalar.encodeValue .int b)
      tail fits room gas fuel).2⟩

#print axioms signed_le_execution
#print axioms selected_signed_le_execution
end SolidityBridge.RoadmapV15.P10
