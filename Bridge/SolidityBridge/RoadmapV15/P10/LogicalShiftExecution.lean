import SolidityBridge.RoadmapV15.P10.LogicalShiftLayout
import SolidityBridge.RoadmapV15.P10.ExponentConsumer

/-! Actual selected SWAP1 followed by SHL/SHR, with both charged fetched steps.
Intermediate State, decoder/gate facts and remaining resources are derived. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

theorem logical_shl_execution (seed : EVM.State) (before after : Backend.Program)
    (value count : Scalar.Word) (tail : Scalar.Stack)
    (fits : (Backend.encode (before ++ [.op (.SWAP 0)])).length < UInt256.size)
    (room : tail.length+2 ≤ 1024) (gas : 6 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    let input := logicalShiftInput seed before after .SHL (value::count::tail)
    let swapped := logicalShiftSwapped seed before after .SHL value count tail
    let result := if count.toNat < 256 then value <<< count.toNat else 0
    let next := (Assembly.chargedPrepare swapped 3).replaceStackAndIncrPC
      ((result::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.run Scalar.uintShl.code (value::count::tail) = some (result::tail) ∧
    Assembly.driverSteps 2 (fuel+3) #[] input = .ok next ∧
    EVM.X (fuel+3) #[] input = EVM.X (fuel+1) #[] next := by
  dsimp only
  have initialFits : (Backend.encode before).length < UInt256.size := by
    rw [logical_shift_prefix_length] at fits
    omega
  have initialGas : 3 ≤ seed.gasAvailable.toNat := by omega
  let firstSite : Site (.SWAP 0) := ⟨seed,before,.op .SHL::after,initialFits⟩
  have first := swap_family_agreement 0 firstSite [] tail value count rfl
    (by simpa only [List.length_nil,Nat.zero_add] using room) initialGas (fuel+1)
  have firstDriver : Assembly.driverSteps 1 (fuel+3) #[]
      (logicalShiftInput seed before after .SHL (value::count::tail)) =
      .ok (logicalShiftSwapped seed before after .SHL value count tail) := by
    simpa only [firstSite,logicalShiftSwapped,logicalShiftInput,modularSite,Site.state,List.nil_append] using first.2.1
  have firstX : EVM.X (fuel+3) #[] (logicalShiftInput seed before after .SHL (value::count::tail)) =
      EVM.X (fuel+2) #[] (logicalShiftSwapped seed before after .SHL value count tail) := by
    simpa only [firstSite,logicalShiftSwapped,logicalShiftInput,modularSite,Site.state,List.nil_append] using first.2.2
  have remaining : 3 ≤ (logicalShiftSwapped seed before after .SHL value count tail).gasAvailable.toNat := by
    change 3 ≤ (seed.gasAvailable-UInt256.ofNat 3).toNat
    rw [reference_gas_debit seed.gasAvailable 3 initialGas]
    omega
  have second := logical_shl_agreement
    (logicalShiftTailSite (logicalShiftSwapped seed before after .SHL value count tail) before after .SHL fits)
    count value tail room remaining fuel
  dsimp only at second
  rw [logical_shift_tail_alignment] at second
  refine ⟨?_,?_,firstX.trans second.2.2⟩
  · rfl
  · rw [fetched_steps_cons 1 (fuel+1),firstDriver]
    exact second.2.1

/-- Consume the actual intrinsic selected certificate, not an assumed source run. -/
theorem selected_logical_shl_execution (seed : EVM.State) (before after : Backend.Program)
    (value count : PrimTy.uint.Denote) (tail : Scalar.Stack)
    (fits : (Backend.encode (before ++ [.op (.SWAP 0)])).length < UInt256.size)
    (room : tail.length+2 ≤ 1024) (gas : 6 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    let v := Scalar.encodeValue .uint value
    let n := Scalar.encodeValue .uint count
    let input := logicalShiftInput seed before after .SHL (v::n::tail)
    let swapped := logicalShiftSwapped seed before after .SHL v n tail
    let result := if n.toNat < 256 then v <<< n.toNat else 0
    let next := (Assembly.chargedPrepare swapped 3).replaceStackAndIncrPC
      ((result::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.run Scalar.uintShl.code (v::n::tail) =
      (BinOp.shl.evalT (p := .uint) rfl value count).map (fun r => Scalar.encodeValue .uint r::tail) ∧
    Assembly.driverSteps 2 (fuel+3) #[] input = .ok next ∧
    EVM.X (fuel+3) #[] input = EVM.X (fuel+1) #[] next := by
  exact ⟨Scalar.uintShl.correct value count tail,
    (logical_shl_execution seed before after (Scalar.encodeValue .uint value)
      (Scalar.encodeValue .uint count) tail fits room gas fuel).2⟩

theorem logical_shr_execution (seed : EVM.State) (before after : Backend.Program)
    (value count : Scalar.Word) (tail : Scalar.Stack)
    (fits : (Backend.encode (before ++ [.op (.SWAP 0)])).length < UInt256.size)
    (room : tail.length+2 ≤ 1024) (gas : 6 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    let input := logicalShiftInput seed before after .SHR (value::count::tail)
    let swapped := logicalShiftSwapped seed before after .SHR value count tail
    let result := if count.toNat < 256 then value >>> count.toNat else 0
    let next := (Assembly.chargedPrepare swapped 3).replaceStackAndIncrPC
      ((result::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.run Scalar.uintShr.code (value::count::tail) = some (result::tail) ∧
    Assembly.driverSteps 2 (fuel+3) #[] input = .ok next ∧
    EVM.X (fuel+3) #[] input = EVM.X (fuel+1) #[] next := by
  dsimp only
  have initialFits : (Backend.encode before).length < UInt256.size := by
    rw [logical_shift_prefix_length] at fits
    omega
  have initialGas : 3 ≤ seed.gasAvailable.toNat := by omega
  let firstSite : Site (.SWAP 0) := ⟨seed,before,.op .SHR::after,initialFits⟩
  have first := swap_family_agreement 0 firstSite [] tail value count rfl
    (by simpa only [List.length_nil,Nat.zero_add] using room) initialGas (fuel+1)
  have firstDriver : Assembly.driverSteps 1 (fuel+3) #[]
      (logicalShiftInput seed before after .SHR (value::count::tail)) =
      .ok (logicalShiftSwapped seed before after .SHR value count tail) := by
    simpa only [firstSite,logicalShiftSwapped,logicalShiftInput,modularSite,Site.state,List.nil_append] using first.2.1
  have firstX : EVM.X (fuel+3) #[] (logicalShiftInput seed before after .SHR (value::count::tail)) =
      EVM.X (fuel+2) #[] (logicalShiftSwapped seed before after .SHR value count tail) := by
    simpa only [firstSite,logicalShiftSwapped,logicalShiftInput,modularSite,Site.state,List.nil_append] using first.2.2
  have remaining : 3 ≤ (logicalShiftSwapped seed before after .SHR value count tail).gasAvailable.toNat := by
    change 3 ≤ (seed.gasAvailable-UInt256.ofNat 3).toNat
    rw [reference_gas_debit seed.gasAvailable 3 initialGas]
    omega
  have second := logical_shr_agreement
    (logicalShiftTailSite (logicalShiftSwapped seed before after .SHR value count tail) before after .SHR fits)
    count value tail room remaining fuel
  dsimp only at second
  rw [logical_shift_tail_alignment] at second
  refine ⟨?_,?_,firstX.trans second.2.2⟩
  · rfl
  · rw [fetched_steps_cons 1 (fuel+1),firstDriver]
    exact second.2.1

/-- Consume the actual intrinsic selected certificate, not an assumed source run. -/
theorem selected_logical_shr_execution (seed : EVM.State) (before after : Backend.Program)
    (value count : PrimTy.uint.Denote) (tail : Scalar.Stack)
    (fits : (Backend.encode (before ++ [.op (.SWAP 0)])).length < UInt256.size)
    (room : tail.length+2 ≤ 1024) (gas : 6 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    let v := Scalar.encodeValue .uint value
    let n := Scalar.encodeValue .uint count
    let input := logicalShiftInput seed before after .SHR (v::n::tail)
    let swapped := logicalShiftSwapped seed before after .SHR v n tail
    let result := if n.toNat < 256 then v >>> n.toNat else 0
    let next := (Assembly.chargedPrepare swapped 3).replaceStackAndIncrPC
      ((result::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.run Scalar.uintShr.code (v::n::tail) =
      (BinOp.shr.evalT (p := .uint) rfl value count).map (fun r => Scalar.encodeValue .uint r::tail) ∧
    Assembly.driverSteps 2 (fuel+3) #[] input = .ok next ∧
    EVM.X (fuel+3) #[] input = EVM.X (fuel+1) #[] next := by
  exact ⟨Scalar.uintShr.correct value count tail,
    (logical_shr_execution seed before after (Scalar.encodeValue .uint value)
      (Scalar.encodeValue .uint count) tail fits room gas fuel).2⟩

#print axioms logical_shl_execution
#print axioms selected_logical_shl_execution
#print axioms logical_shr_execution
#print axioms selected_logical_shr_execution
end SolidityBridge.RoadmapV15.P10
