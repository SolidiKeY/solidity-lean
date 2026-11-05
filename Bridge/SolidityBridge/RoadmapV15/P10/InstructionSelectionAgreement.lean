import SolidityBridge.RoadmapV15.P10.ExponentConsumer
import Solidity.Backend.Selection.ArithmeticSelection
import SolidityBridge.Yul.ArithmeticSelection
import SolidityBridge.RoadmapV15.P10.WrappingArithmeticConsumer

/-! Concrete published instruction certificates to actual charged fetched ADD/MUL/SUB/EXP.
Only numeric stacks are related; each model retains its own complete frame.
Physical input origin, full Source/Yul admission and world/Osaka adequacy stay open. -/
namespace SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
namespace Cert
export SolidityBridge.Yul.ArithmeticSelection (add mul)
end Cert

theorem emitted : Cert.add.code=[.op .ADD] ∧ Cert.mul.code=[.op .MUL] := by decide

theorem add (valid : Array UInt256) (site : Site .ADD)
    (a b : Scalar.Word) (tail : Scalar.Stack) (m : Solidity.Evm.Machine)
    (represented : m.stack=Selection.irStack (a::b::tail))
    (room : tail.length+2≤1024) (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      (((a+b)::tail).map (fun w=>UInt256.mk w.toFin))
    Solidity.Evm.Instr.step .add m=.ok {m with stack:=Selection.irStack ((a+b)::tail)} 0 ∧
    Scalar.run Cert.add.code (a::b::tail)=some ((a+b)::tail) ∧
    Assembly.driverSteps 1 (fuel+2) valid input=.ok next ∧
    EVM.X (fuel+2) valid input=EVM.X (fuel+1) valid next ∧
    next.toState=input.toState ∧ next.memory=input.memory ∧
    next.returnData=input.returnData ∧ next.H_return=input.H_return := by
  first
  | solve | rfl
  | solve | decide
  | solve | omega
  | solve | simp only [List.map_cons]
  | dsimp only
    have scalar : Scalar.run Cert.add.code (a::b::tail)=some ((a+b)::tail) := by rfl
    have ir := (Cert.add.success (a::b::tail) ((a+b)::tail) m represented).mpr scalar
    have native := wrapping_add_agreement valid site a b tail room gas fuel
    exact ⟨ir,scalar,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

theorem mul (valid : Array UInt256) (site : Site .MUL)
    (a b : Scalar.Word) (tail : Scalar.Stack) (m : Solidity.Evm.Machine)
    (represented : m.stack=Selection.irStack (a::b::tail))
    (room : tail.length+2≤1024) (gas : 5≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let next := (Assembly.chargedPrepare input 5).replaceStackAndIncrPC
      (((a*b)::tail).map (fun w=>UInt256.mk w.toFin))
    Solidity.Evm.Instr.step .mul m=.ok {m with stack:=Selection.irStack ((a*b)::tail)} 0 ∧
    Scalar.run Cert.mul.code (a::b::tail)=some ((a*b)::tail) ∧
    Assembly.driverSteps 1 (fuel+2) valid input=.ok next ∧
    EVM.X (fuel+2) valid input=EVM.X (fuel+1) valid next ∧
    next.toState=input.toState ∧ next.memory=input.memory ∧
    next.returnData=input.returnData ∧ next.H_return=input.H_return := by
  first
  | solve | rfl
  | solve | decide
  | solve | omega
  | solve | simp only [List.map_cons]
  | dsimp only
    have scalar : Scalar.run Cert.mul.code (a::b::tail)=some ((a*b)::tail) := by rfl
    have ir := (Cert.mul.success (a::b::tail) ((a*b)::tail) m represented).mpr scalar
    have native := wrapping_mul_agreement valid site a b tail room gas fuel
    exact ⟨ir,scalar,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩


/-- Public selected SUB to actual charged fetched subtraction, preserving both
models' complete frames separately. Numeric input origin remains explicit. -/
theorem sub (valid : Array UInt256) (site : Site .SUB)
    (a b : Scalar.Word) (tail : Scalar.Stack) (m : Solidity.Evm.Machine)
    (represented : m.stack=Selection.irStack (a::b::tail))
    (room : tail.length+2≤1024) (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      (((a-b)::tail).map (fun w=>UInt256.mk w.toFin))
    Solidity.Evm.Instr.step .sub m=.ok {m with stack:=Selection.irStack ((a-b)::tail)} 0 ∧
    Scalar.run Selection.subCertificate.code (a::b::tail)=some ((a-b)::tail) ∧
    Assembly.driverSteps 1 (fuel+2) valid input=.ok next ∧
    EVM.X (fuel+2) valid input=EVM.X (fuel+1) valid next ∧
    next.toState=input.toState ∧ next.memory=input.memory ∧
    next.returnData=input.returnData ∧ next.H_return=input.H_return := by
  first
  | solve | rfl
  | solve | simp only
  | solve | decide
  | solve | omega
  | dsimp only
    have scalar : Scalar.run Selection.subCertificate.code (a::b::tail)=some ((a-b)::tail) := by rfl
    have ir := (Selection.subCertificate.success (a::b::tail) ((a-b)::tail) m represented).mpr scalar
    have native := wrapping_sub_agreement valid site a b tail room gas fuel
    exact ⟨ir,scalar,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

/-- Actual component selection, rather than a supplied certificate choice. -/
theorem selected_exp : Selection.selectArithmetic .exp = some Selection.expCertificate := by rfl

/-- Selected EXP retains the exact pinned exponent-byte cost on this input. -/
theorem exp (site : Site .EXP) (a b : Scalar.Word) (tail : Scalar.Stack)
    (m : Solidity.Evm.Machine) (represented : m.stack=Selection.irStack (a::b::tail))
    (room : tail.length+2≤1024)
    (gas : EVM.C' (modularSite site (a::b::tail)).state .EXP≤site.seed.gasAvailable.toNat)
    (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let cost := EVM.C' input .EXP
    let result := BitVec.ofNat 256 (a.toNat ^ b.toNat)
    let next := (Assembly.chargedPrepare input cost).replaceStackAndIncrPC
      ((result::tail).map (fun w=>UInt256.mk w.toFin))
    Solidity.Evm.Instr.step .exp m=.ok {m with stack:=Selection.irStack (result::tail)} 0 ∧
    Scalar.run Selection.expCertificate.code (a::b::tail)=some (result::tail) ∧
    Assembly.driverSteps 1 (fuel+2) #[] input=.ok next ∧
    EVM.X (fuel+2) #[] input=EVM.X (fuel+1) #[] next ∧
    next.toState=input.toState ∧ next.memory=input.memory ∧
    next.returnData=input.returnData ∧ next.H_return=input.H_return := by
  first
  | solve | rfl
  | solve | simp only
  | solve | decide
  | solve | omega
  | dsimp only
    have scalar : Scalar.run Selection.expCertificate.code (a::b::tail)=
        some (BitVec.ofNat 256 (a.toNat ^ b.toNat)::tail) := by rfl
    have ir := (Selection.expCertificate.success _ _ m represented).mpr scalar
    have native := power_agreement site a b tail room gas fuel
    exact ⟨ir,scalar,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

/-- The uniform bound is discharged by the existing intrinsic exponent bound. -/
theorem exp_uniform (site : Site .EXP) (a b : Scalar.Word) (tail : Scalar.Stack)
    (m : Solidity.Evm.Machine) (represented : m.stack=Selection.irStack (a::b::tail))
    (room : tail.length+2≤1024) (gas : 1610≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let result := BitVec.ofNat 256 (a.toNat ^ b.toNat)
    let next := (Assembly.chargedPrepare input (EVM.C' input .EXP)).replaceStackAndIncrPC
      ((result::tail).map (fun w=>UInt256.mk w.toFin))
    Solidity.Evm.Instr.step .exp m=.ok {m with stack:=Selection.irStack (result::tail)} 0 ∧
    Scalar.run Selection.expCertificate.code (a::b::tail)=some (result::tail) ∧
    Assembly.driverSteps 1 (fuel+2) #[] input=.ok next ∧
    EVM.X (fuel+2) #[] input=EVM.X (fuel+1) #[] next ∧
    next.toState=input.toState ∧ next.memory=input.memory ∧
    next.returnData=input.returnData ∧ next.H_return=input.H_return := by
  exact exp site a b tail m represented room (Nat.le_trans (power_cost_bound site a b tail) gas) fuel

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.selected_exp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms selected_exp
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.exp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exp
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.exp_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exp_uniform
#print axioms sub

#print axioms emitted
#print axioms add
#print axioms mul
end SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement
