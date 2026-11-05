import SolidityBridge.Yul.ArithmeticSelection
import SolidityBridge.RoadmapV15.P10.WrappingArithmeticConsumer

/-! Concrete published instruction certificates to actual charged fetched ADD/MUL.
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

#print axioms emitted
#print axioms add
#print axioms mul
end SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement
