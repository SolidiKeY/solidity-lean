import SolidityBridge.RoadmapV15.P10.SignedDivisionConsumer
import SolidityBridge.RoadmapV15.P10.SignedLePrimitive
import Solidity.Backend.Selection.SignedSelection
import SolidityBridge.RoadmapV15.P10.SignedGeConsumer
import SolidityBridge.RoadmapV15.P10.UintNotConsumer
import SolidityBridge.RoadmapV15.P10.BitwiseConsumer
import SolidityBridge.RoadmapV15.P10.UnsignedOrderConsumer
import SolidityBridge.RoadmapV15.P10.EqualityConsumer
import SolidityBridge.RoadmapV15.P10.BooleanNotConsumer
import SolidityBridge.RoadmapV15.P10.LogicalShiftConsumer
import Solidity.Backend.Selection.UnsignedSelection
import SolidityBridge.RoadmapV15.P10.UnsignedDivisionConsumer
import SolidityBridge.RoadmapV15.P10.ExponentConsumer
import Solidity.Backend.Selection.ArithmeticSelection
import SolidityBridge.Yul.ArithmeticSelection
import SolidityBridge.RoadmapV15.P10.WrappingArithmeticConsumer

/-! Published numeric instruction certificates to actual charged fetched execution.
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

theorem selected_div_mod :
    Selection.selectUnsigned .div=some Selection.divCertificate ∧
    Selection.selectUnsigned .mod=some Selection.modCertificate := by
  first | decide | exact ⟨rfl,rfl⟩

theorem div (site : Site .DIV) (a b : Scalar.Word) (tail : Scalar.Stack)
    (m : Solidity.Evm.Machine) (represented : m.stack=Selection.irStack (a::b::tail))
    (room : tail.length+2≤1024) (gas : 5≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let result := (if b == 0 then (0 : Scalar.Word) else BitVec.ofNat 256 (a.toNat / b.toNat))
    let next := (Assembly.chargedPrepare input 5).replaceStackAndIncrPC
      ((result::tail).map (fun w=>UInt256.mk w.toFin))
    Solidity.Evm.Instr.step .div m=.ok {m with stack:=Selection.irStack (result::tail)} 0 ∧
    Scalar.run Selection.divCertificate.code (a::b::tail)=some (result::tail) ∧
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
    have scalar : Scalar.run Selection.divCertificate.code (a::b::tail)=some ((if b == 0 then (0 : Scalar.Word) else BitVec.ofNat 256 (a.toNat / b.toNat))::tail) := by rfl
    have ir := (Selection.divCertificate.success _ _ m represented).mpr scalar
    have native := div_agreement site a b tail room gas fuel
    exact ⟨ir,scalar,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

theorem mod (site : Site .MOD) (a b : Scalar.Word) (tail : Scalar.Stack)
    (m : Solidity.Evm.Machine) (represented : m.stack=Selection.irStack (a::b::tail))
    (room : tail.length+2≤1024) (gas : 5≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let result := (if b == 0 then (0 : Scalar.Word) else BitVec.ofNat 256 (a.toNat % b.toNat))
    let next := (Assembly.chargedPrepare input 5).replaceStackAndIncrPC
      ((result::tail).map (fun w=>UInt256.mk w.toFin))
    Solidity.Evm.Instr.step .mod m=.ok {m with stack:=Selection.irStack (result::tail)} 0 ∧
    Scalar.run Selection.modCertificate.code (a::b::tail)=some (result::tail) ∧
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
    have scalar : Scalar.run Selection.modCertificate.code (a::b::tail)=some ((if b == 0 then (0 : Scalar.Word) else BitVec.ofNat 256 (a.toNat % b.toNat))::tail) := by rfl
    have ir := (Selection.modCertificate.success _ _ m represented).mpr scalar
    have native := mod_agreement site a b tail room gas fuel
    exact ⟨ir,scalar,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.selected_div_mod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms selected_div_mod
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.div' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms div
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.mod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mod

theorem selected_shifts :
    Selection.selectUnsigned .shl=some Selection.shlCertificate ∧
    Selection.selectUnsigned .shr=some Selection.shrCertificate := by
  first | decide | exact ⟨rfl,rfl⟩

theorem shl (site : Site .SHL) (count value : Scalar.Word) (tail : Scalar.Stack)
    (m : Solidity.Evm.Machine) (represented : m.stack=Selection.irStack (count::value::tail))
    (room : tail.length+2≤1024) (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (count::value::tail)).state
    let result := (if count.toNat < 256 then value <<< count.toNat else (0 : Scalar.Word))
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((result::tail).map (fun w=>UInt256.mk w.toFin))
    Solidity.Evm.Instr.step .shl m=.ok {m with stack:=Selection.irStack (result::tail)} 0 ∧
    Scalar.run Selection.shlCertificate.code (count::value::tail)=some (result::tail) ∧
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
    have scalar : Scalar.run Selection.shlCertificate.code (count::value::tail)=some ((if count.toNat < 256 then value <<< count.toNat else (0 : Scalar.Word))::tail) := by rfl
    have ir := (Selection.shlCertificate.success _ _ m represented).mpr scalar
    have native := logical_shl_agreement site count value tail room gas fuel
    exact ⟨ir,scalar,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

theorem shr (site : Site .SHR) (count value : Scalar.Word) (tail : Scalar.Stack)
    (m : Solidity.Evm.Machine) (represented : m.stack=Selection.irStack (count::value::tail))
    (room : tail.length+2≤1024) (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (count::value::tail)).state
    let result := (if count.toNat < 256 then value >>> count.toNat else (0 : Scalar.Word))
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((result::tail).map (fun w=>UInt256.mk w.toFin))
    Solidity.Evm.Instr.step .shr m=.ok {m with stack:=Selection.irStack (result::tail)} 0 ∧
    Scalar.run Selection.shrCertificate.code (count::value::tail)=some (result::tail) ∧
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
    have scalar : Scalar.run Selection.shrCertificate.code (count::value::tail)=some ((if count.toNat < 256 then value >>> count.toNat else (0 : Scalar.Word))::tail) := by rfl
    have ir := (Selection.shrCertificate.success _ _ m represented).mpr scalar
    have native := logical_shr_agreement site count value tail room gas fuel
    exact ⟨ir,scalar,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.selected_shifts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms selected_shifts
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.shl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shl
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.shr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shr

theorem selected_flags :
    Selection.selectBitwiseComparison .eq=some Selection.eqCertificate ∧
    Selection.selectBitwiseComparison .iszero=some Selection.iszeroCertificate := by
  first | decide | exact ⟨rfl,rfl⟩

theorem eq (valid : Array UInt256) (site : Site .EQ) (a b : Scalar.Word) (tail : Scalar.Stack)
    (m : Solidity.Evm.Machine) (represented : m.stack=Selection.irStack (a::b::tail))
    (room : tail.length+2≤1024) (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let result := Scalar.flag (a == b)
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((result::tail).map (fun w=>UInt256.mk w.toFin))
    Solidity.Evm.Instr.step .eq m=.ok {m with stack:=Selection.irStack (result::tail)} 0 ∧
    Scalar.run Selection.eqCertificate.code (a::b::tail)=some (result::tail) ∧
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
    have scalar : Scalar.run Selection.eqCertificate.code (a::b::tail)=some (Scalar.flag (a == b)::tail) := by rfl
    have ir := (Selection.eqCertificate.success _ _ m represented).mpr scalar
    have native := equality_agreement valid site a b tail room gas fuel
    exact ⟨ir,scalar,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

theorem iszero (valid : Array UInt256) (site : Site .ISZERO) (a : Scalar.Word) (tail : Scalar.Stack)
    (m : Solidity.Evm.Machine) (represented : m.stack=Selection.irStack (a::tail))
    (room : tail.length+1≤1024) (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::tail)).state
    let result := Scalar.flag (a == 0)
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((result::tail).map (fun w=>UInt256.mk w.toFin))
    Solidity.Evm.Instr.step .iszero m=.ok {m with stack:=Selection.irStack (result::tail)} 0 ∧
    Scalar.run Selection.iszeroCertificate.code (a::tail)=some (result::tail) ∧
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
    have scalar : Scalar.run Selection.iszeroCertificate.code (a::tail)=some (Scalar.flag (a == 0)::tail) := by rfl
    have ir := (Selection.iszeroCertificate.success _ _ m represented).mpr scalar
    have native := iszero_agreement valid site a tail room gas fuel
    exact ⟨ir,scalar,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.selected_flags' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms selected_flags
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms eq
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.iszero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms iszero

theorem selected_order :
    Selection.selectBitwiseComparison .lt=some Selection.ltCertificate ∧
    Selection.selectBitwiseComparison .gt=some Selection.gtCertificate := by
  first | decide | exact ⟨rfl,rfl⟩

theorem lt (valid : Array UInt256) (site : Site .LT) (a b : Scalar.Word) (tail : Scalar.Stack)
    (m : Solidity.Evm.Machine) (represented : m.stack=Selection.irStack (a::b::tail))
    (room : tail.length+2≤1024) (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let result := Scalar.flag (decide (a.toNat < b.toNat))
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((result::tail).map (fun w=>UInt256.mk w.toFin))
    Solidity.Evm.Instr.step .lt m=.ok {m with stack:=Selection.irStack (result::tail)} 0 ∧
    Scalar.run Selection.ltCertificate.code (a::b::tail)=some (result::tail) ∧
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
    have scalar : Scalar.run Selection.ltCertificate.code (a::b::tail)=some (Scalar.flag (decide (a.toNat < b.toNat))::tail) := by rfl
    have ir := (Selection.ltCertificate.success _ _ m represented).mpr scalar
    have native := unsigned_lt_agreement valid site a b tail room gas fuel
    exact ⟨ir,scalar,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

theorem gt (valid : Array UInt256) (site : Site .GT) (a b : Scalar.Word) (tail : Scalar.Stack)
    (m : Solidity.Evm.Machine) (represented : m.stack=Selection.irStack (a::b::tail))
    (room : tail.length+2≤1024) (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let result := Scalar.flag (decide (a.toNat > b.toNat))
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((result::tail).map (fun w=>UInt256.mk w.toFin))
    Solidity.Evm.Instr.step .gt m=.ok {m with stack:=Selection.irStack (result::tail)} 0 ∧
    Scalar.run Selection.gtCertificate.code (a::b::tail)=some (result::tail) ∧
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
    have scalar : Scalar.run Selection.gtCertificate.code (a::b::tail)=some (Scalar.flag (decide (a.toNat > b.toNat))::tail) := by rfl
    have ir := (Selection.gtCertificate.success _ _ m represented).mpr scalar
    have native := unsigned_gt_agreement valid site a b tail room gas fuel
    exact ⟨ir,scalar,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.selected_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms selected_order
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms lt
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.gt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms gt
theorem selected_and_or :
    Selection.selectBitwiseComparison .and=some Selection.andCertificate ∧
    Selection.selectBitwiseComparison .or=some Selection.orCertificate := by
  first | decide | exact ⟨rfl,rfl⟩

theorem bitAnd (site : Site .AND) (a b : Scalar.Word) (tail : Scalar.Stack)
    (m : Solidity.Evm.Machine) (represented : m.stack=Selection.irStack (a::b::tail))
    (room : tail.length+2≤1024) (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let result := (a &&& b)
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((result::tail).map (fun w=>UInt256.mk w.toFin))
    Solidity.Evm.Instr.step .and m=.ok {m with stack:=Selection.irStack (result::tail)} 0 ∧
    Scalar.run Selection.andCertificate.code (a::b::tail)=some (result::tail) ∧
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
    have scalar : Scalar.run Selection.andCertificate.code (a::b::tail)=some ((a &&& b)::tail) := by rfl
    have ir := (Selection.andCertificate.success _ _ m represented).mpr scalar
    have native := bitwise_and_agreement site a b tail room gas fuel
    exact ⟨ir,scalar,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

theorem bitOr (site : Site .OR) (a b : Scalar.Word) (tail : Scalar.Stack)
    (m : Solidity.Evm.Machine) (represented : m.stack=Selection.irStack (a::b::tail))
    (room : tail.length+2≤1024) (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let result := (a ||| b)
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((result::tail).map (fun w=>UInt256.mk w.toFin))
    Solidity.Evm.Instr.step .or m=.ok {m with stack:=Selection.irStack (result::tail)} 0 ∧
    Scalar.run Selection.orCertificate.code (a::b::tail)=some (result::tail) ∧
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
    have scalar : Scalar.run Selection.orCertificate.code (a::b::tail)=some ((a ||| b)::tail) := by rfl
    have ir := (Selection.orCertificate.success _ _ m represented).mpr scalar
    have native := bitwise_or_agreement site a b tail room gas fuel
    exact ⟨ir,scalar,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.selected_and_or' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms selected_and_or
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.bitAnd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bitAnd
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.bitOr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bitOr
theorem selected_xor : Selection.selectBitwiseComparison .xor=some Selection.xorCertificate := by
  rfl

theorem bitXor (site : Site .XOR) (a b : Scalar.Word) (tail : Scalar.Stack)
    (m : Solidity.Evm.Machine) (represented : m.stack=Selection.irStack (a::b::tail))
    (room : tail.length+2≤1024) (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let result := (a ^^^ b)
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((result::tail).map (fun w=>UInt256.mk w.toFin))
    Solidity.Evm.Instr.step .xor m=.ok {m with stack:=Selection.irStack (result::tail)} 0 ∧
    Scalar.run Selection.xorCertificate.code (a::b::tail)=some (result::tail) ∧
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
    have scalar : Scalar.run Selection.xorCertificate.code (a::b::tail)=some ((a ^^^ b)::tail) := by rfl
    have ir := (Selection.xorCertificate.success _ _ m represented).mpr scalar
    have native := bitwise_xor_agreement site a b tail room gas fuel
    exact ⟨ir,scalar,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.selected_xor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms selected_xor
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.bitXor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bitXor
theorem selected_not : Selection.selectBitwiseComparison .not=some Selection.notCertificate := by
  rfl

theorem bitNot (valid : Array UInt256) (site : Site .NOT) (a : Scalar.Word) (tail : Scalar.Stack)
    (m : Solidity.Evm.Machine) (represented : m.stack=Selection.irStack (a::tail))
    (room : tail.length+1≤1024) (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::tail)).state
    let result := (~~~a)
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((result::tail).map (fun w=>UInt256.mk w.toFin))
    Solidity.Evm.Instr.step .not m=.ok {m with stack:=Selection.irStack (result::tail)} 0 ∧
    Scalar.run Selection.notCertificate.code (a::tail)=some (result::tail) ∧
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
    have scalar : Scalar.run Selection.notCertificate.code (a::tail)=some ((~~~a)::tail) := by rfl
    have ir := (Selection.notCertificate.success _ _ m represented).mpr scalar
    have native := uint_not_agreement valid site a tail room gas fuel
    exact ⟨ir,scalar,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.selected_not' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms selected_not
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.bitNot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bitNot
theorem selected_slt : Selection.selectSigned .slt=some Selection.sltCertificate := by
  rfl

theorem slt (valid : Array UInt256) (site : Site .SLT) (a b : Scalar.Word) (tail : Scalar.Stack)
    (m : Solidity.Evm.Machine) (represented : m.stack=Selection.irStack (a::b::tail))
    (room : tail.length+2≤1024) (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let result := Scalar.flag (decide (a.toInt < b.toInt))
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((result::tail).map (fun w=>UInt256.mk w.toFin))
    Solidity.Evm.Instr.step .slt m=.ok {m with stack:=Selection.irStack (result::tail)} 0 ∧
    Scalar.run Selection.sltCertificate.code (a::b::tail)=some (result::tail) ∧
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
    have scalar : Scalar.run Selection.sltCertificate.code (a::b::tail)=some (Scalar.flag (decide (a.toInt < b.toInt))::tail) := by rfl
    have ir := (Selection.sltCertificate.success _ _ m represented).mpr scalar
    have native := signed_lt_agreement valid site a b tail room gas fuel
    exact ⟨ir,scalar,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.selected_slt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms selected_slt
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.slt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms slt
theorem selected_sgt : Selection.selectSigned .sgt=some Selection.sgtCertificate := by
  rfl

theorem sgt (site : Site .SGT) (a b : Scalar.Word) (tail : Scalar.Stack)
    (m : Solidity.Evm.Machine) (represented : m.stack=Selection.irStack (a::b::tail))
    (room : tail.length+2≤1024) (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let result := Scalar.flag (decide (b.toInt < a.toInt))
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((result::tail).map (fun w=>UInt256.mk w.toFin))
    Solidity.Evm.Instr.step .sgt m=.ok {m with stack:=Selection.irStack (result::tail)} 0 ∧
    Scalar.run Selection.sgtCertificate.code (a::b::tail)=some (result::tail) ∧
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
    have scalar : Scalar.run Selection.sgtCertificate.code (a::b::tail)=some (Scalar.flag (decide (b.toInt < a.toInt))::tail) := by rfl
    have ir := (Selection.sgtCertificate.success _ _ m represented).mpr scalar
    have native := signed_gt_agreement site a b tail room gas fuel
    exact ⟨ir,scalar,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.selected_sgt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms selected_sgt
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.sgt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sgt
theorem selected_sdiv : Selection.selectSigned .sdiv=some Selection.sdivCertificate := by
  rfl

theorem sdiv (site : Site .SDIV) (a b : Scalar.Word) (tail : Scalar.Stack)
    (m : Solidity.Evm.Machine) (represented : m.stack=Selection.irStack (a::b::tail))
    (room : tail.length+2≤1024) (gas : 5≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let result := (if b == 0 then (0 : Scalar.Word) else BitVec.ofInt 256 (a.toInt.tdiv b.toInt))
    let next := (Assembly.chargedPrepare input 5).replaceStackAndIncrPC
      ((result::tail).map (fun w=>UInt256.mk w.toFin))
    Solidity.Evm.Instr.step .sdiv m=.ok {m with stack:=Selection.irStack (result::tail)} 0 ∧
    Scalar.run Selection.sdivCertificate.code (a::b::tail)=some (result::tail) ∧
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
    have scalar : Scalar.run Selection.sdivCertificate.code (a::b::tail)=some ((if b == 0 then (0 : Scalar.Word) else BitVec.ofInt 256 (a.toInt.tdiv b.toInt))::tail) := by rfl
    have ir := (Selection.sdivCertificate.success _ _ m represented).mpr scalar
    have native := sdiv_agreement site a b tail room gas fuel
    exact ⟨ir,scalar,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.selected_sdiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms selected_sdiv
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.sdiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sdiv
theorem selected_smod : Selection.selectSigned .smod=some Selection.smodCertificate := by
  rfl

theorem smod (site : Site .SMOD) (a b : Scalar.Word) (tail : Scalar.Stack)
    (m : Solidity.Evm.Machine) (represented : m.stack=Selection.irStack (a::b::tail))
    (room : tail.length+2≤1024) (gas : 5≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let result := (if b == 0 then (0 : Scalar.Word) else BitVec.ofInt 256 (a.toInt.tmod b.toInt))
    let next := (Assembly.chargedPrepare input 5).replaceStackAndIncrPC
      ((result::tail).map (fun w=>UInt256.mk w.toFin))
    Solidity.Evm.Instr.step .smod m=.ok {m with stack:=Selection.irStack (result::tail)} 0 ∧
    Scalar.run Selection.smodCertificate.code (a::b::tail)=some (result::tail) ∧
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
    have scalar : Scalar.run Selection.smodCertificate.code (a::b::tail)=some ((if b == 0 then (0 : Scalar.Word) else BitVec.ofInt 256 (a.toInt.tmod b.toInt))::tail) := by rfl
    have ir := (Selection.smodCertificate.success _ _ m represented).mpr scalar
    have native := smod_agreement site a b tail room gas fuel
    exact ⟨ir,scalar,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.selected_smod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms selected_smod
/-- info: 'SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement.smod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms smod
end SolidityBridge.RoadmapV15.P10.InstructionSelectionAgreement
