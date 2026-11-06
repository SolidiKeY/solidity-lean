import Solidity.Backend.Selection.StackSelection
import SolidityBridge.RoadmapV15.P10.StackFamilyConsumer
import SolidityBridge.RoadmapV15.P10.PopConsumer

/-! Published typed IR selection to actual fetched DUP/SWAP families and POP. Each
machine retains its own full frame. The numeric initial-stack relation is not
Source/compiler input origin or full Osaka/resource adequacy. -/
namespace SolidityBridge.RoadmapV15.P10.StackSelectionAgreement
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

theorem selected_dup (n : Fin 16) :
    Selection.selectStack (.dup (n.val+1)) = some (Selection.dupCertificate n) := by
  first | rfl | simp only [Selection.selectStack, dif_pos n.isLt]

theorem selected_swap (n : Fin 16) :
    Selection.selectStack (.swap (n.val+1)) = some (Selection.swapCertificate n) := by
  first | rfl | simp only [Selection.selectStack, dif_pos n.isLt]

theorem dup (n : Fin 16) (site : Site (.DUP n))
    (pre tail : Scalar.Stack) (a : Scalar.Word) (depth : pre.length=n.val)
    (m : Solidity.Evm.Machine) (represented : m.stack=Selection.irStack (pre ++ a::tail))
    (room : pre.length+tail.length+2≤1024) (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (pre ++ a::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((a::(pre ++ a::tail)).map (fun w=>UInt256.mk w.toFin))
    Solidity.Evm.Instr.step (.dup (n.val+1)) m =
      .ok {m with stack:=Selection.irStack (a::(pre ++ a::tail))} 0 ∧
    Scalar.run (Selection.dupCertificate n).code (pre ++ a::tail) = some (a::(pre ++ a::tail)) ∧
    Assembly.driverSteps 1 (fuel+2) #[] input=.ok next ∧
    EVM.X (fuel+2) #[] input=EVM.X (fuel+1) #[] next ∧
    next.toState=input.toState ∧ next.memory=input.memory ∧
    next.returnData=input.returnData ∧ next.H_return=input.H_return := by
  first
  | solve | simp only
  | solve | omega
  | dsimp only
    have native := dup_family_agreement n site pre tail a depth room gas fuel
    have scalar : Scalar.run (Selection.dupCertificate n).code (pre ++ a::tail) =
        some (a::(pre ++ a::tail)) := by
      change (Scalar.step (.op (.DUP n)) (pre ++ a::tail)).bind (fun output=>some output) = _
      rw [native.1]
      rfl
    have ir := (Selection.dupCertificate n).success (pre ++ a::tail) (a::(pre ++ a::tail)) m represented
    exact ⟨ir.mpr scalar,scalar,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

theorem swap (n : Fin 16) (site : Site (.SWAP n))
    (middle tail : Scalar.Stack) (a b : Scalar.Word) (depth : middle.length=n.val)
    (m : Solidity.Evm.Machine) (represented : m.stack=Selection.irStack (a::(middle ++ b::tail)))
    (room : middle.length+tail.length+2≤1024) (gas : 3≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::(middle ++ b::tail))).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((b::(middle ++ a::tail)).map (fun w=>UInt256.mk w.toFin))
    Solidity.Evm.Instr.step (.swap (n.val+1)) m =
      .ok {m with stack:=Selection.irStack (b::(middle ++ a::tail))} 0 ∧
    Scalar.run (Selection.swapCertificate n).code (a::(middle ++ b::tail)) = some (b::(middle ++ a::tail)) ∧
    Assembly.driverSteps 1 (fuel+2) #[] input=.ok next ∧
    EVM.X (fuel+2) #[] input=EVM.X (fuel+1) #[] next ∧
    next.toState=input.toState ∧ next.memory=input.memory ∧
    next.returnData=input.returnData ∧ next.H_return=input.H_return := by
  first
  | solve | simp only
  | solve | omega
  | dsimp only
    have native := swap_family_agreement n site middle tail a b depth room gas fuel
    have scalar : Scalar.run (Selection.swapCertificate n).code (a::(middle ++ b::tail)) =
        some (b::(middle ++ a::tail)) := by
      change (Scalar.step (.op (.SWAP n)) (a::(middle ++ b::tail))).bind (fun output=>some output) = _
      rw [native.1]
      rfl
    have ir := (Selection.swapCertificate n).success (a::(middle ++ b::tail)) (b::(middle ++ a::tail)) m represented
    exact ⟨ir.mpr scalar,scalar,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

/-- Public selection chooses the original POP certificate. -/
theorem selected_pop : Selection.selectStack .pop = some Selection.popCertificate := by rfl

theorem pop (valid : Array UInt256) (site : Site .POP)
    (a : Scalar.Word) (tail : Scalar.Stack) (m : Solidity.Evm.Machine)
    (represented : m.stack=Selection.irStack (a::tail))
    (room : tail.length+1≤1024) (gas : 2≤site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::tail)).state
    let next := (Assembly.chargedPrepare input 2).replaceStackAndIncrPC
      (tail.map (fun w=>UInt256.mk w.toFin))
    Solidity.Evm.Instr.step .pop m=.ok {m with stack:=Selection.irStack tail} 0 ∧
    Scalar.run Selection.popCertificate.code (a::tail)=some tail ∧
    Assembly.driverSteps 1 (fuel+2) valid input=.ok next ∧
    EVM.X (fuel+2) valid input=EVM.X (fuel+1) valid next ∧
    next.toState=input.toState ∧ next.memory=input.memory ∧
    next.returnData=input.returnData ∧ next.H_return=input.H_return := by
  first
  | solve | simp only
  | solve | omega
  | dsimp only
    have scalar : Scalar.run Selection.popCertificate.code (a::tail)=some tail := by rfl
    have ir := Selection.popCertificate.success (a::tail) tail m represented
    have native := pop_agreement valid site a tail room gas fuel
    exact ⟨ir.mpr scalar,scalar,native.2.1,native.2.2,rfl,rfl,rfl,rfl⟩

#print axioms selected_pop
#print axioms pop
#print axioms selected_dup
#print axioms selected_swap
#print axioms dup
#print axioms swap
end SolidityBridge.RoadmapV15.P10.StackSelectionAgreement
