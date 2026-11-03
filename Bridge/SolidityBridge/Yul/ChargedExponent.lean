import SolidityBridge.Yul.QuotientPlacement
import SolidityBridge.RoadmapV15.P10.ExponentConsumer
import Solidity.Yul.Compilation.ExponentMachine
/-! Source-indexed native EXP continuation with the exact pinned dynamic cost.
Source/G24/view/scanner and whole Osaka/world/resource/trace closure are separate.
The cost is native resource bookkeeping, not an admitted source observation. -/
namespace SolidityBridge.Yul.ChargedExponent
open Solidity Solidity.Yul Solidity.Yul.Closed Solidity.Yul.Compilation
open Backend Scalar Solidity.Evm.External EvmYul
open SolidityBridge.RoadmapV15

def cost (exponent : Scalar.Word) : Nat :=
  if UInt256.eq0 ⟨exponent.toFin⟩ then 10 else 10+50*(1+Nat.log 256 exponent.toNat)

variable (headCode tailCode : Backend.Program)
    (fits : (Backend.encode headCode).length+3<UInt256.size)

def final (seed : EVM.State) (base exponent : Scalar.Word) (caller : Scalar.Stack) :=
  (Assembly.chargedPrepare
    (QuotientPlacement.secondRead headCode tailCode fits seed .EXP base exponent caller)
    (cost exponent)).replaceStackAndIncrPC
    ((ExponentMachine.compiled.value #v[base,exponent]::base::exponent::caller).map
      (fun w => UInt256.mk w.toFin))

theorem continuation (seed : EVM.State) (base exponent : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length≤1020) (gas : 6+cost exponent≤seed.gasAvailable.toNat) (fuel : Nat) :
    evalExpr 2 .nil True.intro ExponentMachine.expr ExponentMachine.compiled.profile
      (ProducerExpressions.sourceLocals #v[base,exponent]) =
      some (fun _ => (ExponentMachine.compiled.value #v[base,exponent]).toFin) ∧
    Assembly.driverSteps 1 (fuel+2) #[]
      (QuotientPlacement.secondRead headCode tailCode fits seed .EXP base exponent caller) =
      .ok (final headCode tailCode fits seed base exponent caller) ∧
    EVM.X (fuel+4) #[] (QuotientPlacement.entry headCode tailCode fits seed .EXP base exponent caller) =
      EVM.X (fuel+1) #[] (final headCode tailCode fits seed base exponent caller) := by
  have minimum : 10≤cost exponent := by unfold cost; split <;> omega
  have gas11 : 11≤seed.gasAvailable.toNat := by omega
  have reads := QuotientPlacement.reads headCode tailCode fits seed .EXP base exponent caller room gas11 fuel
  have gas0 : 3≤seed.gasAvailable.toNat := by omega
  have charge1 : (QuotientPlacement.firstRead headCode tailCode fits seed .EXP base exponent caller).gasAvailable.toNat = seed.gasAvailable.toNat-3 := Fin.sub_val_of_le gas0
  have gas1 : 3≤(QuotientPlacement.firstRead headCode tailCode fits seed .EXP base exponent caller).gasAvailable.toNat := by rw [charge1]; omega
  have charge2 : (QuotientPlacement.secondRead headCode tailCode fits seed .EXP base exponent caller).gasAvailable.toNat =
      (QuotientPlacement.firstRead headCode tailCode fits seed .EXP base exponent caller).gasAvailable.toNat-3 := Fin.sub_val_of_le gas1
  have reserve : cost exponent≤(QuotientPlacement.secondRead headCode tailCode fits seed .EXP base exponent caller).gasAvailable.toNat := by
    rw [charge2,charge1]; omega
  have input3 : (P10.modularSite
      (QuotientPlacement.arithmeticSite headCode tailCode fits
        (QuotientPlacement.secondRead headCode tailCode fits seed .EXP base exponent caller) .EXP)
      (base::exponent::base::exponent::caller)).state =
      QuotientPlacement.secondRead headCode tailCode fits seed .EXP base exponent caller := by
    simp only [QuotientPlacement.arithmeticSite,P10.modularSite,P10.Site.state,
      QuotientPlacement.firstRead,QuotientPlacement.secondRead,QuotientPlacement.entry,QuotientPlacement.firstSite,
      Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,
      Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Backend.Instr.encode,
      ChargedQuotients.reads,List.length_append,List.length_cons,List.length_nil,
      List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,← QuotientPlacement.pc_succ]
  have realCost : EVM.C' (P10.modularSite
      (QuotientPlacement.arithmeticSite headCode tailCode fits
        (QuotientPlacement.secondRead headCode tailCode fits seed .EXP base exponent caller) .EXP)
      (base::exponent::base::exponent::caller)).state .EXP = cost exponent := by
    exact P10.power_cost _ base exponent (base::exponent::caller)
  have last := P10.power_agreement
    (QuotientPlacement.arithmeticSite headCode tailCode fits
      (QuotientPlacement.secondRead headCode tailCode fits seed .EXP base exponent caller) .EXP)
    base exponent (base::exponent::caller) (by simp only [List.length_cons]; omega)
    (by rw [realCost]; exact reserve) fuel
  have actual :
      Assembly.driverSteps 1 (fuel+2) #[]
        (QuotientPlacement.secondRead headCode tailCode fits seed .EXP base exponent caller) =
        .ok (final headCode tailCode fits seed base exponent caller) ∧
      EVM.X (fuel+2) #[] (QuotientPlacement.secondRead headCode tailCode fits seed .EXP base exponent caller) =
        EVM.X (fuel+1) #[] (final headCode tailCode fits seed base exponent caller) := by
    simpa only [realCost,input3,final] using last.2
  exact ⟨ExponentMachine.compiled.source #v[base,exponent],actual.1,reads.2.2.1.trans actual.2⟩
end SolidityBridge.Yul.ChargedExponent
