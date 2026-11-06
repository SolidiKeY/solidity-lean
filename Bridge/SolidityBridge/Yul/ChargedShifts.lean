import SolidityBridge.Yul.QuotientPlacement
import SolidityBridge.RoadmapV15.P10.LogicalShiftConsumer
import Solidity.Yul.Compilation.ShiftSubMachine
/-! Concrete native continuations for the original Yul SHL/SHR compiler slices.
The existing DUP2 prefix theorem supplies a sufficient gas11 contract. The
arithmetic opcode charges three gas; this is not a minimum-gas theorem.
No Source/G24/view/scanner/whole-program adequacy follows. -/
namespace SolidityBridge.Yul.ChargedShifts
open Solidity Solidity.Yul Solidity.Yul.Closed Solidity.Yul.Compilation
open Backend Scalar Solidity.Evm.External EvmYul
open SolidityBridge.RoadmapV15
variable (headCode tailCode : Backend.Program)
    (fits : (Backend.encode headCode).length+3<UInt256.size)

def final (seed : EVM.State) (op : Backend.Op) (result count value : Scalar.Word)
    (caller : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare
    (QuotientPlacement.secondRead headCode tailCode fits seed op count value caller) 3).replaceStackAndIncrPC
    ((result::count::value::caller).map (fun w => UInt256.mk w.toFin))

theorem shl_continuation (seed : EVM.State) (count value : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length≤1020) (gas : 11≤seed.gasAvailable.toNat) (fuel : Nat) :
    evalExpr 2 .nil True.intro ShiftSubMachine.shlExpr ShiftSubMachine.shlCompiled.profile
      (ProducerExpressions.sourceLocals #v[count,value]) =
      some (fun _ => (ShiftSubMachine.shlCompiled.value #v[count,value]).toFin) ∧
    Assembly.driverSteps 1 (fuel+2) #[]
      (QuotientPlacement.secondRead headCode tailCode fits seed .SHL count value caller) =
      .ok (final headCode tailCode fits seed .SHL
        (ShiftSubMachine.shlCompiled.value #v[count,value]) count value caller) ∧
    EVM.X (fuel+4) #[] (QuotientPlacement.entry headCode tailCode fits seed .SHL count value caller) =
      EVM.X (fuel+1) #[] (final headCode tailCode fits seed .SHL
        (ShiftSubMachine.shlCompiled.value #v[count,value]) count value caller) := by
  have reads := QuotientPlacement.reads headCode tailCode fits seed .SHL count value caller room gas fuel
  have input3 : (P10.modularSite
      (QuotientPlacement.arithmeticSite headCode tailCode fits
        (QuotientPlacement.secondRead headCode tailCode fits seed .SHL count value caller) .SHL)
      (count::value::count::value::caller)).state =
      QuotientPlacement.secondRead headCode tailCode fits seed .SHL count value caller := by
    simp only [QuotientPlacement.arithmeticSite,P10.modularSite,P10.Site.state,
      QuotientPlacement.firstRead,QuotientPlacement.secondRead,QuotientPlacement.entry,QuotientPlacement.firstSite,
      Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,
      Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Backend.Instr.encode,
      ChargedQuotients.reads,List.length_append,List.length_cons,List.length_nil,
      List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,← QuotientPlacement.pc_succ]
  have gas3 : 3 ≤ (QuotientPlacement.secondRead headCode tailCode fits seed .SHL count value caller).gasAvailable.toNat := by
    have reserve := reads.2.2.2
    omega
  have last := P10.logical_shl_agreement
    (QuotientPlacement.arithmeticSite headCode tailCode fits
      (QuotientPlacement.secondRead headCode tailCode fits seed .SHL count value caller) .SHL)
    count value (count::value::caller) (by simp only [List.length_cons]; omega) gas3 fuel
  have actual :
      Assembly.driverSteps 1 (fuel+2) #[]
        (QuotientPlacement.secondRead headCode tailCode fits seed .SHL count value caller) =
        .ok (final headCode tailCode fits seed .SHL
          (ShiftSubMachine.shlCompiled.value #v[count,value]) count value caller) ∧
      EVM.X (fuel+2) #[]
        (QuotientPlacement.secondRead headCode tailCode fits seed .SHL count value caller) =
        EVM.X (fuel+1) #[] (final headCode tailCode fits seed .SHL
          (ShiftSubMachine.shlCompiled.value #v[count,value]) count value caller) := by
    simpa only [input3,final] using last.2
  exact ⟨ShiftSubMachine.shlCompiled.source #v[count,value],actual.1,reads.2.2.1.trans actual.2⟩

theorem shr_continuation (seed : EVM.State) (count value : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length≤1020) (gas : 11≤seed.gasAvailable.toNat) (fuel : Nat) :
    evalExpr 2 .nil True.intro ShiftSubMachine.shrExpr ShiftSubMachine.shrCompiled.profile
      (ProducerExpressions.sourceLocals #v[count,value]) =
      some (fun _ => (ShiftSubMachine.shrCompiled.value #v[count,value]).toFin) ∧
    Assembly.driverSteps 1 (fuel+2) #[]
      (QuotientPlacement.secondRead headCode tailCode fits seed .SHR count value caller) =
      .ok (final headCode tailCode fits seed .SHR
        (ShiftSubMachine.shrCompiled.value #v[count,value]) count value caller) ∧
    EVM.X (fuel+4) #[] (QuotientPlacement.entry headCode tailCode fits seed .SHR count value caller) =
      EVM.X (fuel+1) #[] (final headCode tailCode fits seed .SHR
        (ShiftSubMachine.shrCompiled.value #v[count,value]) count value caller) := by
  have reads := QuotientPlacement.reads headCode tailCode fits seed .SHR count value caller room gas fuel
  have input3 : (P10.modularSite
      (QuotientPlacement.arithmeticSite headCode tailCode fits
        (QuotientPlacement.secondRead headCode tailCode fits seed .SHR count value caller) .SHR)
      (count::value::count::value::caller)).state =
      QuotientPlacement.secondRead headCode tailCode fits seed .SHR count value caller := by
    simp only [QuotientPlacement.arithmeticSite,P10.modularSite,P10.Site.state,
      QuotientPlacement.firstRead,QuotientPlacement.secondRead,QuotientPlacement.entry,QuotientPlacement.firstSite,
      Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,
      Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Backend.Instr.encode,
      ChargedQuotients.reads,List.length_append,List.length_cons,List.length_nil,
      List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,← QuotientPlacement.pc_succ]
  have gas3 : 3 ≤ (QuotientPlacement.secondRead headCode tailCode fits seed .SHR count value caller).gasAvailable.toNat := by
    have reserve := reads.2.2.2
    omega
  have last := P10.logical_shr_agreement
    (QuotientPlacement.arithmeticSite headCode tailCode fits
      (QuotientPlacement.secondRead headCode tailCode fits seed .SHR count value caller) .SHR)
    count value (count::value::caller) (by simp only [List.length_cons]; omega) gas3 fuel
  have actual :
      Assembly.driverSteps 1 (fuel+2) #[]
        (QuotientPlacement.secondRead headCode tailCode fits seed .SHR count value caller) =
        .ok (final headCode tailCode fits seed .SHR
          (ShiftSubMachine.shrCompiled.value #v[count,value]) count value caller) ∧
      EVM.X (fuel+2) #[]
        (QuotientPlacement.secondRead headCode tailCode fits seed .SHR count value caller) =
        EVM.X (fuel+1) #[] (final headCode tailCode fits seed .SHR
          (ShiftSubMachine.shrCompiled.value #v[count,value]) count value caller) := by
    simpa only [input3,final] using last.2
  exact ⟨ShiftSubMachine.shrCompiled.source #v[count,value],actual.1,reads.2.2.1.trans actual.2⟩
end SolidityBridge.Yul.ChargedShifts
