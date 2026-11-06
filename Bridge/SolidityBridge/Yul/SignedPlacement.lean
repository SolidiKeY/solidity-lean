import SolidityBridge.Yul.QuotientPlacement
import SolidityBridge.RoadmapV15.P10.SignedDivisionConsumer
/-! Actual signed source quotient compiler and concrete charged correspondence.
The existing source signed-word semantics, target definitions and P10 proof
bodies are reused; no word cleaning, state or calling convention is introduced.
Prefix reachability, future suffix validity and Source/G24 remain separate. -/
namespace SolidityBridge.Yul.SignedPlacement
open Solidity Solidity.Yul Solidity.Yul.Closed Solidity.Yul.Compilation
open Backend Scalar Solidity.Evm.External EvmYul
open SolidityBridge.RoadmapV15
open QuotientPlacement

def sdivExpr : Expr [] [] 2 1 :=
  .builtin (.pure .sdiv) (Fin.cases (.local 0) (fun _ => .local 1))
def smodExpr : Expr [] [] 2 1 :=
  .builtin (.pure .smod) (Fin.cases (.local 0) (fun _ => .local 1))
def sdivCompiled := (PureExpressions.compile 2 sdivExpr).get (by rfl)
def smodCompiled := (PureExpressions.compile 2 smodExpr).get (by rfl)

variable (headCode tailCode : Backend.Program)
    (fits : (Backend.encode headCode).length + 3 < UInt256.size)

def sdivFinal (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack) : EVM.State :=
  QuotientPlacement.finish (QuotientPlacement.secondRead headCode tailCode fits seed .SDIV a b caller)
    (sdivCompiled.value #v[a,b]) a b caller

def smodFinal (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack) : EVM.State :=
  QuotientPlacement.finish (QuotientPlacement.secondRead headCode tailCode fits seed .SMOD a b caller)
    (smodCompiled.value #v[a,b]) a b caller


/-- Real signed operation and whole charged read-prefix continuation.
All words, caller data and intermediate States are derived from concrete P10 bodies. -/
theorem sdiv_continuation (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length ≤ 1020) (gas : 11 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) #[] (secondRead headCode tailCode fits seed .SDIV a b caller) = .ok (sdivFinal headCode tailCode fits seed a b caller) ∧
    EVM.X (fuel+4) #[] (entry headCode tailCode fits seed .SDIV a b caller) = EVM.X (fuel+1) #[] (sdivFinal headCode tailCode fits seed a b caller) := by
  have readProof := reads headCode tailCode fits seed .SDIV a b caller room gas fuel
  have input3 : (P10.modularSite (arithmeticSite headCode tailCode fits (secondRead headCode tailCode fits seed .SDIV a b caller) .SDIV)
      (a::b::a::b::caller)).state = secondRead headCode tailCode fits seed .SDIV a b caller := by
    simp only [arithmeticSite,P10.modularSite,P10.Site.state,firstRead,secondRead,entry,firstSite,
      Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,
      Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Backend.Instr.encode,
      ChargedQuotients.reads,List.length_append,List.length_cons,List.length_nil,
      List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,← pc_succ]
  have last := P10.sdiv_agreement (arithmeticSite headCode tailCode fits (secondRead headCode tailCode fits seed .SDIV a b caller) .SDIV) a b (a::b::caller)
    (by simp only [List.length_cons];omega) readProof.2.2.2 fuel
  have final :
      Assembly.driverSteps 1 (fuel+2) #[] (secondRead headCode tailCode fits seed .SDIV a b caller) = .ok (sdivFinal headCode tailCode fits seed a b caller) ∧
      EVM.X (fuel+2) #[] (secondRead headCode tailCode fits seed .SDIV a b caller) = EVM.X (fuel+1) #[] (sdivFinal headCode tailCode fits seed a b caller) := by
    simpa only [input3,sdivFinal,finish] using last.2
  exact ⟨final.1,readProof.2.2.1.trans final.2⟩

/-- Real signed operation and whole charged read-prefix continuation.
All words, caller data and intermediate States are derived from concrete P10 bodies. -/
theorem smod_continuation (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length ≤ 1020) (gas : 11 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) #[] (secondRead headCode tailCode fits seed .SMOD a b caller) = .ok (smodFinal headCode tailCode fits seed a b caller) ∧
    EVM.X (fuel+4) #[] (entry headCode tailCode fits seed .SMOD a b caller) = EVM.X (fuel+1) #[] (smodFinal headCode tailCode fits seed a b caller) := by
  have readProof := reads headCode tailCode fits seed .SMOD a b caller room gas fuel
  have input3 : (P10.modularSite (arithmeticSite headCode tailCode fits (secondRead headCode tailCode fits seed .SMOD a b caller) .SMOD)
      (a::b::a::b::caller)).state = secondRead headCode tailCode fits seed .SMOD a b caller := by
    simp only [arithmeticSite,P10.modularSite,P10.Site.state,firstRead,secondRead,entry,firstSite,
      Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,
      Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Backend.Instr.encode,
      ChargedQuotients.reads,List.length_append,List.length_cons,List.length_nil,
      List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,← pc_succ]
  have last := P10.smod_agreement (arithmeticSite headCode tailCode fits (secondRead headCode tailCode fits seed .SMOD a b caller) .SMOD) a b (a::b::caller)
    (by simp only [List.length_cons];omega) readProof.2.2.2 fuel
  have final :
      Assembly.driverSteps 1 (fuel+2) #[] (secondRead headCode tailCode fits seed .SMOD a b caller) = .ok (smodFinal headCode tailCode fits seed a b caller) ∧
      EVM.X (fuel+2) #[] (secondRead headCode tailCode fits seed .SMOD a b caller) = EVM.X (fuel+1) #[] (smodFinal headCode tailCode fits seed a b caller) := by
    simpa only [input3,smodFinal,finish] using last.2
  exact ⟨final.1,readProof.2.2.1.trans final.2⟩

#print axioms sdiv_continuation
#print axioms smod_continuation
end SolidityBridge.Yul.SignedPlacement
