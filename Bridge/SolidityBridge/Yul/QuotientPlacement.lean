import SolidityBridge.Yul.ChargedQuotients
import SolidityBridge.RoadmapV15.P10.StackFamilyConsumer
/-! Charged source quotient slices at arbitrary encoded program offsets.
The bound covers all three instruction PCs and their continuation without wrapping.
No reachability of the prefix, suffix validity or Source/G24 adequacy is assumed. -/
namespace SolidityBridge.Yul.QuotientPlacement
open Solidity Solidity.Yul.Compilation Backend Scalar
open Solidity.Evm.External EvmYul
open SolidityBridge.RoadmapV15

theorem pc_succ (n : Nat) :
    UInt256.ofNat (n+1) = UInt256.ofNat n + UInt256.ofNat 1 := by
  apply congrArg UInt256.mk
  apply Fin.ext
  exact Nat.add_mod _ _ _

variable (headCode tailCode : Backend.Program)
    (fits : (Backend.encode headCode).length + 3 < UInt256.size)

def firstSite (seed : EVM.State) (op : Backend.Op) : P10.Site (.DUP 1) where
  seed := seed
  before := headCode
  after := .op (.DUP 1) :: .op op :: tailCode
  pcFits := by omega

def entry (seed : EVM.State) (op : Backend.Op) (a b : Scalar.Word) (caller : Scalar.Stack) : EVM.State :=
  (P10.modularSite (firstSite headCode tailCode fits seed op) (a::b::caller)).state

def firstRead (seed : EVM.State) (op : Backend.Op) (a b : Scalar.Word) (caller : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (entry headCode tailCode fits seed op a b caller) 3).replaceStackAndIncrPC
    ((b::a::b::caller).map (fun w => UInt256.mk w.toFin))

def secondSite (seed : EVM.State) (op : Backend.Op) (a b : Scalar.Word) (caller : Scalar.Stack) : P10.Site (.DUP 1) where
  seed := firstRead headCode tailCode fits seed op a b caller
  before := headCode ++ [.op (.DUP 1)]
  after := .op op :: tailCode
  pcFits := by simp only [Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Instr.encode,List.length_append,List.length_cons,List.length_nil]; omega

def secondRead (seed : EVM.State) (op : Backend.Op) (a b : Scalar.Word) (caller : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (firstRead headCode tailCode fits seed op a b caller) 3).replaceStackAndIncrPC
    ((a::b::a::b::caller).map (fun w => UInt256.mk w.toFin))

def finish (input : EVM.State) (value a b : Scalar.Word) (caller : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare input 5).replaceStackAndIncrPC
    ((value::a::b::caller).map (fun w => UInt256.mk w.toFin))

def arithmeticSite (seed : EVM.State) (op : Backend.Op) : P10.Site op where
  seed := seed
  before := headCode ++ ChargedQuotients.reads
  after := tailCode
  pcFits := by simp only [ChargedQuotients.reads,Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Instr.encode,List.length_append,List.length_cons,List.length_nil]; omega

def divFinal (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack) : EVM.State :=
  finish (secondRead headCode tailCode fits seed .DIV a b caller) (ChargedQuotients.divCompiled.value #v[a,b]) a b caller
def modFinal (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack) : EVM.State :=
  finish (secondRead headCode tailCode fits seed .MOD a b caller) (ChargedQuotients.modCompiled.value #v[a,b]) a b caller

/-- Two actual charged reads, with their exact intermediate State and X path.
Initial gas11 and peak capacity derive the later gas5/capacity obligations.
No desired step, intermediate gate or continuation is an input premise. -/
theorem reads (seed : EVM.State) (op : Backend.Op) (a b : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length ≤ 1020) (gas : 11 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+4) #[] (entry headCode tailCode fits seed op a b caller) = .ok (firstRead headCode tailCode fits seed op a b caller) ∧
    Assembly.driverSteps 1 (fuel+3) #[] (firstRead headCode tailCode fits seed op a b caller) = .ok (secondRead headCode tailCode fits seed op a b caller) ∧
    EVM.X (fuel+4) #[] (entry headCode tailCode fits seed op a b caller) = EVM.X (fuel+2) #[] (secondRead headCode tailCode fits seed op a b caller) ∧
    5 ≤ (secondRead headCode tailCode fits seed op a b caller).gasAvailable.toNat := by
  have gas0 : 3 ≤ seed.gasAvailable.toNat := by omega
  have charge1 : (firstRead headCode tailCode fits seed op a b caller).gasAvailable.toNat = seed.gasAvailable.toNat-3 :=
    Fin.sub_val_of_le gas0
  have gas1 : 3 ≤ (firstRead headCode tailCode fits seed op a b caller).gasAvailable.toNat := by rw [charge1];omega
  have charge2 : (secondRead headCode tailCode fits seed op a b caller).gasAvailable.toNat =
      (firstRead headCode tailCode fits seed op a b caller).gasAvailable.toNat-3 := Fin.sub_val_of_le gas1
  have gas2 : 5 ≤ (secondRead headCode tailCode fits seed op a b caller).gasAvailable.toNat := by rw [charge2,charge1];omega
  have one := P10.dup_family_agreement 1 (firstSite headCode tailCode fits seed op) [a] caller b rfl
    (by simp only [List.length_cons,List.length_nil];omega) gas0 (fuel+2)
  have first :
      Assembly.driverSteps 1 (fuel+4) #[] (entry headCode tailCode fits seed op a b caller) = .ok (firstRead headCode tailCode fits seed op a b caller) ∧
      EVM.X (fuel+4) #[] (entry headCode tailCode fits seed op a b caller) = EVM.X (fuel+3) #[] (firstRead headCode tailCode fits seed op a b caller) := by
    simpa only [entry,firstRead,List.cons_append,List.nil_append] using one.2
  have input2 : (P10.modularSite (secondSite headCode tailCode fits seed op a b caller) (b::a::b::caller)).state =
      firstRead headCode tailCode fits seed op a b caller := by
    simp only [secondSite,P10.modularSite,P10.Site.state,firstRead,entry,firstSite,
      Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,
      Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Backend.Instr.encode,
      List.length_append,List.length_cons,List.length_nil,
      List.append_assoc,List.cons_append,List.nil_append,← pc_succ]
  have two := P10.dup_family_agreement 1 (secondSite headCode tailCode fits seed op a b caller) [b] (b::caller) a rfl
    (by simp only [List.length_cons,List.length_nil];omega) gas1 (fuel+1)
  have second :
      Assembly.driverSteps 1 (fuel+3) #[] (firstRead headCode tailCode fits seed op a b caller) = .ok (secondRead headCode tailCode fits seed op a b caller) ∧
      EVM.X (fuel+3) #[] (firstRead headCode tailCode fits seed op a b caller) = EVM.X (fuel+2) #[] (secondRead headCode tailCode fits seed op a b caller) := by
    simpa only [List.cons_append,List.nil_append,input2,secondRead] using two.2
  exact ⟨first.1,second.1,first.2.trans second.2,gas2⟩

/-- Whole actual three-instruction DIV X continuation to the source compiler's
value. The preceding read states/gas and final arithmetic run are DERIVED. -/
theorem div_continuation (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length ≤ 1020) (gas : 11 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) #[] (secondRead headCode tailCode fits seed .DIV a b caller) = .ok (divFinal headCode tailCode fits seed a b caller) ∧
    EVM.X (fuel+4) #[] (entry headCode tailCode fits seed .DIV a b caller) = EVM.X (fuel+1) #[] (divFinal headCode tailCode fits seed a b caller) := by
  have readProof := reads headCode tailCode fits seed .DIV a b caller room gas fuel
  have input3 : (P10.modularSite (arithmeticSite headCode tailCode fits (secondRead headCode tailCode fits seed .DIV a b caller) .DIV)
      (a::b::a::b::caller)).state = secondRead headCode tailCode fits seed .DIV a b caller := by
    simp only [arithmeticSite,P10.modularSite,P10.Site.state,firstRead,secondRead,entry,firstSite,
      Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,
      Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Backend.Instr.encode,
      ChargedQuotients.reads,List.length_append,List.length_cons,List.length_nil,
      List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,← pc_succ]
  have last := P10.div_agreement (arithmeticSite headCode tailCode fits (secondRead headCode tailCode fits seed .DIV a b caller) .DIV) a b (a::b::caller)
    (by simp only [List.length_cons];omega) readProof.2.2.2 fuel
  have final :
      Assembly.driverSteps 1 (fuel+2) #[] (secondRead headCode tailCode fits seed .DIV a b caller) = .ok (divFinal headCode tailCode fits seed a b caller) ∧
      EVM.X (fuel+2) #[] (secondRead headCode tailCode fits seed .DIV a b caller) = EVM.X (fuel+1) #[] (divFinal headCode tailCode fits seed a b caller) := by
    simpa only [input3,divFinal,finish] using last.2
  exact ⟨final.1,readProof.2.2.1.trans final.2⟩

/-- Corresponding whole MOD continuation, retaining every original local and
caller word, exact charged State and the SAME actual source compiler value. -/
theorem mod_continuation (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length ≤ 1020) (gas : 11 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) #[] (secondRead headCode tailCode fits seed .MOD a b caller) = .ok (modFinal headCode tailCode fits seed a b caller) ∧
    EVM.X (fuel+4) #[] (entry headCode tailCode fits seed .MOD a b caller) = EVM.X (fuel+1) #[] (modFinal headCode tailCode fits seed a b caller) := by
  have readProof := reads headCode tailCode fits seed .MOD a b caller room gas fuel
  have input3 : (P10.modularSite (arithmeticSite headCode tailCode fits (secondRead headCode tailCode fits seed .MOD a b caller) .MOD)
      (a::b::a::b::caller)).state = secondRead headCode tailCode fits seed .MOD a b caller := by
    simp only [arithmeticSite,P10.modularSite,P10.Site.state,firstRead,secondRead,entry,firstSite,
      Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,
      Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Backend.Instr.encode,
      ChargedQuotients.reads,List.length_append,List.length_cons,List.length_nil,
      List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,← pc_succ]
  have last := P10.mod_agreement (arithmeticSite headCode tailCode fits (secondRead headCode tailCode fits seed .MOD a b caller) .MOD) a b (a::b::caller)
    (by simp only [List.length_cons];omega) readProof.2.2.2 fuel
  have final :
      Assembly.driverSteps 1 (fuel+2) #[] (secondRead headCode tailCode fits seed .MOD a b caller) = .ok (modFinal headCode tailCode fits seed a b caller) ∧
      EVM.X (fuel+2) #[] (secondRead headCode tailCode fits seed .MOD a b caller) = EVM.X (fuel+1) #[] (modFinal headCode tailCode fits seed a b caller) := by
    simpa only [input3,modFinal,finish] using last.2
  exact ⟨final.1,readProof.2.2.1.trans final.2⟩

#print axioms reads
#print axioms div_continuation
#print axioms mod_continuation
end SolidityBridge.Yul.QuotientPlacement
