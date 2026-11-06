import SolidityBridge.Yul.ChargedQuotients
import SolidityBridge.RoadmapV15.P10.StackFamilyConsumer
/-! Contextual quotient prefix over arbitrary actual Backend.Program suffixes.
The source expression and existing target State/driver are unchanged.
This is root-PC0/depth0 transport, not arbitrary relocation or Source/G24 adequacy. -/
namespace SolidityBridge.Yul.QuotientSuffix
open Solidity Solidity.Yul.Compilation Backend Scalar
open Solidity.Evm.External EvmYul
open SolidityBridge.RoadmapV15

variable (tailCode : Backend.Program)

def firstSite (seed : EVM.State) (op : Backend.Op) : P10.Site (.DUP 1) where
  seed := seed
  before := []
  after := .op (.DUP 1) :: .op op :: tailCode
  pcFits := by decide

def entry (seed : EVM.State) (op : Backend.Op) (a b : Scalar.Word) (caller : Scalar.Stack) : EVM.State :=
  (P10.modularSite (firstSite tailCode seed op) (a::b::caller)).state

def firstRead (seed : EVM.State) (op : Backend.Op) (a b : Scalar.Word) (caller : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (entry tailCode seed op a b caller) 3).replaceStackAndIncrPC
    ((b::a::b::caller).map (fun w => UInt256.mk w.toFin))

def secondSite (seed : EVM.State) (op : Backend.Op) (a b : Scalar.Word) (caller : Scalar.Stack) : P10.Site (.DUP 1) where
  seed := firstRead tailCode seed op a b caller
  before := [.op (.DUP 1)]
  after := .op op :: tailCode
  pcFits := by decide

def secondRead (seed : EVM.State) (op : Backend.Op) (a b : Scalar.Word) (caller : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (firstRead tailCode seed op a b caller) 3).replaceStackAndIncrPC
    ((a::b::a::b::caller).map (fun w => UInt256.mk w.toFin))

def finish (input : EVM.State) (value a b : Scalar.Word) (caller : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare input 5).replaceStackAndIncrPC
    ((value::a::b::caller).map (fun w => UInt256.mk w.toFin))

def arithmeticSite (seed : EVM.State) (op : Backend.Op) : P10.Site op where
  seed := seed
  before := ChargedQuotients.reads
  after := tailCode
  pcFits := by decide

def divFinal (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack) : EVM.State :=
  finish (secondRead tailCode seed .DIV a b caller) (ChargedQuotients.divCompiled.value #v[a,b]) a b caller
def modFinal (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack) : EVM.State :=
  finish (secondRead tailCode seed .MOD a b caller) (ChargedQuotients.modCompiled.value #v[a,b]) a b caller

/-- Two actual charged reads, with their exact intermediate State and X path.
Initial gas11 and peak capacity derive the later gas5/capacity obligations.
No desired step, intermediate gate or continuation is an input premise. -/
theorem reads (seed : EVM.State) (op : Backend.Op) (a b : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length ≤ 1020) (gas : 11 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+4) #[] (entry tailCode seed op a b caller) = .ok (firstRead tailCode seed op a b caller) ∧
    Assembly.driverSteps 1 (fuel+3) #[] (firstRead tailCode seed op a b caller) = .ok (secondRead tailCode seed op a b caller) ∧
    EVM.X (fuel+4) #[] (entry tailCode seed op a b caller) = EVM.X (fuel+2) #[] (secondRead tailCode seed op a b caller) ∧
    5 ≤ (secondRead tailCode seed op a b caller).gasAvailable.toNat := by
  have gas0 : 3 ≤ seed.gasAvailable.toNat := by omega
  have charge1 : (firstRead tailCode seed op a b caller).gasAvailable.toNat = seed.gasAvailable.toNat-3 :=
    Fin.sub_val_of_le gas0
  have gas1 : 3 ≤ (firstRead tailCode seed op a b caller).gasAvailable.toNat := by rw [charge1];omega
  have charge2 : (secondRead tailCode seed op a b caller).gasAvailable.toNat =
      (firstRead tailCode seed op a b caller).gasAvailable.toNat-3 := Fin.sub_val_of_le gas1
  have gas2 : 5 ≤ (secondRead tailCode seed op a b caller).gasAvailable.toNat := by rw [charge2,charge1];omega
  have one := P10.dup_family_agreement 1 (firstSite tailCode seed op) [a] caller b rfl
    (by simp only [List.length_cons,List.length_nil];omega) gas0 (fuel+2)
  have first :
      Assembly.driverSteps 1 (fuel+4) #[] (entry tailCode seed op a b caller) = .ok (firstRead tailCode seed op a b caller) ∧
      EVM.X (fuel+4) #[] (entry tailCode seed op a b caller) = EVM.X (fuel+3) #[] (firstRead tailCode seed op a b caller) := by
    simpa only [entry,firstRead,List.cons_append,List.nil_append] using one.2
  have input2 : (P10.modularSite (secondSite tailCode seed op a b caller) (b::a::b::caller)).state =
      firstRead tailCode seed op a b caller := by rfl
  have two := P10.dup_family_agreement 1 (secondSite tailCode seed op a b caller) [b] (b::caller) a rfl
    (by simp only [List.length_cons,List.length_nil];omega) gas1 (fuel+1)
  have second :
      Assembly.driverSteps 1 (fuel+3) #[] (firstRead tailCode seed op a b caller) = .ok (secondRead tailCode seed op a b caller) ∧
      EVM.X (fuel+3) #[] (firstRead tailCode seed op a b caller) = EVM.X (fuel+2) #[] (secondRead tailCode seed op a b caller) := by
    simpa only [List.cons_append,List.nil_append,input2,secondRead] using two.2
  exact ⟨first.1,second.1,first.2.trans second.2,gas2⟩

/-- Whole actual three-instruction DIV X continuation to the source compiler's
value. The preceding read states/gas and final arithmetic run are DERIVED. -/
theorem div_continuation (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length ≤ 1020) (gas : 11 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) #[] (secondRead tailCode seed .DIV a b caller) = .ok (divFinal tailCode seed a b caller) ∧
    EVM.X (fuel+4) #[] (entry tailCode seed .DIV a b caller) = EVM.X (fuel+1) #[] (divFinal tailCode seed a b caller) := by
  have readProof := reads tailCode seed .DIV a b caller room gas fuel
  have input3 : (P10.modularSite (arithmeticSite tailCode (secondRead tailCode seed .DIV a b caller) .DIV)
      (a::b::a::b::caller)).state = secondRead tailCode seed .DIV a b caller := by rfl
  have last := P10.div_agreement (arithmeticSite tailCode (secondRead tailCode seed .DIV a b caller) .DIV) a b (a::b::caller)
    (by simp only [List.length_cons];omega) readProof.2.2.2 fuel
  have final :
      Assembly.driverSteps 1 (fuel+2) #[] (secondRead tailCode seed .DIV a b caller) = .ok (divFinal tailCode seed a b caller) ∧
      EVM.X (fuel+2) #[] (secondRead tailCode seed .DIV a b caller) = EVM.X (fuel+1) #[] (divFinal tailCode seed a b caller) := by
    simpa only [input3,divFinal,finish] using last.2
  exact ⟨final.1,readProof.2.2.1.trans final.2⟩

/-- Corresponding whole MOD continuation, retaining every original local and
caller word, exact charged State and the SAME actual source compiler value. -/
theorem mod_continuation (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length ≤ 1020) (gas : 11 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) #[] (secondRead tailCode seed .MOD a b caller) = .ok (modFinal tailCode seed a b caller) ∧
    EVM.X (fuel+4) #[] (entry tailCode seed .MOD a b caller) = EVM.X (fuel+1) #[] (modFinal tailCode seed a b caller) := by
  have readProof := reads tailCode seed .MOD a b caller room gas fuel
  have input3 : (P10.modularSite (arithmeticSite tailCode (secondRead tailCode seed .MOD a b caller) .MOD)
      (a::b::a::b::caller)).state = secondRead tailCode seed .MOD a b caller := by rfl
  have last := P10.mod_agreement (arithmeticSite tailCode (secondRead tailCode seed .MOD a b caller) .MOD) a b (a::b::caller)
    (by simp only [List.length_cons];omega) readProof.2.2.2 fuel
  have final :
      Assembly.driverSteps 1 (fuel+2) #[] (secondRead tailCode seed .MOD a b caller) = .ok (modFinal tailCode seed a b caller) ∧
      EVM.X (fuel+2) #[] (secondRead tailCode seed .MOD a b caller) = EVM.X (fuel+1) #[] (modFinal tailCode seed a b caller) := by
    simpa only [input3,modFinal,finish] using last.2
  exact ⟨final.1,readProof.2.2.1.trans final.2⟩

#print axioms reads
#print axioms div_continuation
#print axioms mod_continuation
end SolidityBridge.Yul.QuotientSuffix
