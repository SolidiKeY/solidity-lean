import SolidityBridge.Yul.QuotientPlacement
import SolidityBridge.RoadmapV15.P10.BooleanNotConsumer
import Solidity.Yul.Compilation.UnaryMachine
/-! Concrete charged execution of the actual DUP1/ISZERO compiler sequence.
Raw words are not restricted to Boolean encodings. Source/G24, scanner and
whole-program Osaka/world/resource closure remain separate. -/
namespace SolidityBridge.Yul.ChargedIszero
open Solidity Solidity.Yul Solidity.Yul.Closed Solidity.Yul.Compilation
open Backend Scalar Solidity.Evm.External EvmYul
open SolidityBridge.RoadmapV15

variable (headCode tailCode : Backend.Program)
    (fits : (Backend.encode headCode).length+2<UInt256.size)

def firstSite (seed : EVM.State) : P10.Site (.DUP 0) where
  seed := seed
  before := headCode
  after := .op .ISZERO :: tailCode
  pcFits := by omega

def entry (seed : EVM.State) (a : Scalar.Word) (caller : Scalar.Stack) : EVM.State :=
  (P10.modularSite (firstSite headCode tailCode fits seed) (a::caller)).state

def copied (seed : EVM.State) (a : Scalar.Word) (caller : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (entry headCode tailCode fits seed a caller) 3).replaceStackAndIncrPC
    ((a::a::caller).map (fun w => UInt256.mk w.toFin))

def zeroSite (seed : EVM.State) (a : Scalar.Word) (caller : Scalar.Stack) : P10.Site .ISZERO where
  seed := copied headCode tailCode fits seed a caller
  before := headCode ++ [.op (.DUP 0)]
  after := tailCode
  pcFits := by
    simp only [Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Instr.encode,
      List.length_append,List.length_cons,List.length_nil]
    omega

def final (seed : EVM.State) (a : Scalar.Word) (caller : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (copied headCode tailCode fits seed a caller) 3).replaceStackAndIncrPC
    ((UnaryMachine.iszeroCompiled.value #v[a]::a::caller).map (fun w => UInt256.mk w.toFin))
/-- The second fetched site is the state actually reached by DUP1. -/
theorem zero_input (seed : EVM.State) (a : Scalar.Word) (caller : Scalar.Stack) :
    (P10.modularSite (zeroSite headCode tailCode fits seed a caller) (a::a::caller)).state =
      copied headCode tailCode fits seed a caller := by
  simp only [zeroSite,P10.modularSite,P10.Site.state,copied,entry,firstSite,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,
    Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Backend.Instr.encode,
    List.length_append,List.length_cons,List.length_nil,List.append_assoc,
    List.cons_append,List.nil_append,Nat.add_assoc,← QuotientPlacement.pc_succ]

/-- Both charged steps and the complete compiler-slice continuation are derived.
The arbitrary caller tail and raw original local remain in the exact final State.
The stack peak includes the additional DUP word; gas is charged twice. -/
theorem execution (seed : EVM.State) (a : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length ≤ 1022) (gas : 6 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+3) #[] (entry headCode tailCode fits seed a caller) =
      .ok (copied headCode tailCode fits seed a caller) ∧
    Assembly.driverSteps 1 (fuel+2) #[] (copied headCode tailCode fits seed a caller) =
      .ok (final headCode tailCode fits seed a caller) ∧
    EVM.X (fuel+3) #[] (entry headCode tailCode fits seed a caller) =
      EVM.X (fuel+1) #[] (final headCode tailCode fits seed a caller) := by
  have gas0 : 3 ≤ seed.gasAvailable.toNat := by omega
  have charge : (copied headCode tailCode fits seed a caller).gasAvailable.toNat =
      seed.gasAvailable.toNat-3 := Fin.sub_val_of_le gas0
  have gas1 : 3 ≤ (copied headCode tailCode fits seed a caller).gasAvailable.toNat := by
    rw [charge]; omega
  have one := P10.dup_family_agreement 0 (firstSite headCode tailCode fits seed) [] caller a rfl
    (by simp only [List.length_nil]; omega) gas0 (fuel+1)
  have first :
      Assembly.driverSteps 1 (fuel+3) #[] (entry headCode tailCode fits seed a caller) =
        .ok (copied headCode tailCode fits seed a caller) ∧
      EVM.X (fuel+3) #[] (entry headCode tailCode fits seed a caller) =
        EVM.X (fuel+2) #[] (copied headCode tailCode fits seed a caller) := by
    simpa only [entry,copied,List.nil_append] using one.2
  have two := P10.iszero_agreement #[] (zeroSite headCode tailCode fits seed a caller) a (a::caller)
    (by simp only [List.length_cons]; omega) gas1 fuel
  have second :
      Assembly.driverSteps 1 (fuel+2) #[] (copied headCode tailCode fits seed a caller) =
        .ok (final headCode tailCode fits seed a caller) ∧
      EVM.X (fuel+2) #[] (copied headCode tailCode fits seed a caller) =
        EVM.X (fuel+1) #[] (final headCode tailCode fits seed a caller) := by
    simpa only [zero_input,final] using two.2
  exact ⟨first.1,second.1,first.2.trans second.2⟩

end SolidityBridge.Yul.ChargedIszero
