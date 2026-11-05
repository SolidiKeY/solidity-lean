import SolidityBridge.Yul.QuotientPlacement
import SolidityBridge.RoadmapV15.P10.Modular
import Solidity.Yul.Compilation.PureExpressions
/-! Actual arity-three source compiler and charged DUP3/DUP3/DUP3 prefix.
No source/state/calling convention is added. Full Source/G24/view/scanner and
whole-program Osaka/world/resource/trace composition remain separate. -/
namespace SolidityBridge.Yul.ChargedModular
open Solidity Solidity.Yul Solidity.Yul.Closed Solidity.Yul.Compilation
open Backend Scalar Solidity.Evm.External EvmYul
open SolidityBridge.RoadmapV15

def addExpr : Expr [] [] 3 1 :=
  .builtin (.pure .addmod) (Fin.cases (.local 0) (Fin.cases (.local 1) (fun _ => .local 2)))
def mulExpr : Expr [] [] 3 1 :=
  .builtin (.pure .mulmod) (Fin.cases (.local 0) (Fin.cases (.local 1) (fun _ => .local 2)))
def addCompiled := (PureExpressions.compile 2 addExpr).get (by rfl)
def mulCompiled := (PureExpressions.compile 2 mulExpr).get (by rfl)
def reads : Backend.Program := [.op (.DUP 2),.op (.DUP 2),.op (.DUP 2)]

variable (headCode tailCode : Backend.Program)
    (fits : (Backend.encode headCode).length+4<UInt256.size)

def firstSite (seed : EVM.State) (op : Backend.Op) : P10.Site (.DUP 2) where
  seed := seed
  before := headCode
  after := [.op (.DUP 2),.op (.DUP 2),.op op] ++ tailCode
  pcFits := by omega

def entry (seed : EVM.State) (op : Backend.Op) (a b k : Scalar.Word) (caller : Scalar.Stack) :=
  (P10.modularSite (firstSite headCode tailCode fits seed op) (a::b::k::caller)).state

def firstRead (seed : EVM.State) (op : Backend.Op) (a b k : Scalar.Word) (caller : Scalar.Stack) :=
  (Assembly.chargedPrepare (entry headCode tailCode fits seed op a b k caller) 3).replaceStackAndIncrPC
    ((k::a::b::k::caller).map (fun w => UInt256.mk w.toFin))

def secondSite (seed : EVM.State) (op : Backend.Op) (a b k : Scalar.Word) (caller : Scalar.Stack) : P10.Site (.DUP 2) where
  seed := firstRead headCode tailCode fits seed op a b k caller
  before := headCode ++ [.op (.DUP 2)]
  after := [.op (.DUP 2),.op op] ++ tailCode
  pcFits := by
    simp only [Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Instr.encode,List.length_append,List.length_cons,List.length_nil]
    omega

def secondRead (seed : EVM.State) (op : Backend.Op) (a b k : Scalar.Word) (caller : Scalar.Stack) :=
  (Assembly.chargedPrepare (firstRead headCode tailCode fits seed op a b k caller) 3).replaceStackAndIncrPC
    ((b::k::a::b::k::caller).map (fun w => UInt256.mk w.toFin))

def thirdSite (seed : EVM.State) (op : Backend.Op) (a b k : Scalar.Word) (caller : Scalar.Stack) : P10.Site (.DUP 2) where
  seed := secondRead headCode tailCode fits seed op a b k caller
  before := headCode ++ [.op (.DUP 2),.op (.DUP 2)]
  after := .op op :: tailCode
  pcFits := by
    simp only [Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Instr.encode,List.length_append,List.length_cons,List.length_nil]
    omega

def thirdRead (seed : EVM.State) (op : Backend.Op) (a b k : Scalar.Word) (caller : Scalar.Stack) :=
  (Assembly.chargedPrepare (secondRead headCode tailCode fits seed op a b k caller) 3).replaceStackAndIncrPC
    ((a::b::k::a::b::k::caller).map (fun w => UInt256.mk w.toFin))

def arithmeticSite (seed : EVM.State) (op : Backend.Op) : P10.Site op where
  seed := seed
  before := headCode ++ reads
  after := tailCode
  pcFits := by
    simp only [reads,Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Instr.encode,List.length_append,List.length_cons,List.length_nil]
    omega

def final (seed : EVM.State) (op : Backend.Op) (result a b k : Scalar.Word) (caller : Scalar.Stack) :=
  (Assembly.chargedPrepare (thirdRead headCode tailCode fits seed op a b k caller) 8).replaceStackAndIncrPC
    ((result::a::b::k::caller).map (fun w => UInt256.mk w.toFin))

theorem read_prefix (seed : EVM.State) (op : Backend.Op) (a b k : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length≤1018) (gas : 17≤seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+5) #[] (entry headCode tailCode fits seed op a b k caller) =
      .ok (firstRead headCode tailCode fits seed op a b k caller) ∧
    Assembly.driverSteps 1 (fuel+4) #[] (firstRead headCode tailCode fits seed op a b k caller) =
      .ok (secondRead headCode tailCode fits seed op a b k caller) ∧
    Assembly.driverSteps 1 (fuel+3) #[] (secondRead headCode tailCode fits seed op a b k caller) =
      .ok (thirdRead headCode tailCode fits seed op a b k caller) ∧
    EVM.X (fuel+5) #[] (entry headCode tailCode fits seed op a b k caller) =
      EVM.X (fuel+2) #[] (thirdRead headCode tailCode fits seed op a b k caller) ∧
    8≤(thirdRead headCode tailCode fits seed op a b k caller).gasAvailable.toNat := by
  have gas0 : 3≤seed.gasAvailable.toNat := by omega
  have charge1 : (firstRead headCode tailCode fits seed op a b k caller).gasAvailable.toNat = seed.gasAvailable.toNat-3 := Fin.sub_val_of_le gas0
  have gas1 : 3≤(firstRead headCode tailCode fits seed op a b k caller).gasAvailable.toNat := by rw [charge1]; omega
  have charge2 : (secondRead headCode tailCode fits seed op a b k caller).gasAvailable.toNat = (firstRead headCode tailCode fits seed op a b k caller).gasAvailable.toNat-3 := Fin.sub_val_of_le gas1
  have gas2 : 3≤(secondRead headCode tailCode fits seed op a b k caller).gasAvailable.toNat := by rw [charge2,charge1]; omega
  have charge3 : (thirdRead headCode tailCode fits seed op a b k caller).gasAvailable.toNat = (secondRead headCode tailCode fits seed op a b k caller).gasAvailable.toNat-3 := Fin.sub_val_of_le gas2
  have reserve : 8≤(thirdRead headCode tailCode fits seed op a b k caller).gasAvailable.toNat := by rw [charge3,charge2,charge1]; omega
  have one := P10.dup_family_agreement 2 (firstSite headCode tailCode fits seed op) [a,b] caller k rfl
    (by simp only [List.length_cons,List.length_nil]; omega) gas0 (fuel+3)
  have first :
      Assembly.driverSteps 1 (fuel+5) #[] (entry headCode tailCode fits seed op a b k caller) = .ok (firstRead headCode tailCode fits seed op a b k caller) ∧
      EVM.X (fuel+5) #[] (entry headCode tailCode fits seed op a b k caller) = EVM.X (fuel+4) #[] (firstRead headCode tailCode fits seed op a b k caller) := by
    simpa only [entry,firstRead,List.cons_append,List.nil_append] using one.2
  have input2 : (P10.modularSite (secondSite headCode tailCode fits seed op a b k caller)
      (k::a::b::k::caller)).state = firstRead headCode tailCode fits seed op a b k caller := by
    simp only [secondSite,P10.modularSite,P10.Site.state,firstRead,entry,firstSite,
      Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,
      Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Backend.Instr.encode,
      List.length_append,List.length_cons,List.length_nil,List.append_assoc,List.cons_append,List.nil_append,← QuotientPlacement.pc_succ]
  have step2 := P10.dup_family_agreement 2 (secondSite headCode tailCode fits seed op a b k caller) [k,a] (k::caller) b rfl
    (by simp only [List.length_cons,List.length_nil]; omega) gas1 (fuel+2)
  have actual2 :
      Assembly.driverSteps 1 (fuel+4) #[] (firstRead headCode tailCode fits seed op a b k caller) = .ok (secondRead headCode tailCode fits seed op a b k caller) ∧
      EVM.X (fuel+4) #[] (firstRead headCode tailCode fits seed op a b k caller) = EVM.X (fuel+3) #[] (secondRead headCode tailCode fits seed op a b k caller) := by
    simpa only [List.cons_append,List.nil_append,input2,secondRead] using step2.2
  have input3 : (P10.modularSite (thirdSite headCode tailCode fits seed op a b k caller)
      (b::k::a::b::k::caller)).state = secondRead headCode tailCode fits seed op a b k caller := by
    simp only [thirdSite,P10.modularSite,P10.Site.state,firstRead,secondRead,entry,firstSite,
      Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,
      Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Backend.Instr.encode,
      List.length_append,List.length_cons,List.length_nil,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,← QuotientPlacement.pc_succ]
  have step3 := P10.dup_family_agreement 2 (thirdSite headCode tailCode fits seed op a b k caller) [b,k] (b::k::caller) a rfl
    (by simp only [List.length_cons,List.length_nil]; omega) gas2 (fuel+1)
  have actual3 :
      Assembly.driverSteps 1 (fuel+3) #[] (secondRead headCode tailCode fits seed op a b k caller) = .ok (thirdRead headCode tailCode fits seed op a b k caller) ∧
      EVM.X (fuel+3) #[] (secondRead headCode tailCode fits seed op a b k caller) = EVM.X (fuel+2) #[] (thirdRead headCode tailCode fits seed op a b k caller) := by
    simpa only [List.cons_append,List.nil_append,input3,thirdRead] using step3.2
  exact ⟨first.1,actual2.1,actual3.1,first.2.trans (actual2.2.trans actual3.2),reserve⟩
theorem add_continuation (seed : EVM.State) (a b k : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length≤1018) (gas : 17≤seed.gasAvailable.toNat) (fuel : Nat) :
    evalExpr 2 .nil True.intro addExpr addCompiled.profile (ProducerExpressions.sourceLocals #v[a,b,k]) =
      some (fun _ => (addCompiled.value #v[a,b,k]).toFin) ∧
    Assembly.driverSteps 1 (fuel+2) #[] (thirdRead headCode tailCode fits seed .ADDMOD a b k caller) =
      .ok (final headCode tailCode fits seed .ADDMOD (addCompiled.value #v[a,b,k]) a b k caller) ∧
    EVM.X (fuel+5) #[] (entry headCode tailCode fits seed .ADDMOD a b k caller) =
      EVM.X (fuel+1) #[] (final headCode tailCode fits seed .ADDMOD (addCompiled.value #v[a,b,k]) a b k caller) := by
  have start := read_prefix headCode tailCode fits seed .ADDMOD a b k caller room gas fuel
  have input4 : (P10.modularSite (arithmeticSite headCode tailCode fits
      (thirdRead headCode tailCode fits seed .ADDMOD a b k caller) .ADDMOD)
      (a::b::k::a::b::k::caller)).state = thirdRead headCode tailCode fits seed .ADDMOD a b k caller := by
    simp only [arithmeticSite,P10.modularSite,P10.Site.state,thirdRead,secondRead,firstRead,entry,firstSite,reads,
      Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,
      Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Backend.Instr.encode,
      List.length_append,List.length_cons,List.length_nil,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,← QuotientPlacement.pc_succ]
  have last := P10.addmod_agreement (arithmeticSite headCode tailCode fits
      (thirdRead headCode tailCode fits seed .ADDMOD a b k caller) .ADDMOD) a b k (a::b::k::caller)
    (by simp only [List.length_cons]; omega) start.2.2.2.2 fuel
  have actual :
      Assembly.driverSteps 1 (fuel+2) #[] (thirdRead headCode tailCode fits seed .ADDMOD a b k caller) =
        .ok (final headCode tailCode fits seed .ADDMOD (addCompiled.value #v[a,b,k]) a b k caller) ∧
      EVM.X (fuel+2) #[] (thirdRead headCode tailCode fits seed .ADDMOD a b k caller) =
        EVM.X (fuel+1) #[] (final headCode tailCode fits seed .ADDMOD (addCompiled.value #v[a,b,k]) a b k caller) := by
    simpa only [input4,final] using last.2
  exact ⟨addCompiled.source #v[a,b,k],actual.1,start.2.2.2.1.trans actual.2⟩

theorem mul_continuation (seed : EVM.State) (a b k : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length≤1018) (gas : 17≤seed.gasAvailable.toNat) (fuel : Nat) :
    evalExpr 2 .nil True.intro mulExpr mulCompiled.profile (ProducerExpressions.sourceLocals #v[a,b,k]) =
      some (fun _ => (mulCompiled.value #v[a,b,k]).toFin) ∧
    Assembly.driverSteps 1 (fuel+2) #[] (thirdRead headCode tailCode fits seed .MULMOD a b k caller) =
      .ok (final headCode tailCode fits seed .MULMOD (mulCompiled.value #v[a,b,k]) a b k caller) ∧
    EVM.X (fuel+5) #[] (entry headCode tailCode fits seed .MULMOD a b k caller) =
      EVM.X (fuel+1) #[] (final headCode tailCode fits seed .MULMOD (mulCompiled.value #v[a,b,k]) a b k caller) := by
  have start := read_prefix headCode tailCode fits seed .MULMOD a b k caller room gas fuel
  have input4 : (P10.modularSite (arithmeticSite headCode tailCode fits
      (thirdRead headCode tailCode fits seed .MULMOD a b k caller) .MULMOD)
      (a::b::k::a::b::k::caller)).state = thirdRead headCode tailCode fits seed .MULMOD a b k caller := by
    simp only [arithmeticSite,P10.modularSite,P10.Site.state,thirdRead,secondRead,firstRead,entry,firstSite,reads,
      Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,
      Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Backend.Instr.encode,
      List.length_append,List.length_cons,List.length_nil,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,← QuotientPlacement.pc_succ]
  have last := P10.mulmod_agreement (arithmeticSite headCode tailCode fits
      (thirdRead headCode tailCode fits seed .MULMOD a b k caller) .MULMOD) a b k (a::b::k::caller)
    (by simp only [List.length_cons]; omega) start.2.2.2.2 fuel
  have actual :
      Assembly.driverSteps 1 (fuel+2) #[] (thirdRead headCode tailCode fits seed .MULMOD a b k caller) =
        .ok (final headCode tailCode fits seed .MULMOD (mulCompiled.value #v[a,b,k]) a b k caller) ∧
      EVM.X (fuel+2) #[] (thirdRead headCode tailCode fits seed .MULMOD a b k caller) =
        EVM.X (fuel+1) #[] (final headCode tailCode fits seed .MULMOD (mulCompiled.value #v[a,b,k]) a b k caller) := by
    simpa only [input4,final] using last.2
  exact ⟨mulCompiled.source #v[a,b,k],actual.1,start.2.2.2.1.trans actual.2⟩
end SolidityBridge.Yul.ChargedModular
