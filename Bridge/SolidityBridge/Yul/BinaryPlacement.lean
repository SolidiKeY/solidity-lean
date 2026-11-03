import SolidityBridge.Yul.QuotientPlacement
/-! Typed consumer of a real five-gas binary primitive proof. The source index
is the actual intrinsic expression and its compiler certificate, not an arbitrary
replacement evaluator. The interface itself proves no primitive; concrete bodies
must inhabit it. The emitted code image is an explicit obligation; full Source/G24/Osaka adequacy stays separate. -/
namespace SolidityBridge.Yul.BinaryPlacement
open Solidity Solidity.Yul Solidity.Yul.Closed Solidity.Yul.Compilation
open Backend Scalar Solidity.Evm.External EvmYul
open SolidityBridge.RoadmapV15 QuotientPlacement

structure Primitive {expr : Expr [] [] 2 1} (op : Backend.Op)
    (compiled : ProducerExpressions.Compiled 2 expr) where
  codeOrigin : compiled.lowered.code 0 = some (ChargedQuotients.reads ++ [.op op])
  run : ∀ (site : P10.Site op) (a b : Scalar.Word) (tail : Scalar.Stack)
    (room : tail.length+2 ≤ 1024) (gas : 5 ≤ site.seed.gasAvailable.toNat) (fuel : Nat),
    let input := (P10.modularSite site (a::b::tail)).state
    let next := (Assembly.chargedPrepare input 5).replaceStackAndIncrPC
      (((compiled.value #v[a,b])::tail).map (fun w => UInt256.mk w.toFin))
    Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
    EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next

def final {expr : Expr [] [] 2 1} {op : Backend.Op}
    {compiled : ProducerExpressions.Compiled 2 expr} (_primitive : Primitive op compiled)
    (headCode tailCode : Backend.Program)
    (fits : (Backend.encode headCode).length + 3 < UInt256.size)
    (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack) : EVM.State :=
  finish (secondRead headCode tailCode fits seed op a b caller)
    (compiled.value #v[a,b]) a b caller

/-- Conditional consumer law. Concrete producer instances below discharge its
real primitive/code-origin obligations; the interface alone is not coverage. -/
theorem continuation {expr : Expr [] [] 2 1} {op : Backend.Op}
    {compiled : ProducerExpressions.Compiled 2 expr} (primitive : Primitive op compiled)
    (headCode tailCode : Backend.Program)
    (fits : (Backend.encode headCode).length+3<UInt256.size)
    (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length≤1020) (gas : 11≤seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) #[] (secondRead headCode tailCode fits seed op a b caller) =
      .ok (final primitive headCode tailCode fits seed a b caller) ∧
    EVM.X (fuel+4) #[] (entry headCode tailCode fits seed op a b caller) =
      EVM.X (fuel+1) #[] (final primitive headCode tailCode fits seed a b caller) := by
  have readProof := reads headCode tailCode fits seed op a b caller room gas fuel
  have input3 : (P10.modularSite
      (arithmeticSite headCode tailCode fits (secondRead headCode tailCode fits seed op a b caller) op)
      (a::b::a::b::caller)).state = secondRead headCode tailCode fits seed op a b caller := by
    simp only [arithmeticSite,P10.modularSite,P10.Site.state,firstRead,secondRead,entry,firstSite,
      Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,
      Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Backend.Instr.encode,
      ChargedQuotients.reads,List.length_append,List.length_cons,List.length_nil,
      List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,← pc_succ]
  have last := primitive.run
    (arithmeticSite headCode tailCode fits (secondRead headCode tailCode fits seed op a b caller) op)
    a b (a::b::caller) (by simp only [List.length_cons];omega) readProof.2.2.2 fuel
  have actual :
      Assembly.driverSteps 1 (fuel+2) #[] (secondRead headCode tailCode fits seed op a b caller) =
        .ok (final primitive headCode tailCode fits seed a b caller) ∧
      EVM.X (fuel+2) #[] (secondRead headCode tailCode fits seed op a b caller) =
        EVM.X (fuel+1) #[] (final primitive headCode tailCode fits seed a b caller) := by
    simpa only [input3,final,finish] using last
  exact ⟨actual.1,readProof.2.2.1.trans actual.2⟩

#print axioms continuation
end SolidityBridge.Yul.BinaryPlacement
