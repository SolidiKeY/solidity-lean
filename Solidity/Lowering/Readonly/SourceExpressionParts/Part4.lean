import Solidity.Lowering.Readonly.SourceBuiltinEffects
import Solidity.Lowering.Readonly.TupleCopyEffects

/-! Generated typed cuts of the actual Source expression history step.
No execution semantics or type/admission premise is replaced. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source

theorem evalE_indexArray_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} {l : DataLoc} {τ σ : STy} {n : Option Nat} (a : RExpr E Γ (.array l τ n)) (i : RExpr E Γ σ) (h : σ.isIndex = true) :
    Effect F.static (evalE G F (fuel+1) (RExpr.indexArray (E := E) (Γ := Γ) a i h)) := by
  simp only [Solidity.Source.evalE]
  repeat' first
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.locals F.static)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.st F.static)
     | (with_reducible exact _history.evalE F _)
     | (with_reducible exact _history.evalPair F _ _)
     | (with_reducible exact _history.evalArgs F _)
     | (with_reducible exact _history.evalConvArgs F _)
     | (with_reducible exact _history.evalLoc F _)
     | (with_reducible exact _history.evalBuiltin F _ _ _)
     | (with_reducible exact _history.callInternal F _ _ _)
     | (with_reducible exact _history.pay F _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.parent F.static _ _ (_history.callAddr F _ _ _ _))
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.getV_effect F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.indexNat_effect F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.readAt_effect F.static F _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.storRef_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.readLoc_effect F.static F _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.writeLoc_effect F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.deleteLoc_effect F fuel _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.indexLoc_effect F.static F _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.keyStep_effect F.static F fuel _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.bytesOfRV_effect F.static F fuel _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.convRV_effect F.static F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.convExplicitRV_effect F.static F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.instanceAt_effect F.static G _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.fieldsOf_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.allocRef_effect F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.encodeVals_effect F.static F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.extReturn_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.copyInto_effect F fuel _ _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.abiDecodeData_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.lengthOf_effect F.static F _)
     | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
     | refine Solidity.Lowering.Readonly.SourceHistory.Effect.sub F.static _ _ ?_
     | split
     | dsimp only

theorem evalE_indexMapping_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} {τk τv : STy} (a : RExpr E Γ (.mapping τk τv)) (k : RExpr E Γ τk) :
    Effect F.static (evalE G F (fuel+1) (RExpr.indexMapping (E := E) (Γ := Γ) a k)) := by
  simp only [Solidity.Source.evalE]
  repeat' first
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.locals F.static)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.st F.static)
     | (with_reducible exact _history.evalE F _)
     | (with_reducible exact _history.evalPair F _ _)
     | (with_reducible exact _history.evalArgs F _)
     | (with_reducible exact _history.evalConvArgs F _)
     | (with_reducible exact _history.evalLoc F _)
     | (with_reducible exact _history.evalBuiltin F _ _ _)
     | (with_reducible exact _history.callInternal F _ _ _)
     | (with_reducible exact _history.pay F _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.parent F.static _ _ (_history.callAddr F _ _ _ _))
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.getV_effect F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.indexNat_effect F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.readAt_effect F.static F _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.storRef_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.readLoc_effect F.static F _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.writeLoc_effect F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.deleteLoc_effect F fuel _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.indexLoc_effect F.static F _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.keyStep_effect F.static F fuel _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.bytesOfRV_effect F.static F fuel _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.convRV_effect F.static F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.convExplicitRV_effect F.static F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.instanceAt_effect F.static G _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.fieldsOf_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.allocRef_effect F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.encodeVals_effect F.static F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.extReturn_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.copyInto_effect F fuel _ _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.abiDecodeData_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.lengthOf_effect F.static F _)
     | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
     | refine Solidity.Lowering.Readonly.SourceHistory.Effect.sub F.static _ _ ?_
     | split
     | dsimp only

theorem evalE_indexBytes_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} {τ σ : STy} (a : RExpr E Γ τ) (i : RExpr E Γ σ) (h : σ.isIndex = true) :
    Effect F.static (evalE G F (fuel+1) (RExpr.indexBytes (E := E) (Γ := Γ) a i h)) := by
  simp only [Solidity.Source.evalE]
  repeat' first
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.locals F.static)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.st F.static)
     | (with_reducible exact _history.evalE F _)
     | (with_reducible exact _history.evalPair F _ _)
     | (with_reducible exact _history.evalArgs F _)
     | (with_reducible exact _history.evalConvArgs F _)
     | (with_reducible exact _history.evalLoc F _)
     | (with_reducible exact _history.evalBuiltin F _ _ _)
     | (with_reducible exact _history.callInternal F _ _ _)
     | (with_reducible exact _history.pay F _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.parent F.static _ _ (_history.callAddr F _ _ _ _))
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.getV_effect F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.indexNat_effect F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.readAt_effect F.static F _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.storRef_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.readLoc_effect F.static F _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.writeLoc_effect F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.deleteLoc_effect F fuel _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.indexLoc_effect F.static F _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.keyStep_effect F.static F fuel _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.bytesOfRV_effect F.static F fuel _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.convRV_effect F.static F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.convExplicitRV_effect F.static F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.instanceAt_effect F.static G _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.fieldsOf_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.allocRef_effect F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.encodeVals_effect F.static F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.extReturn_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.copyInto_effect F fuel _ _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.abiDecodeData_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.lengthOf_effect F.static F _)
     | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
     | refine Solidity.Lowering.Readonly.SourceHistory.Effect.sub F.static _ _ ?_
     | split
     | dsimp only

theorem evalE_length_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} {τ ρ : STy} (a : RExpr E Γ τ) (h : τ.lengthTy = some ρ) :
    Effect F.static (evalE G F (fuel+1) (RExpr.length (E := E) (Γ := Γ) a h)) := by
  simp only [Solidity.Source.evalE]
  repeat' first
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.locals F.static)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.st F.static)
     | (with_reducible exact _history.evalE F _)
     | (with_reducible exact _history.evalPair F _ _)
     | (with_reducible exact _history.evalArgs F _)
     | (with_reducible exact _history.evalConvArgs F _)
     | (with_reducible exact _history.evalLoc F _)
     | (with_reducible exact _history.evalBuiltin F _ _ _)
     | (with_reducible exact _history.callInternal F _ _ _)
     | (with_reducible exact _history.pay F _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.parent F.static _ _ (_history.callAddr F _ _ _ _))
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.getV_effect F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.indexNat_effect F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.readAt_effect F.static F _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.storRef_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.readLoc_effect F.static F _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.writeLoc_effect F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.deleteLoc_effect F fuel _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.indexLoc_effect F.static F _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.keyStep_effect F.static F fuel _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.bytesOfRV_effect F.static F fuel _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.convRV_effect F.static F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.convExplicitRV_effect F.static F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.instanceAt_effect F.static G _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.fieldsOf_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.allocRef_effect F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.encodeVals_effect F.static F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.extReturn_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.copyInto_effect F fuel _ _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.abiDecodeData_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.lengthOf_effect F.static F _)
     | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
     | refine Solidity.Lowering.Readonly.SourceHistory.Effect.sub F.static _ _ ?_
     | split
     | dsimp only

theorem evalE_payable_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} {σ : STy} (e : RExpr E Γ σ) :
    Effect F.static (evalE G F (fuel+1) (RExpr.payable (E := E) (Γ := Γ) e)) := by
  simp only [Solidity.Source.evalE]
  repeat' first
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.locals F.static)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.st F.static)
     | (with_reducible exact _history.evalE F _)
     | (with_reducible exact _history.evalPair F _ _)
     | (with_reducible exact _history.evalArgs F _)
     | (with_reducible exact _history.evalConvArgs F _)
     | (with_reducible exact _history.evalLoc F _)
     | (with_reducible exact _history.evalBuiltin F _ _ _)
     | (with_reducible exact _history.callInternal F _ _ _)
     | (with_reducible exact _history.pay F _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.parent F.static _ _ (_history.callAddr F _ _ _ _))
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.getV_effect F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.indexNat_effect F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.readAt_effect F.static F _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.storRef_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.readLoc_effect F.static F _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.writeLoc_effect F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.deleteLoc_effect F fuel _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.indexLoc_effect F.static F _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.keyStep_effect F.static F fuel _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.bytesOfRV_effect F.static F fuel _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.convRV_effect F.static F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.convExplicitRV_effect F.static F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.instanceAt_effect F.static G _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.fieldsOf_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.allocRef_effect F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.encodeVals_effect F.static F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.extReturn_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.copyInto_effect F fuel _ _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.abiDecodeData_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.lengthOf_effect F.static F _)
     | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
     | refine Solidity.Lowering.Readonly.SourceHistory.Effect.sub F.static _ _ ?_
     | split
     | dsimp only

theorem evalE_call_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} {ps rs : List STy} (d : Decl) (h : d.fnSig E = some (ps, rs)) (args : RConvArgs E Γ ps) :
    Effect F.static (evalE G F (fuel+1) (RExpr.call (E := E) (Γ := Γ) d h args)) := by
  simp only [Solidity.Source.evalE]
  repeat' first
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.locals F.static)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.st F.static)
     | (with_reducible exact _history.evalE F _)
     | (with_reducible exact _history.evalPair F _ _)
     | (with_reducible exact _history.evalArgs F _)
     | (with_reducible exact _history.evalConvArgs F _)
     | (with_reducible exact _history.evalLoc F _)
     | (with_reducible exact _history.evalBuiltin F _ _ _)
     | (with_reducible exact _history.callInternal F _ _ _)
     | (with_reducible exact _history.pay F _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.parent F.static _ _ (_history.callAddr F _ _ _ _))
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.getV_effect F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.indexNat_effect F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.readAt_effect F.static F _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.storRef_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.readLoc_effect F.static F _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.writeLoc_effect F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.deleteLoc_effect F fuel _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.indexLoc_effect F.static F _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.keyStep_effect F.static F fuel _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.bytesOfRV_effect F.static F fuel _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.convRV_effect F.static F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.convExplicitRV_effect F.static F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.instanceAt_effect F.static G _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.fieldsOf_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.allocRef_effect F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.encodeVals_effect F.static F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.extReturn_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.copyInto_effect F fuel _ _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.abiDecodeData_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.lengthOf_effect F.static F _)
     | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
     | refine Solidity.Lowering.Readonly.SourceHistory.Effect.sub F.static _ _ ?_
     | split
     | dsimp only

theorem evalE_magic_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} {τ : STy} (b : Builtin) (m : String) (h : b.memberTy m = some τ) :
    Effect F.static (evalE G F (fuel+1) (RExpr.magic (E := E) (Γ := Γ) b m h)) := by
  simp only [Solidity.Source.evalE]
  repeat' first
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.locals F.static)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.st F.static)
     | (with_reducible exact _history.evalE F _)
     | (with_reducible exact _history.evalPair F _ _)
     | (with_reducible exact _history.evalArgs F _)
     | (with_reducible exact _history.evalConvArgs F _)
     | (with_reducible exact _history.evalLoc F _)
     | (with_reducible exact _history.evalBuiltin F _ _ _)
     | (with_reducible exact _history.callInternal F _ _ _)
     | (with_reducible exact _history.pay F _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.parent F.static _ _ (_history.callAddr F _ _ _ _))
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.getV_effect F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.indexNat_effect F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.readAt_effect F.static F _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.storRef_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.readLoc_effect F.static F _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.writeLoc_effect F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.deleteLoc_effect F fuel _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.indexLoc_effect F.static F _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.keyStep_effect F.static F fuel _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.bytesOfRV_effect F.static F fuel _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.convRV_effect F.static F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.convExplicitRV_effect F.static F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.instanceAt_effect F.static G _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.fieldsOf_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.allocRef_effect F.static _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.encodeVals_effect F.static F fuel _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.extReturn_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.copyInto_effect F fuel _ _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.abiDecodeData_effect F.static _ _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.lengthOf_effect F.static F _)
     | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
     | refine Solidity.Lowering.Readonly.SourceHistory.Effect.sub F.static _ _ ?_
     | split
     | dsimp only

end Solidity.Lowering.Readonly.SourceHistory
