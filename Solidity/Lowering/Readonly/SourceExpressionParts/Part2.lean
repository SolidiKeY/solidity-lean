import Solidity.Lowering.Readonly.SourceBuiltinEffects
import Solidity.Lowering.Readonly.TupleCopyEffects

/-! Generated typed cuts of the actual Source expression history step.
No execution semantics or type/admission premise is replaced. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source

theorem evalE_this_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} (c : String) :
    Effect F.static (evalE G F (fuel+1) (RExpr.this (E := E) (Γ := Γ) c)) := by
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

theorem evalE_tuple_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Effect F.static (evalE G F (fuel+1) (RExpr.tuple (E := E) (Γ := Γ) es)) := by
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

theorem evalE_conv_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} {σ τ : STy} (e : RExpr E Γ σ) (h : Conv E.isBase E.mapFree σ τ) :
    Effect F.static (evalE G F (fuel+1) (RExpr.conv (E := E) (Γ := Γ) e h)) := by
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

theorem evalE_convExplicit_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} {σ τ : STy} (e : RExpr E Γ σ) (h : σ.explicit E.isBase E.mapFree τ = true) :
    Effect F.static (evalE G F (fuel+1) (RExpr.convExplicit (E := E) (Γ := Γ) e h)) := by
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

theorem evalE_unary_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} {τ : STy} (op : PrefixOp) (e : RExpr E Γ τ) :
    Effect F.static (evalE G F (fuel+1) (RExpr.unary (E := E) (Γ := Γ) op e)) := by
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

theorem evalE_incDec_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} {τ : STy} (inc pre : Bool) (l : RLVal E Γ τ) :
    Effect F.static (evalE G F (fuel+1) (RExpr.incDec (E := E) (Γ := Γ) inc pre l)) := by
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

theorem evalE_delete_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} {τ : STy} (l : RLVal E Γ τ) :
    Effect F.static (evalE G F (fuel+1) (RExpr.delete (E := E) (Γ := Γ) l)) := by
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
