import Solidity.Lowering.Readonly.SourceBuiltinEffects
import Solidity.Lowering.Readonly.TupleCopyEffects

/-! Generated typed cuts of the actual Source expression history step.
No execution semantics or type/admission premise is replaced. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source

theorem evalE_const_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} (q : Q) :
    Effect F.static (evalE G F (fuel+1) (RExpr.const (E := E) (Γ := Γ) q)) := by
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

theorem evalE_bytesLit_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} (n : NumLit) (len : Nat) :
    Effect F.static (evalE G F (fuel+1) (RExpr.bytesLit (E := E) (Γ := Γ) n len)) := by
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

theorem evalE_addressLit_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} (ds : List (Fin 16)) :
    Effect F.static (evalE G F (fuel+1) (RExpr.addressLit (E := E) (Γ := Γ) ds)) := by
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

theorem evalE_bool_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} (b : Bool) :
    Effect F.static (evalE G F (fuel+1) (RExpr.bool (E := E) (Γ := Γ) b)) := by
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

theorem evalE_str_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} (bs : List UInt8) :
    Effect F.static (evalE G F (fuel+1) (RExpr.str (E := E) (Γ := Γ) bs)) := by
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

theorem evalE_local_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} {τ : STy} (i : Idx Γ τ) :
    Effect F.static (evalE G F (fuel+1) (RExpr.local (E := E) (Γ := Γ) i)) := by
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

theorem evalE_state_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} {τ : STy} (d : Decl) (h : d.varTy E = some τ) :
    Effect F.static (evalE G F (fuel+1) (RExpr.state (E := E) (Γ := Γ) d h)) := by
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
