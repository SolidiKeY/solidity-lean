import Solidity.Lowering.Readonly.SourceBuiltinEffects
import Solidity.Lowering.Readonly.TupleCopyEffects

/-! Generated typed cuts of the actual Source expression history step.
No execution semantics or type/admission premise is replaced. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source

theorem evalE_balance_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} {p : Bool} (a : RExpr E Γ (.address p)) :
    Effect F.static (evalE G F (fuel+1) (RExpr.balance (E := E) (Γ := Γ) a)) := by
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

theorem evalE_builtin_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} {σs : List STy} {τ : STy} (b : Builtin) (args : RArgs E Γ σs) (h : b.callTy E.isBase σs = some τ) :
    Effect F.static (evalE G F (fuel+1) (RExpr.builtin (E := E) (Γ := Γ) b args h)) := by
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

theorem evalE_member_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} {l : DataLoc} {dn : DeclName} {τ : STy} (a : RExpr E Γ (.struct l dn)) (i : Nat) (h : E.fieldTy? dn l i = some τ) :
    Effect F.static (evalE G F (fuel+1) (RExpr.member (E := E) (Γ := Γ) a i h)) := by
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

theorem evalE_structNew_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} {dn : DeclName} {ps : List STy} (h : (E.structFields dn .memory).map (·.map Prod.snd) = some ps) (args : RConvArgs E Γ ps) :
    Effect F.static (evalE G F (fuel+1) (RExpr.structNew (E := E) (Γ := Γ) h args)) := by
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

theorem evalE_extCall_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} {dn : DeclName} {ps rs : List STy} (target : RExpr E Γ (.contract dn)) (d : Decl) (h : d.fnSig E = some (ps, rs)) (value : RExpr E Γ (.int IntTy.u256)) (args : RConvArgs E Γ ps) :
    Effect F.static (evalE G F (fuel+1) (RExpr.extCall (E := E) (Γ := Γ) target d h value args)) := by
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

theorem evalE_transfer_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} (a : RExpr E Γ (.address true)) (v : RExpr E Γ (.int IntTy.u256)) :
    Effect F.static (evalE G F (fuel+1) (RExpr.transfer (E := E) (Γ := Γ) a v)) := by
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

theorem evalE_send_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} (a : RExpr E Γ (.address true)) (v : RExpr E Γ (.int IntTy.u256)) :
    Effect F.static (evalE G F (fuel+1) (RExpr.send (E := E) (Γ := Γ) a v)) := by
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
