import Solidity.Lowering.Readonly.SourceBuiltinEffects
import Solidity.Lowering.Readonly.TupleCopyEffects

/-! Generated typed cuts of the actual Source expression history step.
No execution semantics or type/admission premise is replaced. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source

theorem evalE_abiEncode_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} {σs : List STy} (k : AbiKind) (args : RArgs E Γ σs) :
    Effect F.static (evalE G F (fuel+1) (RExpr.abiEncode (E := E) (Γ := Γ) k args)) := by
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

theorem evalE_assignCopy_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} {τ σ : STy} (l : RLVal E Γ τ) (e : RExpr E Γ σ) (h : σ.copiesTo τ = true) :
    Effect F.static (evalE G F (fuel+1) (RExpr.assignCopy (E := E) (Γ := Γ) l e h)) := by
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

theorem evalE_abiDecode_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} {σ : STy} {τs : List STy} (data : RExpr E Γ σ) (hs : σ.decodeSrc = true) (hd : τs.all (STy.decodable E) = true) :
    Effect F.static (evalE G F (fuel+1) (RExpr.abiDecode (E := E) (Γ := Γ) data hs hd)) := by
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

theorem evalE_slice_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} {τ σ ρ : STy} (a : RExpr E Γ τ) (hτ : τ.sliceable = true) (s : RExpr E Γ σ) (hs : σ.isIndex = true) (e : RExpr E Γ ρ) (he : ρ.isIndex = true) (toEnd : Bool) :
    Effect F.static (evalE G F (fuel+1) (RExpr.slice (E := E) (Γ := Γ) a hτ s hs e he toEnd)) := by
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

theorem evalE_inlineArray_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} {σ : STy} {n : Nat} (args : RConvArgs E Γ (List.replicate n σ)) (hσ : σ.oneWord = true) :
    Effect F.static (evalE G F (fuel+1) (RExpr.inlineArray (E := E) (Γ := Γ) args hσ)) := by
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

theorem evalE_newArray_succ {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (_history : At G fuel) {Γ : RCtx} {τ σ : STy} (hτ : τ.newable = true) (len : RExpr E Γ σ) (hl : σ.isIndex = true) :
    Effect F.static (evalE G F (fuel+1) (RExpr.newArray (E := E) (Γ := Γ) hτ len hl)) := by
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
