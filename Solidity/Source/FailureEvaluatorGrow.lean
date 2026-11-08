import Solidity.Source.FailureFrameHorizon

/-! Event growth of the actual enabled-plan evaluator. This module reuses
Source's intrinsic functions, indices and existing induction proof partition.
It introduces no alternate evaluator, NoFail assumption or execution oracle.
No horizon approximation/session consistency or P8 adequacy is asserted here.
Both calldata modes instantiate the shared HorizonAt schema at the same fixed plan. -/
namespace Solidity.Source.FailureExecution.PlannedGrow
open EM
open Solidity.Roadmap (Address Word Bytes)
variable {E : Env} {points : Roadmap.Evm.FailurePoints}

structure GrowAt (G : Glob E) (points : Roadmap.Evm.FailurePoints) (n : Nat) : Prop where
  evalE : ∀ (F : Fr) ⦃Γ : RCtx⦄ ⦃τ : STy⦄ (e : RExpr E Γ τ), Grow (evalE (plan := some points) G F n e)
  evalPair : ∀ (F : Fr) ⦃Γ : RCtx⦄ ⦃σ τ : STy⦄ (a : RExpr E Γ σ) (b : RExpr E Γ τ), Grow (evalPair (plan := some points) G F n a b)
  evalArgs : ∀ (F : Fr) ⦃Γ : RCtx⦄ ⦃τs : List STy⦄ (es : RArgs E Γ τs), Grow (evalArgs (plan := some points) G F n es)
  evalConvArgs : ∀ (F : Fr) ⦃Γ : RCtx⦄ ⦃τs : List STy⦄ (es : RConvArgs E Γ τs), Grow (evalConvArgs (plan := some points) G F n es)
  evalLoc : ∀ (F : Fr) ⦃Γ : RCtx⦄ ⦃τ : STy⦄ (l : RLVal E Γ τ), Grow (evalLoc (plan := some points) G F n l)
  evalBuiltin : ∀ (F : Fr) ⦃Γ : RCtx⦄ ⦃σs : List STy⦄ (b : Builtin) (args : RArgs E Γ σs) (τ : STy), Grow (evalBuiltin (plan := some points) G F n b args τ)
  evalArgsRev : ∀ (F : Fr) ⦃Γ : RCtx⦄ ⦃τs : List STy⦄ (es : RArgs E Γ τs), Grow (evalArgsRev (plan := some points) G F n es)
  pay : ∀ (F : Fr) ⦃Γ : RCtx⦄ (a : RExpr E Γ (.address true)) (v : RExpr E Γ (.int IntTy.u256)), Grow (pay (plan := some points) G F n a v)
  execS : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) ⦃R : List STy⦄ ⦃M : Bool⦄ ⦃k : SCtx⦄ ⦃Γ Γ' : RCtx⦄ (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ), Grow (execS (plan := some points) G F n nps ph s l)
  forIter : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) ⦃R : List STy⦄ ⦃M u : Bool⦄ ⦃Γ₁ Γ₂ : RCtx⦄ (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂) (l : Locals E.layout Γ₁), Grow (forIter (plan := some points) G F n nps ph c post body l)
  execItems : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) ⦃R : List STy⦄ ⦃M : Bool⦄ ⦃k : SCtx⦄ ⦃Γ Γ' : RCtx⦄ (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ), Grow (execItems (plan := some points) G F n nps ph b l)
  runMods : ∀ (F : Fr) (b : RBody E) (mods : List (RModInv E b.locals)) (l : Locals E.layout b.locals), Grow (runMods (plan := some points) G F n b mods l)
  callInternal : ∀ (F : Fr) (d : Decl) ⦃ps : List STy⦄ (vs : Vals E.layout ps) (rs : List STy), Grow (callInternal (plan := some points) G F n d vs rs)
  callAddr : ∀ (F : Fr) (a : Address) (v : Word) (input : Bytes) (static : Bool), Grow (callAddr (plan := some points) G F n a v input static)
  enterInstance : ∀ (a sender : Address) (v : Word) (input : Bytes) (static : Bool) (c : String) (depth : Nat) (m : Nat × Nat × Heap E.layout), Grow (enterInstance (plan := some points) G n a sender v input static c depth m)
  envLoop : ∀ (depth : Nat) (pstatic : Bool), Grow (envLoop (plan := some points) G n depth pstatic)
  dispatch : ∀ (F : Fr) (input : Bytes), Grow (dispatch (plan := some points) G F n input)

abbrev GrowAtKnown (G : Glob E) (points : Roadmap.Evm.FailurePoints) (n : Nat) : Prop :=
  HorizonAt (fun {Γ} {α} (m _ : EM E Γ α) => Grow m) G n (some points)

theorem callLibrary_grow_step_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n)
    (F : Fr) (d : Decl) {ps : List STy} (vs : Vals E.layout ps) (rs : List STy) :
    Grow (callLibrary (plan := some points) G F (n + 1) d vs rs) := by
  simp only [callLibrary]; grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]


theorem evalE_grow_0_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (known : Bool) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 0 ≤ e.ctorIdx ∧ e.ctorIdx < 12) : Grow (evalE (plan := some points) G F (n + 1) e (calldataKnown := known)) := by
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (simp only [evalE]; apply Grow.withLibraryCalldata; grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow])

theorem evalE_grow_1_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (known : Bool) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 12 ≤ e.ctorIdx ∧ e.ctorIdx < 24) : Grow (evalE (plan := some points) G F (n + 1) e (calldataKnown := known)) := by
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (simp only [evalE]; apply Grow.withLibraryCalldata; grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow])

theorem evalE_grow_2_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (known : Bool) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 24 ≤ e.ctorIdx ∧ e.ctorIdx < 36) : Grow (evalE (plan := some points) G F (n + 1) e (calldataKnown := known)) := by
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (simp only [evalE]; apply Grow.withLibraryCalldata; grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow])

theorem evalE_grow_3_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (known : Bool) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 36 ≤ e.ctorIdx ∧ e.ctorIdx < 60) : Grow (evalE (plan := some points) G F (n + 1) e (calldataKnown := known)) := by
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (simp only [evalE]; apply Grow.withLibraryCalldata; grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow])

theorem evalE_grow_step_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (known : Bool) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ) :
    Grow (evalE (plan := some points) G F (n + 1) e (calldataKnown := known)) := by
  by_cases h0 : e.ctorIdx < 12
  · exact evalE_grow_0_known ih known F e ⟨Nat.zero_le _, h0⟩
  by_cases h1 : e.ctorIdx < 24
  · exact evalE_grow_1_known ih known F e ⟨by omega, h1⟩
  by_cases h2 : e.ctorIdx < 36
  · exact evalE_grow_2_known ih known F e ⟨by omega, h2⟩
  have h3 : e.ctorIdx < 60 := by cases e <;> simp only [RExpr.ctorIdx] <;> omega
  exact evalE_grow_3_known ih known F e ⟨by omega, h3⟩

theorem evalPair_grow_step_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (known : Bool) (F : Fr) {Γ : RCtx} {σ τ : STy} (a : RExpr E Γ σ) (b : RExpr E Γ τ) :
    Grow (evalPair (plan := some points) G F (n + 1) a b (calldataKnown := known)) := by
  simp only [evalPair]; grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]

theorem evalArgs_grow_step_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (known : Bool) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Grow (evalArgs (plan := some points) G F (n + 1) es (calldataKnown := known)) := by
  cases es <;> simp only [evalArgs] <;> grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]

theorem evalConvArgs_grow_step_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (known : Bool) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RConvArgs E Γ τs) :
    Grow (evalConvArgs (plan := some points) G F (n + 1) es (calldataKnown := known)) := by
  cases es <;> simp only [evalConvArgs] <;> grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]

theorem evalLoc_grow_step_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (known : Bool) (F : Fr) {Γ : RCtx} {τ : STy} (l : RLVal E Γ τ) :
    Grow (evalLoc (plan := some points) G F (n + 1) l (calldataKnown := known)) := by
  cases l <;> simp only [evalLoc] <;> grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]

theorem evalBuiltin_grow_0_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (known : Bool) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .require ∨ b = .assert ∨ b = .revert) :
    Grow (evalBuiltin (plan := some points) G F (n + 1) b args τ (calldataKnown := known)) := by
  rcases hb with rfl | rfl | rfl <;> simp only [evalBuiltin] <;> grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]

theorem evalBuiltin_grow_1_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (known : Bool) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .keccak256 ∨ b = .sha256 ∨ b = .ripemd160) :
    Grow (evalBuiltin (plan := some points) G F (n + 1) b args τ (calldataKnown := known)) := by
  rcases hb with rfl | rfl | rfl <;> simp only [evalBuiltin] <;> grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]

theorem evalBuiltin_grow_2_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (known : Bool) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .addmod) :
    Grow (evalBuiltin (plan := some points) G F (n + 1) b args τ (calldataKnown := known)) := by
  rcases hb with rfl <;> simp only [evalBuiltin] <;> grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]

theorem evalBuiltin_grow_3_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (known : Bool) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .mulmod) :
    Grow (evalBuiltin (plan := some points) G F (n + 1) b args τ (calldataKnown := known)) := by
  rcases hb with rfl <;> simp only [evalBuiltin] <;> grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]

theorem evalBuiltin_grow_4_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (known : Bool) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .ecrecover) :
    Grow (evalBuiltin (plan := some points) G F (n + 1) b args τ (calldataKnown := known)) := by
  rcases hb with rfl <;> simp only [evalBuiltin] <;> grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]

theorem evalBuiltin_grow_step_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (known : Bool) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) : Grow (evalBuiltin (plan := some points) G F (n + 1) b args τ (calldataKnown := known)) := by
  cases b
  all_goals first
    | exact evalBuiltin_grow_0_known ih known F _ args τ (by decide)
    | exact evalBuiltin_grow_1_known ih known F _ args τ (by decide)
    | exact evalBuiltin_grow_2_known ih known F _ args τ (by decide)
    | exact evalBuiltin_grow_3_known ih known F _ args τ (by decide)
    | exact evalBuiltin_grow_4_known ih known F _ args τ (by decide)
    | (simp only [evalBuiltin]; grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow])

theorem evalArgsRev_grow_step_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (known : Bool) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Grow (evalArgsRev (plan := some points) G F (n + 1) es (calldataKnown := known)) := by
  cases es <;> simp only [evalArgsRev] <;> grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]

theorem pay_grow_step_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (known : Bool) (F : Fr) {Γ : RCtx} (a : RExpr E Γ (.address true)) (v : RExpr E Γ (.int IntTy.u256)) :
    Grow (pay (plan := some points) G F (n + 1) a v (calldataKnown := known)) := by
  simp only [pay]; grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]

theorem execS_grow_step_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (known : Bool) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ) :
    Grow (execS (plan := some points) G F (n + 1) nps ph s l (calldataKnown := known)) := by
  cases s <;> simp only [execS] <;> grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]

theorem forIter_grow_step_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (known : Bool) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M u : Bool} {Γ₁ Γ₂ : RCtx} (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂) (l : Locals E.layout Γ₁) :
    Grow (forIter (plan := some points) G F (n + 1) nps ph c post body l (calldataKnown := known)) := by
  cases c <;> simp only [forIter] <;> grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]

theorem execItems_grow_step_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (known : Bool) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx} (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ) :
    Grow (execItems (plan := some points) G F (n + 1) nps ph b l (calldataKnown := known)) := by
  cases b <;> simp only [execItems] <;> grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]

theorem runMods_grow_step_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (known : Bool) (F : Fr) (b : RBody E) (mods : List (RModInv E b.locals)) (l : Locals E.layout b.locals) :
    Grow (runMods (plan := some points) G F (n + 1) b mods l (calldataKnown := known)) := by
  cases mods <;> simp only [runMods] <;> grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]

theorem callInternal_grow_step_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (known : Bool) (F : Fr) (d : Decl) {ps : List STy} (vs : Vals E.layout ps) (rs : List STy) :
    Grow (callInternal (plan := some points) G F (n + 1) d vs rs (calldataKnown := known)) := by
  simp only [callInternal]; grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]

theorem callAddr_grow_step_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (F : Fr) (a : Address) (v : Word) (input : Bytes) (static : Bool) :
    Grow (callAddr (plan := some points) G F (n + 1) a v input static) := by
  simp only [callAddr]; grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]

theorem enterInstance_grow_step_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (a sender : Address) (v : Word) (input : Bytes) (static : Bool) (c : String) (depth : Nat) (m : Nat × Nat × Heap E.layout) :
    Grow (enterInstance (plan := some points) G (n + 1) a sender v input static c depth m) := by
  simp only [enterInstance]; grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]

theorem envLoop_grow_step_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (depth : Nat) (pstatic : Bool) :
    Grow (envLoop (plan := some points) G (n + 1) depth pstatic) := by
  rw [envLoop.eq_2 G depth pstatic (some points) n]; grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]

theorem dispatch_grow_fn_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (F : Fr) (input : Bytes) {d : Decl}
    (hp : G.pickFn F input = some d) (he : input.isEmpty = false) : Grow (dispatch (plan := some points) G F (n + 1) input) := by
  simp only [dispatch, hp, he]; grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]

theorem dispatch_grow_getter_none_c_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {d : Decl} {ps : List STy} {ρ : STy} {ri : RInit E}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hc : G.prog.consts d = some ri) :
    Grow (dispatch (plan := some points) G F (n + 1) input) := by
  simp only [dispatch, hp, hc, hg]; grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]

theorem dispatch_grow_getter_none_v_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {d : Decl} {ps : List STy} {ρ : STy} {τ : STy}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hc : G.prog.consts d = none) (hv : d.varTy E = some τ) :
    Grow (dispatch (plan := some points) G F (n + 1) input) := by
  simp only [dispatch, hp, hc, hv, hg]; grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]

theorem dispatch_grow_getter_none_x_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {d : Decl} {ps : List STy} {ρ : STy}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hc : G.prog.consts d = none) (hv : d.varTy E = none) :
    Grow (dispatch (plan := some points) G F (n + 1) input) := by
  simp only [dispatch, hp, hc, hv, hg]; grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]

theorem dispatch_grow_getter_none_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {r : Decl × List STy × STy} (hg : G.pickGetter F input = some r) :
    Grow (dispatch (plan := some points) G F (n + 1) input) := by
  obtain ⟨d, ps, ρ⟩ := r
  cases hc : G.prog.consts d with
  | some ri => exact dispatch_grow_getter_none_c_known ih F input hp hg hc
  | none =>
    cases hv : d.varTy E with
    | some τ => exact dispatch_grow_getter_none_v_known ih F input hp hg hc hv
    | none => exact dispatch_grow_getter_none_x_known ih F input hp hg hc hv

theorem dispatch_grow_getter_some_c_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {d : Decl} {ps : List STy} {ρ : STy} {ri : RInit E}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hc : G.prog.consts d = some ri) :
    Grow (dispatch (plan := some points) G F (n + 1) input) := by
  simp only [dispatch, hp, he, hc, hg]; grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]

theorem dispatch_grow_getter_some_v_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {d : Decl} {ps : List STy} {ρ : STy} {τ : STy}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hc : G.prog.consts d = none) (hv : d.varTy E = some τ) :
    Grow (dispatch (plan := some points) G F (n + 1) input) := by
  simp only [dispatch, hp, he, hc, hv, hg]; grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]

theorem dispatch_grow_getter_some_x_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {d : Decl} {ps : List STy} {ρ : STy}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hc : G.prog.consts d = none) (hv : d.varTy E = none) :
    Grow (dispatch (plan := some points) G F (n + 1) input) := by
  simp only [dispatch, hp, he, hc, hv, hg]; grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]

theorem dispatch_grow_getter_some_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {r : Decl × List STy × STy} (hg : G.pickGetter F input = some r) :
    Grow (dispatch (plan := some points) G F (n + 1) input) := by
  obtain ⟨d, ps, ρ⟩ := r
  cases hc : G.prog.consts d with
  | some ri => exact dispatch_grow_getter_some_c_known ih F input hp he hg hc
  | none =>
    cases hv : d.varTy E with
    | some τ => exact dispatch_grow_getter_some_v_known ih F input hp he hg hc hv
    | none => exact dispatch_grow_getter_some_x_known ih F input hp he hg hc hv

theorem dispatch_grow_getter_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (F : Fr) (input : Bytes) (b : Bool) {r : Decl × List STy × STy}
    (hm : (G.pickFn F input, input.isEmpty) = (none, b) ∨ ∃ d, (G.pickFn F input, input.isEmpty) = (some d, true))
    (hg : G.pickGetter F input = some r) : Grow (dispatch (plan := some points) G F (n + 1) input) := by
  rcases hm with hm | ⟨d, hm⟩ <;> simp only [Prod.mk.injEq] at hm
  · exact dispatch_grow_getter_none_known ih F input hm.1 hg
  · exact dispatch_grow_getter_some_known ih F input hm.1 hm.2 hg

theorem dispatch_grow_special_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (F : Fr) (input : Bytes) (b : Bool)
    (hm : (G.pickFn F input, input.isEmpty) = (none, b) ∨ ∃ d, (G.pickFn F input, input.isEmpty) = (some d, true))
    (hg : G.pickGetter F input = none) : Grow (dispatch (plan := some points) G F (n + 1) input) := by
  rcases hm with hm | ⟨d, hm⟩ <;> simp only [Prod.mk.injEq] at hm <;> simp only [dispatch, hm.1, hm.2, hg] <;>
    grow_go [check_grow, frame_grow, emit_plan_grow, ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, abiDecodeData_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, pushVals_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]

theorem dispatch_grow_step_known {G : Glob E} {n : Nat} (ih : GrowAtKnown G points n) (F : Fr) (input : Bytes) : Grow (dispatch (plan := some points) G F (n + 1) input) := by
  cases hp : G.pickFn F input with
  | some d =>
    cases he : input.isEmpty with
    | false => exact dispatch_grow_fn_known ih F input hp he
    | true =>
      cases hg : G.pickGetter F input with
      | some r => exact dispatch_grow_getter_known ih F input true (.inr ⟨d, by rw [hp, he]⟩) hg
      | none => exact dispatch_grow_special_known ih F input true (.inr ⟨d, by rw [hp, he]⟩) hg
  | none =>
    cases hg : G.pickGetter F input with
    | some r => exact dispatch_grow_getter_known ih F input _ (.inl (by rw [hp])) hg
    | none => exact dispatch_grow_special_known ih F input _ (.inl (by rw [hp])) hg

theorem growAtKnown_zero (G : Glob E) : GrowAtKnown G points 0 := by
  exact {
    evalE := by intros; exact Grow.halt _,
    evalPair := by intros; exact Grow.halt _,
    evalArgs := by intros; exact Grow.halt _,
    evalConvArgs := by intros; exact Grow.halt _,
    evalLoc := by intros; exact Grow.halt _,
    evalBuiltin := by intros; exact Grow.halt _,
    evalArgsRev := by intros; exact Grow.halt _,
    pay := by intros; exact Grow.halt _,
    execS := by intros; exact Grow.halt _,
    forIter := by intros; exact Grow.halt _,
    execItems := by intros; exact Grow.halt _,
    runMods := by intros; exact Grow.halt _,
    callInternal := by intros; exact Grow.halt _,
    callLibrary := by intros; exact Grow.halt _,
    callAddr := by intros; exact Grow.halt _,
    enterInstance := by intros; exact Grow.halt _,
    envLoop := by intros; exact Grow.halt _,
    dispatch := by intros; exact Grow.halt _
  }

theorem growAtKnown (G : Glob E) : ∀ n, GrowAtKnown G points n := by
  intro n
  induction n with
  | zero => exact growAtKnown_zero G
  | succ n ih => exact ⟨evalE_grow_step_known ih, evalPair_grow_step_known ih, evalArgs_grow_step_known ih, evalConvArgs_grow_step_known ih, evalLoc_grow_step_known ih, evalBuiltin_grow_step_known ih, evalArgsRev_grow_step_known ih, pay_grow_step_known ih, execS_grow_step_known ih, forIter_grow_step_known ih, execItems_grow_step_known ih, runMods_grow_step_known ih, callInternal_grow_step_known ih, callLibrary_grow_step_known ih, callAddr_grow_step_known ih, enterInstance_grow_step_known ih, envLoop_grow_step_known ih, dispatch_grow_step_known ih⟩



theorem growAt_zero (G : Glob E) : GrowAt G points 0 where
  evalE := by intros; rw [evalE.eq_1]; exact Grow.halt _
  evalPair := by intros; rw [evalPair.eq_1]; exact Grow.halt _
  evalArgs := by intros; rw [evalArgs.eq_1]; exact Grow.halt _
  evalConvArgs := by intros; rw [evalConvArgs.eq_1]; exact Grow.halt _
  evalLoc := by intros; rw [evalLoc.eq_1]; exact Grow.halt _
  evalBuiltin := by intros; rw [evalBuiltin.eq_1]; exact Grow.halt _
  evalArgsRev := by intros; rw [evalArgsRev.eq_1]; exact Grow.halt _
  pay := by intros; rw [pay.eq_1]; exact Grow.halt _
  execS := by intros; rw [execS.eq_1]; exact Grow.halt _
  forIter := by intros; rw [forIter.eq_1]; exact Grow.halt _
  execItems := by intros; rw [execItems.eq_1]; exact Grow.halt _
  runMods := by intros; rw [runMods.eq_1]; exact Grow.halt _
  callInternal := by intros; rw [callInternal.eq_1]; exact Grow.halt _
  callAddr := by intros; rw [callAddr.eq_1]; exact Grow.halt _
  enterInstance := by intros; rw [enterInstance.eq_1]; exact Grow.halt _
  envLoop := by intros; rw [envLoop.eq_1]; exact Grow.halt _
  dispatch := by intros; rw [dispatch.eq_1]; exact Grow.halt _

theorem evalE_grow_0 {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 0 ≤ e.ctorIdx ∧ e.ctorIdx < 12) : Grow (evalE (plan := some points) G F (n + 1) e) := by
  exact (growAtKnown G (points := points) (n + 1)).evalE true F e

theorem evalE_grow_1 {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 12 ≤ e.ctorIdx ∧ e.ctorIdx < 24) : Grow (evalE (plan := some points) G F (n + 1) e) := by
  exact (growAtKnown G (points := points) (n + 1)).evalE true F e

theorem evalE_grow_2 {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 24 ≤ e.ctorIdx ∧ e.ctorIdx < 36) : Grow (evalE (plan := some points) G F (n + 1) e) := by
  exact (growAtKnown G (points := points) (n + 1)).evalE true F e

theorem evalE_grow_3 {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 36 ≤ e.ctorIdx ∧ e.ctorIdx < 60) : Grow (evalE (plan := some points) G F (n + 1) e) := by
  exact (growAtKnown G (points := points) (n + 1)).evalE true F e

theorem evalE_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ) :
    Grow (evalE (plan := some points) G F (n + 1) e) := by
  exact (growAtKnown G (points := points) (n + 1)).evalE true F e

theorem evalPair_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) {Γ : RCtx} {σ τ : STy} (a : RExpr E Γ σ) (b : RExpr E Γ τ) :
    Grow (evalPair (plan := some points) G F (n + 1) a b) := by
  exact (growAtKnown G (points := points) (n + 1)).evalPair true F a b

theorem evalArgs_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Grow (evalArgs (plan := some points) G F (n + 1) es) := by
  exact (growAtKnown G (points := points) (n + 1)).evalArgs true F es

theorem evalConvArgs_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RConvArgs E Γ τs) :
    Grow (evalConvArgs (plan := some points) G F (n + 1) es) := by
  exact (growAtKnown G (points := points) (n + 1)).evalConvArgs true F es

theorem evalLoc_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) {Γ : RCtx} {τ : STy} (l : RLVal E Γ τ) :
    Grow (evalLoc (plan := some points) G F (n + 1) l) := by
  exact (growAtKnown G (points := points) (n + 1)).evalLoc true F l

theorem evalBuiltin_grow_0 {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .require ∨ b = .assert ∨ b = .revert) :
    Grow (evalBuiltin (plan := some points) G F (n + 1) b args τ) := by
  exact (growAtKnown G (points := points) (n + 1)).evalBuiltin true F b args τ

theorem evalBuiltin_grow_1 {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .keccak256 ∨ b = .sha256 ∨ b = .ripemd160) :
    Grow (evalBuiltin (plan := some points) G F (n + 1) b args τ) := by
  exact (growAtKnown G (points := points) (n + 1)).evalBuiltin true F b args τ

theorem evalBuiltin_grow_2 {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .addmod) :
    Grow (evalBuiltin (plan := some points) G F (n + 1) b args τ) := by
  exact (growAtKnown G (points := points) (n + 1)).evalBuiltin true F b args τ

theorem evalBuiltin_grow_3 {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .mulmod) :
    Grow (evalBuiltin (plan := some points) G F (n + 1) b args τ) := by
  exact (growAtKnown G (points := points) (n + 1)).evalBuiltin true F b args τ

theorem evalBuiltin_grow_4 {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .ecrecover) :
    Grow (evalBuiltin (plan := some points) G F (n + 1) b args τ) := by
  exact (growAtKnown G (points := points) (n + 1)).evalBuiltin true F b args τ

theorem evalBuiltin_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) : Grow (evalBuiltin (plan := some points) G F (n + 1) b args τ) := by
  exact (growAtKnown G (points := points) (n + 1)).evalBuiltin true F b args τ

theorem evalArgsRev_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Grow (evalArgsRev (plan := some points) G F (n + 1) es) := by
  exact (growAtKnown G (points := points) (n + 1)).evalArgsRev true F es

theorem pay_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) {Γ : RCtx} (a : RExpr E Γ (.address true)) (v : RExpr E Γ (.int IntTy.u256)) :
    Grow (pay (plan := some points) G F (n + 1) a v) := by
  exact (growAtKnown G (points := points) (n + 1)).pay true F a v

theorem execS_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ) :
    Grow (execS (plan := some points) G F (n + 1) nps ph s l) := by
  exact (growAtKnown G (points := points) (n + 1)).execS true F nps ph s l

theorem forIter_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M u : Bool} {Γ₁ Γ₂ : RCtx} (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂) (l : Locals E.layout Γ₁) :
    Grow (forIter (plan := some points) G F (n + 1) nps ph c post body l) := by
  exact (growAtKnown G (points := points) (n + 1)).forIter true F nps ph c post body l

theorem execItems_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx} (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ) :
    Grow (execItems (plan := some points) G F (n + 1) nps ph b l) := by
  exact (growAtKnown G (points := points) (n + 1)).execItems true F nps ph b l

theorem runMods_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) (b : RBody E) (mods : List (RModInv E b.locals)) (l : Locals E.layout b.locals) :
    Grow (runMods (plan := some points) G F (n + 1) b mods l) := by
  exact (growAtKnown G (points := points) (n + 1)).runMods true F b mods l

theorem callInternal_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) (d : Decl) {ps : List STy} (vs : Vals E.layout ps) (rs : List STy) :
    Grow (callInternal (plan := some points) G F (n + 1) d vs rs) := by
  exact (growAtKnown G (points := points) (n + 1)).callInternal true F d vs rs

theorem callAddr_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) (a : Address) (v : Word) (input : Bytes) (static : Bool) :
    Grow (callAddr (plan := some points) G F (n + 1) a v input static) := by
  exact (growAtKnown G (points := points) (n + 1)).callAddr F a v input static

theorem enterInstance_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G points n) (a sender : Address) (v : Word) (input : Bytes) (static : Bool) (c : String) (depth : Nat) (m : Nat × Nat × Heap E.layout) :
    Grow (enterInstance (plan := some points) G (n + 1) a sender v input static c depth m) := by
  exact (growAtKnown G (points := points) (n + 1)).enterInstance a sender v input static c depth m

theorem envLoop_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G points n) (depth : Nat) (pstatic : Bool) :
    Grow (envLoop (plan := some points) G (n + 1) depth pstatic) := by
  exact (growAtKnown G (points := points) (n + 1)).envLoop depth pstatic

theorem dispatch_grow_fn {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) (input : Bytes) {d : Decl}
    (hp : G.pickFn F input = some d) (he : input.isEmpty = false) : Grow (dispatch (plan := some points) G F (n + 1) input) := by
  exact (growAtKnown G (points := points) (n + 1)).dispatch F input

theorem dispatch_grow_getter_none_c {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {d : Decl} {ps : List STy} {ρ : STy} {ri : RInit E}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hc : G.prog.consts d = some ri) :
    Grow (dispatch (plan := some points) G F (n + 1) input) := by
  exact (growAtKnown G (points := points) (n + 1)).dispatch F input

theorem dispatch_grow_getter_none_v {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {d : Decl} {ps : List STy} {ρ : STy} {τ : STy}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hc : G.prog.consts d = none) (hv : d.varTy E = some τ) :
    Grow (dispatch (plan := some points) G F (n + 1) input) := by
  exact (growAtKnown G (points := points) (n + 1)).dispatch F input

theorem dispatch_grow_getter_none_x {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {d : Decl} {ps : List STy} {ρ : STy} 
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hc : G.prog.consts d = none) (hv : d.varTy E = none) :
    Grow (dispatch (plan := some points) G F (n + 1) input) := by
  exact (growAtKnown G (points := points) (n + 1)).dispatch F input

theorem dispatch_grow_getter_none {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {r : Decl × List STy × STy} (hg : G.pickGetter F input = some r) :
    Grow (dispatch (plan := some points) G F (n + 1) input) := by
  exact (growAtKnown G (points := points) (n + 1)).dispatch F input

theorem dispatch_grow_getter_some_c {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {d : Decl} {ps : List STy} {ρ : STy} {ri : RInit E}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hc : G.prog.consts d = some ri) :
    Grow (dispatch (plan := some points) G F (n + 1) input) := by
  exact (growAtKnown G (points := points) (n + 1)).dispatch F input

theorem dispatch_grow_getter_some_v {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {d : Decl} {ps : List STy} {ρ : STy} {τ : STy}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hc : G.prog.consts d = none) (hv : d.varTy E = some τ) :
    Grow (dispatch (plan := some points) G F (n + 1) input) := by
  exact (growAtKnown G (points := points) (n + 1)).dispatch F input

theorem dispatch_grow_getter_some_x {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {d : Decl} {ps : List STy} {ρ : STy} 
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hc : G.prog.consts d = none) (hv : d.varTy E = none) :
    Grow (dispatch (plan := some points) G F (n + 1) input) := by
  exact (growAtKnown G (points := points) (n + 1)).dispatch F input

theorem dispatch_grow_getter_some {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {r : Decl × List STy × STy} (hg : G.pickGetter F input = some r) :
    Grow (dispatch (plan := some points) G F (n + 1) input) := by
  exact (growAtKnown G (points := points) (n + 1)).dispatch F input

theorem dispatch_grow_getter {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) (input : Bytes) (b : Bool) {r : Decl × List STy × STy}
    (hm : (G.pickFn F input, input.isEmpty) = (none, b) ∨ ∃ d, (G.pickFn F input, input.isEmpty) = (some d, true))
    (hg : G.pickGetter F input = some r) : Grow (dispatch (plan := some points) G F (n + 1) input) := by
  exact (growAtKnown G (points := points) (n + 1)).dispatch F input

theorem dispatch_grow_special {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) (input : Bytes) (b : Bool)
    (hm : (G.pickFn F input, input.isEmpty) = (none, b) ∨ ∃ d, (G.pickFn F input, input.isEmpty) = (some d, true))
    (hg : G.pickGetter F input = none) : Grow (dispatch (plan := some points) G F (n + 1) input) := by
  exact (growAtKnown G (points := points) (n + 1)).dispatch F input

theorem dispatch_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G points n) (F : Fr) (input : Bytes) : Grow (dispatch (plan := some points) G F (n + 1) input) := by
  exact (growAtKnown G (points := points) (n + 1)).dispatch F input

theorem growAt (G : Glob E) : ∀ n, GrowAt G points n
  | 0 => growAt_zero G
  | n + 1 =>
    have ih := growAt G n
    ⟨evalE_grow_step ih, evalPair_grow_step ih, evalArgs_grow_step ih, evalConvArgs_grow_step ih, evalLoc_grow_step ih, evalBuiltin_grow_step ih, evalArgsRev_grow_step ih, pay_grow_step ih, execS_grow_step ih, forIter_grow_step ih, execItems_grow_step ih, runMods_grow_step ih, callInternal_grow_step ih, callAddr_grow_step ih, enterInstance_grow_step ih, envLoop_grow_step ih, dispatch_grow_step ih⟩


end Solidity.Source.FailureExecution.PlannedGrow
