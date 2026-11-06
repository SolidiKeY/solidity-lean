import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingOuterZero
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarOutcomes

/-! Actual checked subtraction at the allocating call argument boundary.
Zero counter bare-reverts; it does not wrap. Universal frozen return claims
reuse actual source outcomes and unchanged state-indexed plan metadata. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterClaims
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource ScalarAllocatingDescent

theorem decrement_zero (caller : State C (Frame A))
 (counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) caller.env=countValue 0 W_pos) :
 AllocatingScalarEntry.decrement.evalT caller=.error .revert := by
 simp only [AllocatingScalarEntry.decrement,Val.evalT,Simple.evalT,counter,PrimTy.ofLit,
   BinOp.shortT,BinOp.evalT,BinOp.evalNum,BinOp.arithInt,countValue,indexValue,
   Option.bind_some,PrimTy.ofInt?,TRes.ofOpt,ok_bind]
 rfl

theorem next_zero (caller : State C (Frame A)) (ref : HRef caller.H A)
 (counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) caller.env=countValue 0 W_pos)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame A) (.mem A)) caller.env=some ref) :
 (next A (by rfl)).evalT caller=.error .revert := by
 have failed := decrement_zero caller counter
 change (do
   let arguments ← (Args.snocMemory Args.nil A (.user "alias") (.var (.there (.there .here)) (by rfl))).evalT caller
   let value ← AllocatingScalarEntry.decrement.evalT caller
   pure (value,arguments))=_
 simp only [Args.evalT,MPath.mvalT,alias,failed,ok_bind]
 rfl

theorem source_zero (depth : Nat) (caller : State C (Frame A)) (ref : HRef caller.H A)
 (counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) caller.env=countValue 0 W_pos)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame A) (.mem A)) caller.env=some ref) :
 (AllocatingOuterFamily.source depth).run caller=.error .revert := by
 change TRun.call (next A (by rfl)) (result A) (AllocatingScalarSource.body A (by rfl) depth).ext
   (AllocatingScalarSource.body A (by rfl) depth).runR caller=_
 simp only [TRun.call,next_zero caller ref counter alias,error_bind]

theorem source_short (depth n : Nat) (caller : State C (Frame A)) (fit : n+1<W) (ref : HRef caller.H A)
 (counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) caller.env=countValue (n+1) fit)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame A) (.mem A)) caller.env=some ref)
 (short : depth≤n) : (AllocatingOuterFamily.source depth).run caller=.error .exhausted := by
 have args := next_eval (by rfl) caller n fit ref counter alias
 have exhausted := AllocatingScalarSource.exhaustion (by rfl) depth (entered caller n (by omega) ref)
   n (by omega) ref rfl rfl short
 change TRun.call (next A (by rfl)) (result A) (AllocatingScalarSource.body A (by rfl) depth).ext
   (AllocatingScalarSource.body A (by rfl) depth).runR caller=_
 unfold TRun.call
 simp only [args,ok_bind,result,CallRet.enterT]
 change (do
   let out ← (AllocatingScalarSource.body A (by rfl) depth).run (entered caller n (by omega) ref)
   pure (exported (result A) (AllocatingScalarSource.body A (by rfl) depth).ext caller
     (countValue n (by omega),(some ref,())) out))=_
 rw [exhausted]
 rfl

theorem returns (depth : Nat) :
 InterfaceV1.ReturnClaim 2 F (AllocatingOuterFamily.source depth) (AllocatingOuterPlan.plan.at depth) := by
 intro L frame caller base before start entry out source
 obtain ⟨ref,alias,word⟩ := entry.represented.pointers (.there (.there .here) : Idx (Frame A) (.mem A))
 let value := TEnv.get (.there .here : Idx (Frame A) (.val .uint)) caller.env
 have normalized : value=countValue value.word.val value.word.isLt := Subtype.ext (word_val value).symm
 cases countEq : value.word.val with
 | zero =>
   have counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) caller.env=countValue 0 W_pos := by
     simpa only [countEq] using normalized
   rw [source_zero depth caller ref counter alias] at source
   cases source
 | succ n =>
   have fit : n+1<W := by have valid := value.word.isLt;omega
   have counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) caller.env=countValue (n+1) fit := by
     simpa only [countEq] using normalized
   have enough : n<depth := by
     by_cases enough : n<depth
     · exact enough
     · rw [source_short depth n caller fit ref counter alias (by omega)] at source
       cases source
   obtain ⟨actual,native,returned⟩ := AllocatingOuterZero.all_counts depth n caller fit ref counter alias
     L frame base before start entry enough
   have same : actual=out := Except.ok.inj (native.symm.trans source)
   subst actual
   exact returned

theorem target_zero (depth : Nat) (caller : State C (Frame A)) (ref : HRef caller.H A)
 (counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) caller.env=countValue 0 W_pos)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame A) (.mem A)) caller.env=some ref)
 (L frame : Nat) (base : Nat → Fin W) (before : Machine) (start : Nat)
 (entry : InterfaceV1.Entry (AllocatingOuterPlan.plan.at depth) L 2 frame F caller base before start) :
 run (AllocatingOuterPlan.plan.at depth).code before=.revert := by
 have demandEq : AllocatingOuterPlan.demand caller=0 := by
   simp only [AllocatingOuterPlan.demand,next_zero caller ref counter alias]
 have reserve : start+max 4 (3+3*0)≤frame := by
   simpa only [AllocatingOuterPlan.plan,InterfaceV1.RecursiveEmission.at,demandEq] using entry.reserve
 have noWrap : start+max 4 (3+3*0)<W := by
   simpa only [AllocatingOuterPlan.plan,InterfaceV1.RecursiveEmission.at,demandEq] using entry.noWrap
 have above : 8≤start := entry.payloadAbove
 have separate : 8<start ∨ start+max 4 (3+3*0)≤8 := by
   simpa only [AllocatingOuterPlan.plan,InterfaceV1.RecursiveEmission.at,demandEq] using entry.separate
 obtain ⟨saved,savedRun,captured,savedRepr,growth⟩ :=
   Context.capture_context (σ:=caller) (F:=F) (base:=base) before 8 8 start entry.represented
     (by decide) (by decide) (by omega) (by omega) (by change start+3≤frame;omega)
     (.inl (by omega)) (by change start+3<W;omega) entry.cursor
 have failed := decrement_zero caller counter
 have valueRun : run (AllocatingScalarEntry.compiled (C:=C) 2 F).code saved=.revert := by
   rcases (AllocatingScalarEntry.compiled (C:=C) 2 F).cert.correct savedRepr with
     ⟨value,word,evaluated,encoded,actual⟩ | ⟨evaluated,actual⟩
   · rw [failed] at evaluated
     cases evaluated
   · exact actual
 have entryRun : run (AllocatingScalarEntry.code (C:=C) 2 F) saved=.revert := run_append_revert valueRun
 have headRun : run (Restore.saveCells 8 (Restore.contextCells 2 (Frame A)) ++ AllocatingScalarEntry.code (C:=C) 2 F) before=.revert :=
   (run_append_ok savedRun).trans entryRun
 exact run_append_revert (run_append_revert (run_append_revert headRun))

theorem bare_revert (depth : Nat) :
 InterfaceV1.BareRevertClaim 2 F (AllocatingOuterFamily.source depth) (AllocatingOuterPlan.plan.at depth) := by
 intro L frame caller base before start entry source
 obtain ⟨ref,alias,word⟩ := entry.represented.pointers (.there (.there .here) : Idx (Frame A) (.mem A))
 let value := TEnv.get (.there .here : Idx (Frame A) (.val .uint)) caller.env
 have normalized : value=countValue value.word.val value.word.isLt := Subtype.ext (word_val value).symm
 cases countEq : value.word.val with
 | zero =>
   have counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) caller.env=countValue 0 W_pos := by
     simpa only [countEq] using normalized
   exact target_zero depth caller ref counter alias L frame base before start entry
 | succ n =>
   have fit : n+1<W := by have valid := value.word.isLt;omega
   have counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) caller.env=countValue (n+1) fit := by
     simpa only [countEq] using normalized
   by_cases enough : n<depth
   · obtain ⟨out,native,returned⟩ := AllocatingOuterZero.all_counts depth n caller fit ref counter alias
       L frame base before start entry enough
     rw [native] at source
     cases source
   · rw [source_short depth n caller fit ref counter alias (by omega)] at source
     cases source

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterClaims
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterClaims.decrement_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterClaims.decrement_zero
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterClaims.next_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterClaims.next_zero
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterClaims.source_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterClaims.source_zero
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterClaims.source_short' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterClaims.source_short
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterClaims.returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterClaims.returns

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterClaims.target_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterClaims.target_zero
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterClaims.bare_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterClaims.bare_revert
