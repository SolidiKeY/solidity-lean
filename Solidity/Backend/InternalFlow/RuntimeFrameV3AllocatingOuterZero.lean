import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingOuterPlan

/-! Actual zero-allocation outer return with no allocator-ownership premise.
Both inner loops stop at their actual guards. Heap growth is zero; the caller
representation and older words are transported through actual capture/restore.
This does not establish general compiler or approved-profile closure. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterZero
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource ScalarAllocatingDescent

theorem endpoint {L frame : Nat} (depth start : Nat) (σ : State C (Frame A))
 (ref : HRef σ.H A)
 (counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) σ.env=countValue 1 (by decide))
 (alias : TEnv.get (.there (.there .here) : Idx (Frame A) (.mem A)) σ.env=some ref)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L 2 frame F σ base before)
 (startAbove : 9≤start) (room : start+3≤frame) (payloadFit : start+3<W)
 (current : before.mem 8=.val (wmod start)) :
 ∃ (out : Solidity.Out C σ.H (Frame A)) (last : Machine) (addresses : Nat → Fin W),
 (AllocatingOuterFamily.source (depth+1)).run σ=.ok out ∧ run AllocatingOuterFamily.image before=.ok last 0 ∧
 StateRepr L 2 frame F out.st addresses last ∧ last.stack=before.stack ∧
 last.mem 8=.val (wmod start) ∧ last.mem 2=.val (base ref.id) ∧
 last.mem 3=w[1] ∧ last.mem 4=w[0] ∧ last.mem 0=before.mem 0 ∧ BaseExtends σ.H base addresses ∧
 GrowsAllocator 2 frame 0 σ base before out.st addresses last ∧ Footprint.Words 8 start before last := by
 have fit : 0+1<W := by decide
 obtain ⟨saved,savedRun,captured,savedRepr,captureGrowth⟩ :=
   Context.capture_context (σ:=σ) (F:=F) (base:=base) before 8 8 start repr
     (by decide) (by decide) (by omega) (by omega) (by change start+3≤frame;omega) (.inl (by omega)) (by change start+3<W;omega) current
 have entry := AllocatingScalarEntry.entry (by rfl) σ 0 fit ref counter alias base saved savedRepr
 let child := entered σ 0 (by omega) ref
 let active := AllocatingScalarEntry.childMachine (R:=A) 2 saved 0 (by omega)
 let prepared := writeMachine active 7 (.val (wmod (start+3)))
 have savedPointer : saved.mem 8=.val (wmod (start+3)) := captured.cursor
 have activePointer : active.mem 8=.val (wmod (start+3)) := savedPointer
 have preparedRun : run [.mload 8,.mstore 7] active=.ok prepared 0 := by
   change Out.ok (writeMachine active 7 (active.mem 8)) 0=_
   rw [activePointer]
 have preparedRepr : StateRepr L 2 frame F child base prepared :=
   reserved_write entry.2.1 7 (by decide) (by omega) (.val (wmod (start+3)))
 let bodyOut : Solidity.Out C child.H (Frame A) := ⟨child,List.prefix_refl _⟩
 let after := prepared
 let addresses := base
 have bodySource : (AllocatingScalarSource.body A (by rfl) (depth+1)).run child=.ok bodyOut :=
   AllocatingScalarSource.source_zero (by rfl) child depth rfl
 have downTurn := zero_turn child rfl base prepared preparedRepr 8
 have downRun : run [.loop guardCompiled.code (AllocatingScalarTurn.code 8)] prepared=.ok prepared 0 :=
   GuardedRecursion.successful_loop _ _ prepared prepared 1 (by simp only [loopIterN,downTurn])
 have upTurn := FullScalarLoop.turn_done (C:=C) (R:=A) (b:=2) (F:=F) prepared
   (show prepared.mem 8=.val (wmod (start+3)) from activePointer) (show prepared.mem 7=.val (wmod (start+3)) from rfl)
 have upRun : run (FullScalarLoop.code (C:=C) 2 8 7 F) prepared=.ok prepared 0 :=
   FullScalarLoop.run_of_stopped (horizon:=1) (by simp only [loopIterN,upTurn])
 have bodyRun : run (ScalarPairedTransport.image guardCompiled 8 7) prepared=.ok after 0 :=
   (run_append_ok downRun).trans upRun
 have bodyRepr : StateRepr L 2 frame F bodyOut.st addresses after := preparedRepr
 have extended : BaseExtends child.H base addresses := BaseExtends.refl base
 have bodyGrowth : GrowsAllocator 2 frame 0 child base prepared bodyOut.st addresses after := by
   intro point positive owner capacity
   simpa only [Nat.add_zero] using owner
 have bodyStack : after.stack=prepared.stack := rfl
 have bodyPointer : after.mem 8=.val (wmod (start+3)) := activePointer
 have bodyRef : after.mem 2=.val (base ref.id) := by
   obtain ⟨actual,binding,word⟩ := preparedRepr.pointers (.there (.there .here) : Idx (Frame A) (.mem A))
   have same : actual=ref := Option.some.inj binding.symm
   subst actual
   exact word
 have bodyWords : ∀ x,6≤x → x<frame → x≠8 → (x<start+3 ∨ start+3+3*0≤x) → after.mem x=prepared.mem x := by
   intros;rfl
 have savedRef : saved.mem start=.val (base ref.id) := by
   have observed := repr.pointers (.there (.there .here) : Idx (Frame A) (.mem A))
   obtain ⟨r,binding,word⟩ := observed
   have same : r=ref := Option.some.inj (binding.symm.trans alias)
   subst r
   have savedWord : saved.mem start=before.mem 2 := by
     simpa only [Restore.contextCells,List.getElem_map,List.getElem_range] using captured.payload 0 (by decide)
   exact savedWord.trans word
 have savedCount : saved.mem (start+1)=.val (wmod (0+1)) := by
   have word := repr.core.vals (.there .here : Idx (Frame A) (.val .uint))
   change ReprV .uint (TEnv.get (.there .here : Idx (Frame A) (.val .uint)) σ.env) (before.mem 3) at word
   rw [counter] at word
   have actual := Restore.uint_unique word (ReprV.uint_of rfl)
   have savedWord : saved.mem (start+1)=before.mem 3 := by
     simpa only [Restore.contextCells,List.getElem_map,List.getElem_range] using captured.payload 1 (by decide)
   exact savedWord.trans
     (actual.trans (congrArg Word.val (Fin.ext (Nat.mod_eq_of_lt fit).symm)))
 have payloadRef : after.mem start=.val (base ref.id) :=
   (bodyWords start (by omega) (by omega) (by omega) (.inl (by omega))).trans (show prepared.mem start=saved.mem start from by
     change (if start=7 then _ else if start=4 then _ else if start=3 then _ else _) = _
     simp only [if_neg (show start≠7 from by omega),if_neg (show start≠4 from by omega),if_neg (show start≠3 from by omega)]) |>.trans savedRef
 have payloadCount : after.mem (start+1)=.val (wmod (0+1)) :=
   (bodyWords (start+1) (by omega) (by omega) (by omega) (.inl (by omega))).trans (show prepared.mem (start+1)=saved.mem (start+1) from by
     change (if start+1=7 then _ else if start+1=4 then _ else if start+1=3 then _ else _) = _
     simp only [if_neg (show start+1≠7 from by omega),if_neg (show start+1≠4 from by omega),if_neg (show start+1≠3 from by omega)]) |>.trans savedCount
 obtain ⟨last,restoreRun,restored,lastStack,lastPointer,lastRef,lastCount,lastResult,restoreGrowth,outside⟩ :=
   OuterScalarRestore.step bodyOut.st addresses after bodyRepr (0+1) fit 8 8 start
     (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) bodyPointer
     (payloadRef.trans bodyRef.symm) payloadCount
 let arguments : TEnv C σ.H (Parameters A) := (countValue 0 (by omega),(some ref,()))
 let out := exported (result A) Ext.refl σ arguments bodyOut
 have native : (AllocatingOuterFamily.source (depth+1)).run σ=.ok out := by
   change TRun.call (next A (by rfl)) (result A) (AllocatingScalarSource.body A (by rfl) (depth+1)).ext
     (AllocatingScalarSource.body A (by rfl) (depth+1)).runR σ=_
   have scope : (AllocatingScalarSource.body (C:=C) A (by rfl) (depth+1)).ext=Ext.refl := Subsingleton.elim _ _
   rw [scope]
   exact call_return (next A (by rfl)) (result A) .refl _ σ arguments entry.2.2.1 bodyOut bodySource
 obtain ⟨seen,seenRun,_,locals,_⟩ := AllocatingScalarSource.success (by rfl) (depth+1) child 0 (by omega) ref rfl rfl (by omega)
 have sameOut : seen=bodyOut := Except.ok.inj (seenRun.symm.trans bodySource)
 subst seen
 have callerEnv : σ.env=(σ.env.1,(countValue (0+1) fit,(some ref,()))) :=
   Prod.ext rfl (Prod.ext counter (Prod.ext alias (by cases σ.env.2.2.2;rfl)))
 have stateEq : bodyOut.st.setLocal (.there .here) (countValue (0+1) fit)=out.st := by
   change bodyOut.st.withEnv (TEnv.set (.there .here) (countValue (0+1) fit) bodyOut.st.env)=_
   rw [locals]
   simp only [out,exported,result,CallRet.leaveT,CallRet.enterT,TEnv.drop,TEnv.take]
   rw [callerEnv,locals]
   rfl
 rw [stateEq] at restored restoreGrowth
 have actual : run AllocatingOuterFamily.image before=.ok last 0 :=
   (run_append_ok ((run_append_ok ((run_append_ok savedRun).trans entry.1)).trans preparedRun)).trans
     ((run_append_ok bodyRun).trans restoreRun)
 have scalar : after.mem 4=.val (wmod 0) := by
   have represented := bodyRepr.core.vals (.here : Idx (Frame A) (.val .uint))
   change ReprV .uint (TEnv.get (.here : Idx (Frame A) (.val .uint)) bodyOut.st.env) (after.mem 4) at represented
   rw [locals] at represented
   exact (Restore.uint_unique represented (ReprV.uint_of rfl)).trans
     (congrArg Word.val (Fin.ext (Nat.mod_eq_of_lt (by omega : 0<W)).symm))
 have entryGrowth : GrowsAllocator 2 frame 0 σ base saved child base prepared := by
   intro point positive owner capacity
   simpa only [Nat.add_zero] using
     (((owner.localWrite 3 (by omega) (by omega) (.val ⟨0,by omega⟩)).localWrite 4
       (by omega) (by omega) w[0]).localWrite 7 (by omega) (by omega) (.val (wmod (start+3))))
 have total : GrowsAllocator 2 frame (4*0) σ base before out.st addresses last := by
   simpa only [Nat.zero_add,Nat.add_zero] using (captureGrowth.comp entryGrowth).comp (bodyGrowth.comp restoreGrowth)
 have olderWords : Footprint.Words 8 start before last := by
   intro x lower upper
   by_cases pointer : x=8
   · subst x
     exact lastPointer.trans current.symm
   · have preparedWord : prepared.mem x=saved.mem x := by
       change (if x=7 then _ else if x=4 then _ else if x=3 then _ else _) = _
       simp only [if_neg (show x≠7 from by omega),if_neg (show x≠4 from by omega),if_neg (show x≠3 from by omega)]
     exact (outside x pointer (by omega) (by omega)).trans
       ((bodyWords x (by omega) (by omega) pointer (.inl (by omega))).trans
         (preparedWord.trans (captured.exterior x pointer (.inl upper))))

 have cursorCell : last.mem 0=before.mem 0 :=
   (outside 0 (by decide) (by decide) (by decide)).trans
     ((show prepared.mem 0=saved.mem 0 from rfl).trans (captured.exterior 0 (by decide) (.inl (by omega))))
 exact ⟨out,last,addresses,native,actual,restored,lastStack.trans (bodyStack.trans captured.stack),lastPointer,
   lastRef.trans bodyRef,lastCount,lastResult.trans scalar,cursorCell,extended,total,olderWords⟩

theorem return_from_entry (depth : Nat) (caller : State C (Frame A)) (ref : HRef caller.H A)
 (counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) caller.env=countValue 1 (by decide))
 (alias : TEnv.get (.there (.there .here) : Idx (Frame A) (.mem A)) caller.env=some ref)
 (L frame : Nat) (base : Nat → Fin W) (before : Machine) (start : Nat)
 (entry : InterfaceV1.Entry (AllocatingOuterPlan.plan.at (depth+1)) L 2 frame F caller base before start) :
 ∃ out, (AllocatingOuterFamily.source (depth+1)).run caller=.ok out ∧
 InterfaceV1.Returned (AllocatingOuterPlan.plan.at (depth+1)) L 2 frame caller base before start out := by
 have demandEq := AllocatingOuterPlan.demand_value caller 0 (by decide) ref counter alias
 have reserve : start+max 4 (3+3*0)≤frame := by
   simpa only [AllocatingOuterPlan.plan,InterfaceV1.RecursiveEmission.at,demandEq] using entry.reserve
 have noWrap : start+max 4 (3+3*0)<W := by
   simpa only [AllocatingOuterPlan.plan,InterfaceV1.RecursiveEmission.at,demandEq] using entry.noWrap
 have above : 8≤start := entry.payloadAbove
 have separated : 8<start ∨ start+max 4 (3+3*0)≤8 := by
   simpa only [AllocatingOuterPlan.plan,InterfaceV1.RecursiveEmission.at,demandEq] using entry.separate
 have startAbove : 9≤start := by omega
 obtain ⟨out,last,addresses,native,actual,represented,stack,position,reference,countWord,resultWord,cursorCell,extended,growth,olderWords⟩ :=
   endpoint depth start caller ref counter alias base before entry.represented startAbove (by omega) (by omega) entry.cursor
 refine ⟨out,native,last,addresses,actual,represented,stack,extended,?_,position,olderWords⟩
 simpa only [AllocatingOuterPlan.plan,InterfaceV1.RecursiveEmission.at,demandEq,Nat.mul_zero] using growth

/-- All non-wrapped counts, including zero, now use the same state-indexed
plan. Wrapped top-level subtraction, universal ReturnClaim and profiles remain
separate obligations. No pending producer is inhabited here. -/
theorem all_counts (depth n : Nat) (caller : State C (Frame A))
 (fit : n+1<W) (ref : HRef caller.H A)
 (counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) caller.env=countValue (n+1) fit)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame A) (.mem A)) caller.env=some ref)
 (L frame : Nat) (base : Nat → Fin W) (before : Machine) (start : Nat)
 (entry : InterfaceV1.Entry (AllocatingOuterPlan.plan.at depth) L 2 frame F caller base before start)
 (enough : n<depth) :
 ∃ out, (AllocatingOuterFamily.source depth).run caller=.ok out ∧
 InterfaceV1.Returned (AllocatingOuterPlan.plan.at depth) L 2 frame caller base before start out := by
 cases n with
 | zero =>
   cases depth with
   | zero => omega
   | succ depth => exact return_from_entry depth caller ref counter alias L frame base before start entry
 | succ n =>
   exact AllocatingOuterPlan.return_from_entry depth (n+1) (by omega) caller fit ref counter alias L frame base before start entry enough

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterZero
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterZero.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterZero.endpoint

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterZero.return_from_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterZero.return_from_entry
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterZero.all_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterZero.all_counts
