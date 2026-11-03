import Solidity.Backend.InternalFlow.RuntimeFrameV3ParentRestore

/-! Typed states at every running prefix of the existing paired unwind.
Initial payload is explicit evidence; clients must derive it from actual capture.
No new iterator or recursive evaluator is defined. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ParentPrefixes
open Evm Evm.Memory RecursiveSource

def sourceAt {C : Contract} {R : RefTy} (σ : State C (Parameters R)) (n : Nat) (h : n<W) :=
 σ.withEnv (Δ:=Parameters R) (countValue n h,σ.env.2)

theorem running_prefix {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Parameters R)}
 (σ : State C (Parameters R)) (base : Nat → Fin W) (total steps frames : Nat)
 (enough : steps≤frames) (bounded : frames≤total) (bound : total<W)
 (after : Machine)
 (repr : StateRepr L b frame F (sourceAt σ (total-frames) (by omega)) base after)
 (lo pointer bottom start : Nat) (locals : b+2≤lo) (above : lo≤pointer)
 (below : pointer<frame) (_payload : lo≤start) (separate : pointer<start)
 (bottomAbove : b+2≤bottom) (_bottomBefore : bottom<start) (bottomSeparate : bottom≠pointer)
 (fits : start+2*frames<W)
 (current : after.mem pointer=.val (wmod (start+2*frames)))
 (bottomValue : after.mem bottom=.val (wmod start))
 (saved : ∀ j, j<frames → after.mem (start+2*j)=after.mem b ∧
   after.mem (start+2*j+1)=.val (wmod (total-j))) :
 ∃ last,
 loopIterN (run (PairedUnwind.condition pointer bottom))
   (run (Restore.restoreCells pointer (Restore.contextCells b (Parameters R)))) steps after=.inl last ∧
 StateRepr L b frame F (sourceAt σ (total-frames+steps) (by omega)) base last ∧
 last.stack=after.stack ∧ last.mem pointer=.val (wmod (start+2*(frames-steps))) ∧
 last.mem b=after.mem b ∧
 GrowsAllocator b frame 0 (sourceAt σ (total-frames) (by omega)) base after
   (sourceAt σ (total-frames+steps) (by omega)) base last ∧
 (∀ x, frame≤x → last.mem x=after.mem x) ∧
 (∀ x, x≠pointer → x≠b → x≠b+1 → last.mem x=after.mem x) := by
 induction steps generalizing frames after with
 | zero =>
   refine ⟨after,rfl,?_,rfl,?_,rfl,?_,?_,?_⟩
   · simpa only [Nat.add_zero] using repr
   · simpa only [Nat.sub_zero] using current
   · intro cursor positive ownership space
     simpa only [Nat.add_zero] using ownership
   · intro x high;rfl
   · intro x hp hr hc;rfl
 | succ steps ih =>
   cases frames with
   | zero => omega
   | succ frames =>
     have words := saved frames (by omega)
     obtain ⟨mid,executed,represented,stack,cursor,reference,counter,growth⟩ :=
       ParentRestore.restore _ base after repr (total-frames) (by omega) lo pointer
         (start+2*frames) locals above below (by omega) (by omega) (by omega)
         (by simpa only [show start+2*frames+2=start+2*(frames+1) from by omega] using current)
         words.1 words.2
     have nextRepr : StateRepr L b frame F (sourceAt σ (total-frames) (by omega)) base mid := represented
     let snapshot := writeMachine after (b+1) (.val (wmod (total-frames)))
     have payloadWords : ∀ i, i<(Parameters R).length →
         after.mem (start+2*frames+i)=snapshot.mem (b+i) := by
       intro i small
       change i<2 at small
       rcases (by omega : i=0 ∨ i=1) with rfl | rfl
       · simpa only [Nat.add_zero,snapshot,writeMachine,upd,if_neg (show b≠b+1 from by omega)] using words.1
       · simpa only [snapshot,writeMachine,upd,if_true] using words.2
     obtain ⟨other,also,recovered,values⟩ := Context.restore_context b (Parameters R) snapshot after
       lo pointer (start+2*frames) locals above (by omega) (.inl (by omega)) (by change start+2*frames+2<W; omega)
       (by simpa only [show (Parameters R).length=2 from rfl,
         show start+2*frames+2=start+2*(frames+1) from by omega] using current) payloadWords
     have same : other=mid := (Out.ok.inj (also.symm.trans executed)).1
     subst other
     have exterior : ∀ x, x≠pointer → x≠b → x≠b+1 → mid.mem x=after.mem x := by
       intro x notPointer notRef notCounter
       by_cases low : x<lo
       · have absent : x∉Restore.contextCells b (Parameters R) := by
           change x∉[b,b+1]
           simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
           exact ⟨notRef,notCounter⟩
         simpa only [if_neg absent] using recovered.locals x low
       · exact recovered.exterior x (by omega) notPointer
     have nextSaved : ∀ j, j<frames → mid.mem (start+2*j)=mid.mem b ∧
         mid.mem (start+2*j+1)=.val (wmod (total-j)) := by
       intro j small
       exact ⟨(exterior _ (by omega) (by omega) (by omega)).trans
         ((saved j (by omega)).1.trans reference.symm),
         (exterior _ (by omega) (by omega) (by omega)).trans (saved j (by omega)).2⟩
     have nextBottom : mid.mem bottom=.val (wmod start) :=
       (exterior bottom bottomSeparate (by omega) (by omega)).trans bottomValue
     have turn := PairedUnwind.turn_more after mid b pointer bottom start frames R current bottomValue fits executed
     obtain ⟨last,running,finalRepr,finalStack,finalCursor,finalRef,finalGrowth,finalExterior,finalOutside⟩ :=
       ih frames (by omega) (by omega) mid nextRepr (by omega) cursor nextBottom nextSaved
     have arithmetic : total-(frames+1)+(steps+1)=total-frames+steps := by omega
     refine ⟨last,?_,?_,finalStack.trans stack,?_,finalRef.trans reference,?_,?_,?_⟩
     · simpa only [loopIterN,turn] using running
     · simpa only [arithmetic] using finalRepr
     · simpa only [Nat.add_sub_add_right] using finalCursor
     · simpa only [Nat.add_zero,arithmetic] using growth.comp finalGrowth
     · intro x high
       exact (finalExterior x high).trans (exterior x (by omega) (by omega) (by omega))
     · intro x hp hr hc
       exact (finalOutside x hp hr hc).trans (exterior x hp hr hc)

namespace Checks
open CountdownWitness RecursiveActivation

def input := writeMachine AllocatorReturn.Checks.input 7 w[10]
theorem initial : StateRepr 1 2 16 F callee P.base input :=
 reserved_write AllocatorReturn.Checks.represented 7 (by decide) (by decide) w[10]
theorem ownership : StructAllocatorRepr callee.heap P.base 16 ⟨22,by decide⟩ input :=
 AllocatorReturn.Checks.ownership.localWrite 7 (by decide) (by decide) w[10]

/-- Every zero/one/two running horizon of the SAME actual descent/unwind
pair has its typed native parent and genuinely owned heap. -/
theorem horizons (n : Nat) (enough : n≤2) : ∃ down last addresses,
 run (descentCode (C:=P.C) 2 F 8) input=.ok down 0 ∧
 loopIterN (run (PairedUnwind.condition 8 7))
   (run (Restore.restoreCells 8 (Restore.contextCells 2 (Parameters A)))) n down=.inl last ∧
 StateRepr 1 2 16 F (sourceAt callee n (Nat.lt_of_le_of_lt enough (by decide))) addresses last ∧
 last.stack=[w[77]] ∧ last.mem 8=.val (wmod (10+2*(2-n))) ∧
 last.mem 2=w[16] ∧ last.mem 3=.val (wmod n) ∧
 StructAllocatorRepr callee.heap addresses 16 ⟨22,by decide⟩ last ∧
 [last.mem 16,last.mem 17,last.mem 18,last.mem 20,last.mem 21]=[w[2],w[7],w[9],w[1],w[4]] ∧
 [last.mem 0,last.mem 1,last.mem 7,last.mem 10,last.mem 11,last.mem 12,last.mem 13]=
 [w[22],w[16],w[10],w[16],w[2],w[16],w[1]] ∧
 last.mem 3≠.val (wmod (n+1)) := by
 obtain ⟨down,addresses,running,stopped,represented,stack,extended,growth,cursor⟩ :=
   RecursiveDescent.complete rfl 2 (by decide) callee P.r0 rfl rfl P.base input initial
     8 8 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl
 obtain ⟨history,exterior⟩ := RecursiveHistory.saved_history rfl 2 (by decide) callee P.r0 rfl rfl
   P.base input down initial 8 8 10 (by decide) (by decide) (by decide) (by decide)
   (by decide) (by decide) (by decide) rfl running
 have oldRef : down.mem 2=input.mem 2 := exterior 2 (by decide) (by decide) (.inl (by decide))
 have saved : ∀ j, j<2 → down.mem (10+2*j)=down.mem 2 ∧
     down.mem (10+2*j+1)=.val (wmod (2-j)) := by
   intro j small
   exact ⟨(history j small).1.trans oldRef.symm,(history j small).2⟩
 have bottom : down.mem 7=w[10] := (exterior 7 (by decide) (by decide) (.inl (by decide)))
 obtain ⟨last,unwinding,parentRepr,parentStack,parentCursor,parentRef,parentGrowth,parentExterior,parentOutside⟩ :=
   running_prefix callee addresses 2 n 2 enough (by decide) (by decide) down represented
     8 8 7 10 (by decide) (by decide) (by decide) (by decide) (by decide)
     (by decide) (by decide) (by decide) (by decide) cursor bottom saved
 simp only [Nat.sub_self,Nat.zero_add] at parentRepr parentGrowth
 have counter := RecursiveHistory.counter_word (sourceAt callee n (Nat.lt_of_le_of_lt enough (by decide))) n (Nat.lt_of_le_of_lt enough (by decide))
   rfl addresses last parentRepr
 have composed := growth.comp parentGrowth
 have owned := composed ⟨22,by decide⟩ (by decide) ownership (by decide)
 have high : ∀ x,16≤x → last.mem x=input.mem x := by
   intro x bound
   exact (parentExterior x bound).trans (exterior x (by omega) (by omega) (.inr (by omega)))
 refine ⟨down,last,addresses,RecursiveDescent.run_of_stopped stopped,unwinding,parentRepr,
   parentStack.trans stack,parentCursor,parentRef.trans oldRef,counter,owned,?_,?_,?_⟩
 · rw [high 16 (by decide),high 17 (by decide),high 18 (by decide),high 20 (by decide),high 21 (by decide)]
   rfl
 · have low : ∀ x, x<10 → x≠2 → x≠3 → x≠8 → last.mem x=input.mem x := by
     intro x hx hr hc hp
     exact (parentOutside x hp hr hc).trans (exterior x hp hc (.inl hx))
   have a := history 0 (by decide)
   have z := history 1 (by decide)
   rw [low 0 (by decide) (by decide) (by decide) (by decide),
     low 1 (by decide) (by decide) (by decide) (by decide),
     low 7 (by decide) (by decide) (by decide) (by decide),
     parentOutside 10 (by decide) (by decide) (by decide),
     parentOutside 11 (by decide) (by decide) (by decide),
     parentOutside 12 (by decide) (by decide) (by decide),
     parentOutside 13 (by decide) (by decide) (by decide),a.1,a.2,z.1,z.2]
   rfl
 · rw [counter]
   intro same
   have word := congrArg (fun w : Word => match w with | .val v => v.val | _ => 0) same
   change n%W=(n+1)%W at word
   rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt enough (by decide)),
     Nat.mod_eq_of_lt (show n+1<W from Nat.lt_of_le_of_lt (show n+1≤3 from by omega) (by decide))] at word
   omega

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.ParentPrefixes

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ParentPrefixes.running_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ParentPrefixes.running_prefix
