import Solidity.Backend.InternalFlow.RuntimeFrameV3FullScalarLoop

/-! Typed partial horizons of the existing full-capture return loop. The
runtime bottom word and code image stay fixed. Remaining payload is real
memory history, not an assumed execution or a second trace semantics. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarPrefixes
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource FullScalarLoop

theorem returned_value {C : Contract} {R : RefTy} (σ : State C (Frame R)) (n steps : Nat)
 (fit : n+steps<W)
 (value : TEnv.get (.here : Idx (Frame R) (.val .uint)) σ.env=countValue n (by omega)) :
 TEnv.get (.here : Idx (Frame R) (.val .uint)) (returned σ n steps fit).env=countValue (n+steps) fit := by
 cases steps with
 | zero => simpa only [returned,if_pos rfl,Nat.add_zero] using value
 | succ steps => rfl

theorem at_horizon (steps frames n : Nat) (enough : steps≤frames)
 {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Frame R)}
 (σ : State C (Frame R)) (base : Nat → Fin W) (after : Machine)
 (repr : StateRepr L b frame F σ base after) (range : n+frames<W)
 (value : TEnv.get (.here : Idx (Frame R) (.val .uint)) σ.env=countValue n (by omega))
 (lo pointer bottom start : Nat) (locals : b+3≤lo) (pointerAbove : lo≤pointer) (pointerBelow : pointer<frame)
 (_payloadAbove : lo≤start) (payloadBelow : start+3*frames≤frame) (pointerBefore : pointer<start)
 (bottomAbove : b+3≤bottom) (bottomSeparate : bottom≠pointer) (fits : start+3*frames<W)
 (current : after.mem pointer=.val (wmod (start+3*frames)))
 (bottomValue : after.mem bottom=.val (wmod start))
 (saved : ∀ j,j<frames → after.mem (start+3*j)=after.mem b ∧
   after.mem (start+3*j+1)=.val (wmod (n+frames-j))) :
 ∃ last,
 loopIterN (run (condition pointer bottom)) (run (FullScalarUnwind.code (C:=C) b pointer F)) steps after=.inl last ∧
 StateRepr L b frame F (returned σ n steps (by omega)) base last ∧
 GrowsAllocator b frame 0 σ base after (returned σ n steps (by omega)) base last ∧
 last.stack=after.stack ∧ last.mem pointer=.val (wmod (start+3*(frames-steps))) ∧
 last.mem bottom=.val (wmod start) ∧ last.mem b=after.mem b ∧
 (∀ j,j<frames-steps → last.mem (start+3*j)=last.mem b ∧
   last.mem (start+3*j+1)=.val (wmod (n+frames-j))) ∧
 (∀ x,x≠pointer → x≠b → x≠b+1 → x≠b+2 → last.mem x=after.mem x) := by
 induction steps generalizing frames n σ after with
 | zero =>
   refine ⟨after,rfl,repr,?_,rfl,current,bottomValue,rfl,saved,?_⟩
   · intro cursor positive owned space
     simpa only [Nat.add_zero] using owned
   · intro x hp hr hc hv;rfl
 | succ steps ih =>
   cases frames with
   | zero => omega
   | succ frames =>
     have position : start+3*frames+3=start+3*(frames+1) := by omega
     have count : after.mem (start+3*frames+1)=.val (wmod (n+1)) := by
       simpa only [show n+(frames+1)-frames=n+1 from by omega] using (saved frames (by omega)).2
     obtain ⟨mid,body,represented,bodyStack,bodyCursor,bodyRef,bodyCount,bodyResult,bodyGrowth,bodyOutside⟩ :=
       FullScalarUnwind.step σ base after repr n (by omega) value lo pointer (start+3*frames)
         locals pointerAbove pointerBelow (by omega) (by omega) (by rw [position];exact fits)
         (by rw [position];exact current) (saved frames (by omega)).1 count
     let midSource := finished (σ.setLocal (.there .here) (countValue (n+1) (by omega))) (n+1) (by omega)
     have midRepr : StateRepr L b frame F midSource base mid := represented
     have tailSaved : ∀ j,j<frames → mid.mem (start+3*j)=mid.mem b ∧
         mid.mem (start+3*j+1)=.val (wmod ((n+1)+frames-j)) := by
       intro j small
       refine ⟨(bodyOutside _ (by omega) (by omega) (by omega) (by omega)).trans
         ((saved j (by omega)).1.trans bodyRef.symm),?_⟩
       have preserved := (bodyOutside (start+3*j+1) (by omega) (by omega) (by omega) (by omega)).trans (saved j (by omega)).2
       simpa only [show n+(frames+1)-j=(n+1)+frames-j from by omega] using preserved
     have nextBottom := (bodyOutside bottom bottomSeparate (by omega) (by omega) (by omega)).trans bottomValue
     obtain ⟨last,running,lastRepr,lastGrowth,stack,cursor,lastBottom,reference,history,exterior⟩ :=
       ih frames (n+1) (by omega) midSource mid midRepr (by omega) rfl (by omega) (by omega) bodyCursor nextBottom tailSaved
     have stateEq := returned_succ σ n steps (by omega)
     rw [stateEq] at lastRepr lastGrowth
     have turn := turn_more (C:=C) (R:=R) (b:=b) (F:=F) after mid current bottomValue fits body
     refine ⟨last,?_,lastRepr,?_,stack.trans bodyStack,?_,lastBottom,reference.trans bodyRef,?_,?_⟩
     · simpa only [loopIterN,turn] using running
     · simpa only [Nat.zero_add] using bodyGrowth.comp lastGrowth
     · simpa only [show frames+1-(steps+1)=frames-steps from by omega] using cursor
     · intro j small
       have known := history j (by omega)
       exact ⟨known.1,by simpa only [show (n+1)+frames-j=n+(frames+1)-j from by omega] using known.2⟩
     · intro x hp hr hc hv
       exact (exterior x hp hr hc hv).trans (bodyOutside x hp hr hc hv)

end Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarPrefixes

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarPrefixes.returned_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarPrefixes.returned_value

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarPrefixes.at_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarPrefixes.at_horizon
