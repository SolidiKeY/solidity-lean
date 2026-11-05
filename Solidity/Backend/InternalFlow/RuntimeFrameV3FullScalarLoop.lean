import Solidity.Backend.InternalFlow.RuntimeFrameV3FullScalarUnwind
import Solidity.Backend.InternalFlow.RuntimeFrameV3PairedUnwind

/-! Arbitrary finite full-capture returns on the existing target loop semantics.
The code image is independent of frame count. Saved payload, representation,
scalar range and physical frame/no-wrap bounds remain actual premises. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarLoop
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
abbrev condition := RecursiveUnwind.condition

def code {C : Contract} {R : RefTy} (b pointer bottom : Nat) (F : Frag (Frame R)) : List Instr :=
 [.loop (condition pointer bottom) (FullScalarUnwind.code (C:=C) b pointer F)]

/-- Only the final typed local update, not a new source evaluator. -/
def returned {C : Contract} {R : RefTy} (σ : State C (Frame R)) (n frames : Nat) (fit : n+frames<W) :=
 if frames=0 then σ else finished (σ.setLocal (.there .here) (countValue (n+frames) fit)) (n+frames) fit

theorem returned_succ {C : Contract} {R : RefTy} (σ : State C (Frame R)) (n frames : Nat)
 (fit : n+(frames+1)<W) :
 returned (finished (σ.setLocal (.there .here) (countValue (n+1) (by omega))) (n+1) (by omega))
   (n+1) frames (by omega)=returned σ n (frames+1) fit := by
 cases frames with
 | zero => rfl
 | succ k =>
   have values : countValue ((n+1)+(k+1)) (by omega)=countValue (n+(k+1+1)) fit := by
     apply Subtype.ext
     change (((n+1)+(k+1):Nat):Int)=((n+(k+1+1):Nat):Int)
     omega
   change σ.withEnv (Δ:=Frame R) (countValue ((n+1)+(k+1)) (by omega),
     (countValue ((n+1)+(k+1)) (by omega),σ.env.2.2))=
     σ.withEnv (Δ:=Frame R) (countValue (n+(k+1+1)) fit,(countValue (n+(k+1+1)) fit,σ.env.2.2))
   rw [values]

theorem turn_more {C : Contract} {R : RefTy} {b pointer bottom start frames : Nat} {F : Frag (Frame R)}
 (m next : Machine) (current : m.mem pointer=.val (wmod (start+3*(frames+1))))
 (bottomValue : m.mem bottom=.val (wmod start)) (fits : start+3*(frames+1)<W)
 (body : run (FullScalarUnwind.code (C:=C) b pointer F) m=.ok next 0) :
 loopTurn (run (condition pointer bottom)) (run (FullScalarUnwind.code (C:=C) b pointer F)) m=.inl next := by
 have guard := RecursiveUnwind.condition_run m pointer bottom (wmod (start+3*(frames+1))) (wmod start) current bottomValue
 have different : (wmod (start+3*(frames+1))).val≠(wmod start).val := by
   change (start+3*(frames+1))%W≠start%W
   rw [Nat.mod_eq_of_lt fits,Nat.mod_eq_of_lt (show start<W by omega)]
   omega
 simp only [loopTurn,guard,decide_eq_true different,Machine.push,bword,if_true,if_false,Nat.one_ne_zero,body]

theorem turn_done {C : Contract} {R : RefTy} {b pointer bottom start : Nat} {F : Frag (Frame R)}
 (m : Machine) (current : m.mem pointer=.val (wmod start))
 (bottomValue : m.mem bottom=.val (wmod start)) :
 loopTurn (run (condition pointer bottom)) (run (FullScalarUnwind.code (C:=C) b pointer F)) m=.inr (.ok m 0) := by
 have guard := RecursiveUnwind.condition_run m pointer bottom (wmod start) (wmod start) current bottomValue
 simp only [loopTurn,guard,ne_eq,not_true_eq_false,decide_false,Machine.push,bword,
   Bool.false_eq_true,if_false,if_true]

theorem iter (frames n : Nat) {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Frame R)}
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
 loopIterN (run (condition pointer bottom)) (run (FullScalarUnwind.code (C:=C) b pointer F)) frames after=.inl last ∧
 loopIterN (run (condition pointer bottom)) (run (FullScalarUnwind.code (C:=C) b pointer F)) (frames+1) after=.inr (.ok last 0) ∧
 StateRepr L b frame F (returned σ n frames range) base last ∧
 GrowsAllocator b frame 0 σ base after (returned σ n frames range) base last ∧
 last.stack=after.stack ∧ last.mem pointer=.val (wmod start) ∧ last.mem b=after.mem b ∧
 (∀ x,x≠pointer → x≠b → x≠b+1 → x≠b+2 → last.mem x=after.mem x) := by
 induction frames generalizing n σ after with
 | zero =>
   have position : after.mem pointer=.val (wmod start) := by
     simpa only [Nat.mul_zero,Nat.add_zero] using current
   have stopped := turn_done (C:=C) (R:=R) (b:=b) (F:=F) after position bottomValue
   refine ⟨after,rfl,?_,repr,?_,rfl,position,rfl,?_⟩
   · simp only [loopIterN,stopped]
   · intro cursor positive owned space
     simpa only [Nat.add_zero] using owned
   · intro x hp hr hc hv;rfl
 | succ frames ih =>
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
   obtain ⟨last,running,stopped,lastRepr,lastGrowth,stack,cursor,reference,exterior⟩ :=
     ih (n+1) midSource mid midRepr (by omega) rfl (by omega) (by omega) bodyCursor nextBottom tailSaved
   have stateEq := returned_succ σ n frames range
   rw [stateEq] at lastRepr lastGrowth
   have turn := turn_more (C:=C) (R:=R) (b:=b) (F:=F) after mid current bottomValue fits body
   refine ⟨last,?_,?_,lastRepr,?_,stack.trans bodyStack,cursor,reference.trans bodyRef,?_⟩
   · simpa only [loopIterN,turn] using running
   · simpa only [loopIterN,turn] using stopped
   · simpa only [Nat.zero_add] using bodyGrowth.comp lastGrowth
   · intro x hp hr hc hv
     exact (exterior x hp hr hc hv).trans (bodyOutside x hp hr hc hv)

theorem run_of_stopped {C : Contract} {R : RefTy} {b pointer bottom horizon : Nat} {F : Frag (Frame R)}
 {before after : Machine}
 (stopped : loopIterN (run (condition pointer bottom)) (run (FullScalarUnwind.code (C:=C) b pointer F))
   horizon before=.inr (.ok after 0)) : run (code (C:=C) b pointer bottom F) before=.ok after 0 := by
 have done := loopRun_of_iterN stopped
 change loopRun (fun m => exec (condition pointer bottom) 0 m)
   (fun m => exec (FullScalarUnwind.code (C:=C) b pointer F) 0 m) before=.ok after 0 at done
 simp only [code,run,exec_cons_zero,Instr.step,done,Out.ok_bind,exec_nil]

end Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarLoop

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarLoop.returned_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarLoop.returned_succ

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarLoop.turn_more' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarLoop.turn_more

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarLoop.turn_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarLoop.turn_done

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarLoop.iter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarLoop.iter

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarLoop.run_of_stopped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.FullScalarLoop.run_of_stopped
