import Solidity.Backend.InternalFlow.RuntimeFrameV3FullScalarUnwind

/-! Actual scalar call return from a full three-cell capture, without the
recursive body's following increment. The saved and active reference must
agree. This does not restore an arbitrary different parent reference. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.OuterScalarRestore
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

def code {R : RefTy} (b pointer : Nat) : List Instr :=
 FullScalarUnwind.skipCode pointer ++ Restore.restoreCells pointer (Restore.contextCells b (Parameters R))

theorem step {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Frame R)}
 (σ : State C (Frame R)) (base : Nat → Fin W) (after : Machine)
 (repr : StateRepr L b frame F σ base after) (parent : Nat) (bound : parent<W)
 (lo pointer start : Nat) (locals : b+3≤lo) (above : lo≤pointer) (below : pointer<frame)
 (payload : lo≤start) (separate : pointer<start) (fits : start+3<W)
 (current : after.mem pointer=.val (wmod (start+3)))
 (reference : after.mem start=after.mem b) (counter : after.mem (start+1)=.val (wmod parent)) :
 ∃ last,
 run (code (R:=R) b pointer) after=.ok last 0 ∧
 StateRepr L b frame F (σ.setLocal (.there .here) (countValue parent bound)) base last ∧
 last.stack=after.stack ∧ last.mem pointer=.val (wmod start) ∧ last.mem b=after.mem b ∧
 last.mem (b+1)=.val (wmod parent) ∧ last.mem (b+2)=after.mem (b+2) ∧
 GrowsAllocator b frame 0 σ base after (σ.setLocal (.there .here) (countValue parent bound)) base last ∧
 (∀ x,x≠pointer → x≠b → x≠b+1 → last.mem x=after.mem x) := by
 have skipRun := FullScalarUnwind.skip_run after pointer start fits current
 let skipped := FullScalarUnwind.skipped after pointer start
 have skipRepr : StateRepr L b frame F σ base skipped :=
   reserved_write repr pointer (by change b+3≤pointer;omega) below (.val (wmod (start+2)))
 have skipGrowth : GrowsAllocator b frame 0 σ base after σ base skipped := by
   intro cursor positive owner space
   simpa only [Nat.add_zero] using owner.localWrite pointer (by omega) below (.val (wmod (start+2)))
 have skipOutside (x : Nat) (different : x≠pointer) : skipped.mem x=after.mem x := upd_other _ _ different
 have sameRef : skipped.mem start=skipped.mem b := by
   rw [skipOutside start (by omega),skipOutside b (by omega)]
   exact reference
 have sameCounter : skipped.mem (start+1)=.val (wmod parent) := (skipOutside _ (by omega)).trans counter
 obtain ⟨last,actual,represented,stack,position,refWord,countWord,resultWord,growth,outside⟩ :=
   ScalarParentRestore.restore σ base skipped skipRepr parent bound lo pointer start locals above below payload separate
     (by omega) (upd_same _ _ _) sameRef sameCounter
 refine ⟨last,(run_append_ok skipRun).trans actual,represented,stack,position,refWord.trans (skipOutside b (by omega)),
   countWord,resultWord.trans (skipOutside (b+2) (by omega)),?_,?_⟩
 · simpa only [Nat.zero_add] using skipGrowth.comp growth
 · intro x hp hr hc
   exact (outside x hp hr hc).trans (skipOutside x hp)

end Solidity.Backend.InternalFlow.RuntimeFrame.OuterScalarRestore
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.OuterScalarRestore.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.OuterScalarRestore.step
