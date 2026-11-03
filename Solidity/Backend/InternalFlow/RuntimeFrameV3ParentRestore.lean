import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatorReturn

/-! One actual parent restore with typed representation and allocator transport.
Saved payload words are execution evidence; no resulting representation or run
is a premise. This is the countdown parent leaf, not general recursive bodies. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ParentRestore
open Evm Evm.Memory RecursiveSource

theorem restore {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Parameters R)}
 (σ : State C (Parameters R)) (base : Nat → Fin W) (after : Machine)
 (repr : StateRepr L b frame F σ base after)
 (parent : Nat) (bound : parent<W) (lo pointer start : Nat)
 (locals : b+2≤lo) (above : lo≤pointer) (below : pointer<frame)
 (payload : lo≤start) (separate : pointer<start) (fits : start+2<W)
 (current : after.mem pointer=.val (wmod (start+2)))
 (reference : after.mem start=after.mem b)
 (counter : after.mem (start+1)=.val (wmod parent)) :
 ∃ last,
 run (Restore.restoreCells pointer (Restore.contextCells b (Parameters R))) after=.ok last 0 ∧
 StateRepr L b frame F (σ.setLocal .here (countValue parent bound)) base last ∧
 last.stack=after.stack ∧ last.mem pointer=.val (wmod start) ∧
 last.mem b=after.mem b ∧ last.mem (b+1)=.val (wmod parent) ∧
 GrowsAllocator b frame 0 σ base after (σ.setLocal .here (countValue parent bound)) base last := by
 let snapshot := writeMachine after (b+1) (.val (wmod parent))
 have model : StateRepr L b frame F (σ.setLocal .here (countValue parent bound)) base snapshot :=
   repr.setVal .here (countValue parent bound) (.val (wmod parent)) (by
     have word : wmod parent=(⟨parent,bound⟩ : Fin W) := Fin.ext (Nat.mod_eq_of_lt bound)
     rw [word]
     exact ReprV.uint_of rfl)
 have saved : ∀ i, i<(Parameters R).length → after.mem (start+i)=snapshot.mem (b+i) := by
   intro i small
   change i<2 at small
   rcases (by omega : i=0 ∨ i=1) with rfl | rfl
   · simpa only [Nat.add_zero,snapshot,writeMachine,upd,if_neg (show b≠b+1 from by omega)] using reference
   · simpa only [snapshot,writeMachine,upd,if_true] using counter
 obtain ⟨last,executed,recovered,values⟩ := Context.restore_context b (Parameters R) snapshot after
   lo pointer start locals above payload (.inl separate) fits current saved
 have heap : ∀ x, frame≤x → last.mem x=snapshot.mem x := by
   intro x high
   exact (recovered.exterior x (by omega) (by omega)).trans
     (upd_other _ _ (by omega)).symm
 have transported := (Restored.memory_transport model last.mem (fun i _ => values i) heap).stack last.stack
 have reset := congrArg (fun m : Machine => {m with mem:=last.mem,stack:=last.stack}) recovered.fields
 change last={after with mem:=last.mem,stack:=last.stack} at reset
 change StateRepr L b frame F (σ.setLocal .here (countValue parent bound)) base
   {after with mem:=last.mem,stack:=last.stack} at transported
 rw [←reset] at transported
 have oldRef := values (.there .here : Idx (Parameters R) (.mem R))
 have oldCounter := values (.here : Idx (Parameters R) (.val .uint))
 change last.mem b=snapshot.mem b at oldRef
 change last.mem (b+1)=snapshot.mem (b+1) at oldCounter
 refine ⟨last,executed,transported,recovered.stack,recovered.cursor,?_,?_,?_⟩
 · simpa only [snapshot,writeMachine,upd,if_neg (show b≠b+1 from by omega)] using oldRef
 · simpa only [snapshot,writeMachine,upd,if_true] using oldCounter
 · intro cursor positive initial space
   have ownership := recovered.allocator σ.heap base frame cursor (by
     intro x member
     change x∈[b,b+1] at member
     simp only [List.mem_cons,List.not_mem_nil,or_false] at member
     rcases member with rfl | rfl <;> constructor <;> omega) (by omega) below initial
   simpa only [Nat.add_zero] using ownership

namespace Checks
open CountdownWitness RecursiveActivation
abbrev input := AllocatorReturn.Checks.input

/-- Actual checked descent supplies both the child representation and the
nearest-parent payload. No concrete trace normalization or midpoint oracle. -/
theorem parent : ∃ down last addresses,
 run (descentCode (C:=P.C) 2 F 8) input=.ok down 0 ∧
 run (Restore.restoreCells 8 (Restore.contextCells 2 (Parameters A))) down=.ok last 0 ∧
 StateRepr 1 2 16 F ((callee.withEnv (Δ:=Parameters A) (countValue 0 W_pos,(some P.r0,()))).setLocal .here
   (countValue 1 (by decide))) addresses last ∧
 last.stack=[w[77]] ∧ last.mem 8=w[12] ∧ last.mem 2=w[16] ∧ last.mem 3=w[1] ∧
 StructAllocatorRepr callee.heap addresses 16 ⟨22,by decide⟩ last ∧
 last.mem 3≠w[2] ∧ last.mem 2≠w[20] := by
 obtain ⟨down,addresses,running,stopped,represented,stack,extended,growth,cursor⟩ :=
   RecursiveDescent.complete rfl 2 (by decide) callee P.r0 rfl rfl P.base input
     AllocatorReturn.Checks.represented 8 8 10 (by decide) (by decide) (by decide)
     (by decide) (by decide) (by decide) (by decide) rfl
 obtain ⟨history,exterior⟩ := RecursiveHistory.saved_history rfl 2 (by decide) callee P.r0 rfl rfl
   P.base input down AllocatorReturn.Checks.represented 8 8 10 (by decide) (by decide)
   (by decide) (by decide) (by decide) (by decide) (by decide) rfl running
 have oldRef : down.mem 2=input.mem 2 := exterior 2 (by decide) (by decide) (.inl (by decide))
 have saved := history 1 (by decide)
 obtain ⟨last,returned,parentRepr,parentStack,parentCursor,parentRef,parentCounter,parentGrowth⟩ :=
   restore _ addresses down represented 1 (by decide) 8 8 12 (by decide) (by decide)
     (by decide) (by decide) (by decide) (by decide) cursor
     (saved.1.trans oldRef.symm) saved.2
 have composed := growth.comp parentGrowth
 have owned := composed ⟨22,by decide⟩ (by decide) AllocatorReturn.Checks.ownership (by decide)
 refine ⟨down,last,addresses,RecursiveDescent.run_of_stopped stopped,returned,parentRepr,
   parentStack.trans stack,parentCursor,parentRef.trans oldRef,parentCounter,owned,?_,?_⟩
 · rw [parentCounter];decide
 · have word : last.mem 2=w[16] := parentRef.trans oldRef
   rw [word];decide

/-- The nearest-parent source state is reached by the actual native
activation prefix, not chosen solely to fit the restored target words. -/
theorem source_parent :
 (.cons (.assignLocal .here decrement) .nil : Prog P.C (Parameters A) (Parameters A)).run callee=
 .ok ⟨(callee.withEnv (Δ:=Parameters A) (countValue 0 W_pos,(some P.r0,()))).setLocal .here
   (countValue 1 (by decide)),List.prefix_refl _⟩ :=
 (source_activation rfl callee 1 (by decide) P.r0 rfl rfl).2

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.ParentRestore

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ParentRestore.Checks.parent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ParentRestore.Checks.parent
