import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarReentry

/-! Actual target re-entry after caller heap growth. The checked argument
reads the mutated object. Older and newly allocated objects are preserved by
the real second endpoint and allocator laws, not a global keeps premise. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarReentry.Endpoint
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
open DisjointScalarReturn.Client
noncomputable abbrev input := ScalarContinuation.target
abbrev origin := ScalarContinuation.final
noncomputable abbrev initialBase := ScalarContinuation.finalBase
abbrev resultState := origin.setLocal (.here : Idx Γ (.val .uint)) (countValue 3 (by decide))

theorem available : ∃ after addresses,
 run (plan.at 4).code input=.ok after 0 ∧
 StateRepr 1 1 16 F resultState addresses after ∧ after.stack=input.stack ∧
 BaseExtends origin.H initialBase addresses ∧
 after.mem 4=w[3] ∧ after.mem 7=w[3] ∧ after.mem 6=w[3] ∧ after.mem 5=input.mem 2 ∧
 after.mem 9=w[10] ∧ after.mem 8=w[10] ∧
 GrowsAllocator 1 16 0 origin initialBase input resultState addresses after ∧
 (∀ x,x≠4 → x≠9 → x≠8 → x≠5 → x≠6 → x≠7 → (x<10 ∨ 16≤x) → after.mem x=input.mem x) ∧
 (∀ j,j<3 → after.mem (10+2*j)=input.mem 2 ∧ after.mem (10+2*j+1)=.val (wmod (3-j))) := by
 obtain ⟨after,addresses,executed,source,represented,stack,extended,destination,privateResult,counter,alias,cursor,bottom,growth,outside,saved⟩ :=
   DisjointScalarReturn.endpoint (c:=5) rfl origin reference ScalarReentry.count emitted.value .here 3 (by decide)
     actual_count initialBase input ScalarContinuation.endpoint.2.2.1
     8 9 8 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
       (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) prefix_cursor
 exact ⟨after,addresses,executed,represented,stack,extended,destination,privateResult,counter,alias,cursor,bottom,growth,outside,saved⟩

noncomputable def machine : Machine := available.choose
noncomputable def addresses : Nat → Fin W := available.choose_spec.choose

theorem specification :
 run (plan.at 4).code input=.ok machine 0 ∧
 StateRepr 1 1 16 F resultState addresses machine ∧ machine.stack=input.stack ∧
 BaseExtends origin.H initialBase addresses ∧
 machine.mem 4=w[3] ∧ machine.mem 7=w[3] ∧ machine.mem 6=w[3] ∧ machine.mem 5=input.mem 2 ∧
 machine.mem 9=w[10] ∧ machine.mem 8=w[10] ∧
 GrowsAllocator 1 16 0 origin initialBase input resultState addresses machine ∧
 (∀ x,x≠4 → x≠9 → x≠8 → x≠5 → x≠6 → x≠7 → (x<10 ∨ 16≤x) → machine.mem x=input.mem x) ∧
 (∀ j,j<3 → machine.mem (10+2*j)=input.mem 2 ∧ machine.mem (10+2*j+1)=.val (wmod (3-j))) :=
 available.choose_spec.choose_spec

theorem ownership : StructAllocatorRepr resultState.heap addresses 16 (⟨26,by decide⟩ : Fin W) machine := by
 rcases specification with ⟨_,_,_,_,_,_,_,_,_,_,growth,_,_⟩
 exact growth ⟨26,by decide⟩ (by decide) ScalarContinuation.allocation_facts.2.2.1 (by decide)

theorem whole_target : run (ScalarContinuation.image++(plan.at 4).code) before=.ok machine 0 :=
 (run_append_ok ScalarContinuation.target_execution).trans specification.1

/-- The exported scalar does not discard the private object allocated before
re-entry. Its old base is retained by the actual second endpoint. -/
theorem new_object_base : addresses 2=⟨22,by decide⟩ :=
 specification.2.2.2.1 ((ScalarContinuation.changed.alloc (defaultArray .uint ScalarContinuation.size)).2)

theorem old_state_count : ScalarReentry.count.evalT caller=.ok (countValue 7 (by decide)) := by
 with_unfolding_all rfl

theorem rejects_stale_count : ScalarReentry.count.evalT origin≠.ok (countValue 7 (by decide)) := by
 rw [actual_count]
 intro same
 have values := congrArg (fun value : PrimTy.uint.Denote => value.val) (Except.ok.inj same)
 change (3:Int)=7 at values
 contradiction


def sourceProgram : Prog CountdownWitness.P.C Γ Γ :=
 .cons (.block (ScalarContinuation.program 4)) (.cons (statement 4) .nil)
def sourceOutput : Solidity.Out CountdownWitness.P.C caller.H Γ := ⟨resultState,ScalarContinuation.extension⟩

theorem block_source : (.block (ScalarContinuation.program 4) : Stmt CountdownWitness.P.C Γ Γ).run caller=
 .ok ScalarContinuation.output := by
 have actual := ScalarContinuation.source_program
 change TRun.block (ScalarContinuation.program 4).ext (ScalarContinuation.program 4).runR caller=_
 unfold TRun.block
 change (ScalarContinuation.program 4).runR caller=.ok ScalarContinuation.output at actual
 rw [actual]
 have scope : (ScalarContinuation.program 4).ext=Ext.refl := Subsingleton.elim _ _
 simp only [Except.map,scope]
 rfl

theorem whole_source : sourceProgram.run caller=.ok sourceOutput := by
 have second := (source 4).trans (if_pos (by decide))
 rw [sourceProgram,Prog.run_cons_ok block_source]
 simp only [ScalarContinuation.output]
 rw [Prog.run_cons_ok second,Prog.run_nil]
 rfl

theorem endpoint : sourceProgram.run caller=.ok sourceOutput ∧
 run (ScalarContinuation.image++(plan.at 4).code) before=.ok machine 0 ∧
 StateRepr 1 1 16 F resultState addresses machine ∧ machine.stack=before.stack ∧
 BaseExtends caller.H CountdownWitness.P.base addresses ∧
 GrowsAllocator 1 16 4 caller CountdownWitness.P.base before resultState addresses machine := by
 rcases specification with ⟨executed,represented,stack,extended,destination,privateResult,counter,alias,cursor,bottom,growth,outside,saved⟩
 have combined := ScalarContinuation.growth.comp growth
 exact ⟨whole_source,whole_target,represented,stack.trans ScalarContinuation.endpoint.2.2.2.1,
   BaseExtends.trans ScalarContinuation.extension ScalarContinuation.bases_preserved extended,
   by simpa only [Nat.add_zero] using combined⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarReentry.Endpoint
