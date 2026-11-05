import Solidity.Backend.InternalFlow.RuntimeFrameV3DisjointScalarReturn
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarCallerReturn

/-! The original populated scalar source call with a disjoint callee and a
changed caller result: private cell seven exports into destination four,
changing seventy-seven to three while preserving the caller scalar and aliases.
No general compiler selector or profile instance is supplied. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.DisjointScalarReturn.Client
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource CountdownWitness
abbrev Γ := ScalarCallerReturn.Γ
abbrev F := ScalarCallerReturn.F
abbrev caller := ScalarCallerReturn.caller
def before := writeMachine ScalarCallerReturn.before 9 w[10]
def reference : Idx Γ (.mem CountdownWitness.A) := .there (.there .here)
def count : Val P.C Γ .uint := .simple (.lit 3 rfl)
def value : CompiledVal 1 F count := (Memory.compileVal 1 F count).get (by rfl)

theorem selected : Memory.compileVal 1 F count=some value := rfl

theorem initial : StateRepr 1 1 16 F caller P.base before :=
 reserved_write ScalarCallerReturn.initial 9 (by decide) (by decide) w[10]

theorem source_identity (depth : Nat) :
 call rfl reference count (.here : Idx Γ (.val .uint)) "scalarCountdown" depth=ScalarCallerReturn.invoke depth := rfl

theorem available : ∃ (after : Machine) (addresses : Nat → Fin W),
 run (code 1 5 reference value (.here : Idx Γ (.val .uint)) 9 8) before=.ok after 0 ∧
 (∀ f depth,(call rfl reference count (.here : Idx Γ (.val .uint)) f depth).run caller=
   if 3<depth then .ok ⟨caller.setLocal .here (countValue 3 (by decide)),List.prefix_refl _⟩ else .error .exhausted) ∧
 StateRepr 1 1 16 F (caller.setLocal .here (countValue 3 (by decide))) addresses after ∧
 after.stack=[w[77]] ∧ BaseExtends caller.H P.base addresses ∧
 after.mem 4=w[3] ∧ after.mem 7=w[3] ∧ after.mem 6=w[3] ∧ after.mem 5=w[16] ∧
 after.mem 9=w[10] ∧ after.mem 8=w[10] ∧
 GrowsAllocator 1 16 0 caller P.base before (caller.setLocal .here (countValue 3 (by decide))) addresses after ∧
 (∀ x,x≠4 → x≠9 → x≠8 → x≠5 → x≠6 → x≠7 → (x<10 ∨ 16≤x) → after.mem x=before.mem x) ∧
 (∀ j,j<3 → after.mem (10+2*j)=w[16] ∧ after.mem (10+2*j+1)=.val (wmod (3-j))) :=
 endpoint rfl caller reference count value .here 3 (by decide) rfl P.base before initial
   8 9 8 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
     (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl

noncomputable def machine : Machine := available.choose
noncomputable def addresses : Nat → Fin W := available.choose_spec.choose

theorem specification :
 run (code 1 5 reference value (.here : Idx Γ (.val .uint)) 9 8) before=.ok machine 0 ∧
 (∀ f depth,(call rfl reference count (.here : Idx Γ (.val .uint)) f depth).run caller=
   if 3<depth then .ok ⟨caller.setLocal .here (countValue 3 (by decide)),List.prefix_refl _⟩ else .error .exhausted) ∧
 StateRepr 1 1 16 F (caller.setLocal .here (countValue 3 (by decide))) addresses machine ∧
 machine.stack=[w[77]] ∧ BaseExtends caller.H P.base addresses ∧
 machine.mem 4=w[3] ∧ machine.mem 7=w[3] ∧ machine.mem 6=w[3] ∧ machine.mem 5=w[16] ∧
 machine.mem 9=w[10] ∧ machine.mem 8=w[10] ∧
 GrowsAllocator 1 16 0 caller P.base before (caller.setLocal .here (countValue 3 (by decide))) addresses machine ∧
 (∀ x,x≠4 → x≠9 → x≠8 → x≠5 → x≠6 → x≠7 → (x<10 ∨ 16≤x) → machine.mem x=before.mem x) ∧
 (∀ j,j<3 → machine.mem (10+2*j)=w[16] ∧ machine.mem (10+2*j+1)=.val (wmod (3-j))) :=
 available.choose_spec.choose_spec

theorem initial_owner : StructAllocatorRepr caller.heap P.base 16 ⟨22,by decide⟩ before :=
 (((AllocatorReturn.Checks.ownership.localWrite 7 (by decide) (by decide) w[10]).localWrite
   7 (by decide) (by decide) w[0]).localWrite 4 (by decide) (by decide) w[77]).localWrite
   9 (by decide) (by decide) w[10]

theorem entry_contrast : ∃ middle,
 run (DisjointScalarEntry.code 1 5 reference value) before=.ok middle 0 ∧
 middle.mem 7=w[0] ∧ middle.mem 4=w[77] ∧ middle.stack=[w[77]] := by
 obtain ⟨ref,middle,args,executed,callee,old,stack,referenceWord,outside,growth⟩ :=
   DisjointScalarEntry.entered (c:=5) rfl caller reference count value 3 (by decide) rfl P.base before initial (by decide) (by decide)
 have privateZero : middle.mem 7=w[0] := Restored.value_unique (callee.core.vals .here) (ReprV.dflt_zero .uint)
 have oldResult : middle.mem 4=w[77] := Restored.value_unique (old.core.vals .here) (ReprV.uint_of rfl)
 exact ⟨middle,executed,privateZero,oldResult,stack⟩

theorem old_caller_words : (machine.mem 1,machine.mem 2,machine.mem 3)=(w[16],w[16],w[2]) := by
 rcases specification with ⟨_,_,_,_,_,_,_,_,_,_,_,_,outside,_⟩
 rw [outside 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)),
   outside 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)),
   outside 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide))]
 rfl

theorem owner : StructAllocatorRepr caller.heap addresses 16 ⟨22,by decide⟩ machine := by
 rcases specification with ⟨_,_,_,_,_,_,_,_,_,_,_,growth,_⟩
 exact growth ⟨22,by decide⟩ (by decide) initial_owner (by decide)

theorem snapshot :
 (machine.stack,[machine.mem 0,machine.mem 1,machine.mem 2,machine.mem 3,machine.mem 4,
 machine.mem 5,machine.mem 6,machine.mem 7,machine.mem 8,machine.mem 9,machine.mem 10,
 machine.mem 11,machine.mem 12,machine.mem 13,machine.mem 14,machine.mem 15,machine.mem 16,
 machine.mem 17,machine.mem 18,machine.mem 19,machine.mem 20,machine.mem 21])=
 ([w[77]],[w[22],w[16],w[16],w[2],w[3],w[16],w[3],w[3],w[10],w[10],w[16],w[3],
 w[16],w[2],w[16],w[1],w[2],w[7],w[9],w[0],w[1],w[4]]) := by
 rcases specification with ⟨executed,source,reached,stack,extended,destination,result,counter,alias,cursor,bottomWord,growth,outside,saved⟩
 have one : machine.mem 1=w[16] := congrArg (fun xs : Word×Word×Word => xs.1) old_caller_words
 have two : machine.mem 2=w[16] := congrArg (fun xs : Word×Word×Word => xs.2.1) old_caller_words
 have three : machine.mem 3=w[2] := congrArg (fun xs : Word×Word×Word => xs.2.2) old_caller_words
 rw [stack,owner.arrays.free.cell,one,two,three,destination,result,counter,alias,cursor,bottomWord,
   (saved 0 (by decide)).1,(saved 0 (by decide)).2,
   (saved 1 (by decide)).1,(saved 1 (by decide)).2,
   (saved 2 (by decide)).1,(saved 2 (by decide)).2,
   outside 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   outside 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   outside 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   outside 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   outside 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   outside 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide))]
 rfl

theorem source_bindings :
 let out := caller.setLocal (.here : Idx Γ (.val .uint)) (countValue 3 (by decide))
 ((TEnv.get (.here : Idx Γ (.val .uint)) out.env).val,
 (TEnv.get (.there .here : Idx Γ (.val .uint)) out.env).val,
 (TEnv.get (.there (.there .here) : Idx Γ (.mem CountdownWitness.A)) out.env).map HRef.id,
 (TEnv.get (.there (.there (.there .here)) : Idx Γ (.mem CountdownWitness.A)) out.env).map HRef.id)=
 (3,2,some 0,some 0) := rfl

theorem native_and_target (depth : Nat) (enough : 3<depth) :
 (ScalarCallerReturn.invoke depth).run caller=.ok ⟨caller.setLocal .here (countValue 3 (by decide)),List.prefix_refl _⟩ ∧
 run (code 1 5 reference value (.here : Idx Γ (.val .uint)) 9 8) before=.ok machine 0 ∧
 StateRepr 1 1 16 F (caller.setLocal .here (countValue 3 (by decide))) addresses machine := by
 have source := specification.2.1 "scalarCountdown" depth
 rw [if_pos enough,source_identity] at source
 exact ⟨source,specification.1,specification.2.2.1⟩

theorem changed_destination : before.mem 4=w[77] ∧ machine.mem 4=w[3] ∧ machine.mem 4≠before.mem 4 := by
 have value := specification.2.2.2.2.2.1
 refine ⟨rfl,value,?_⟩
 rw [value]
 change w[3]≠w[77]
 decide

theorem distinct_slots : cellOf 1 (.here : Idx Γ (.val .uint))≠cellOf 5 (.here : Idx (Frame CountdownWitness.A) (.val .uint)) := by decide

theorem wrong_typed_slot : machine.mem 4≠machine.mem 3 := by
 have oldScalar : machine.mem 3=w[2] := congrArg (fun xs : Word×Word×Word => xs.2.2) old_caller_words
 rw [specification.2.2.2.2.2.1,oldScalar]
 decide

theorem wrong_alias : machine.mem 5≠w[20] := by
 rcases specification with ⟨_,_,_,_,_,_,_,_,alias,_⟩
 rw [alias]
 decide

theorem wrong_heap_cursor : machine.mem 0≠w[23] := by
 rw [owner.arrays.free.cell]
 decide

theorem shallow (depth : Nat) (short : depth≤3) : (ScalarCallerReturn.invoke depth).run caller=.error .exhausted := by
 have source := specification.2.1 "scalarCountdown" depth
 simpa only [source_identity,if_neg (show ¬(3:Nat)<depth from by omega)] using source

theorem not_revert : run (code 1 5 reference value (.here : Idx Γ (.val .uint)) 9 8) before≠.revert := by
 rw [specification.1]
 intro wrong
 cases wrong

theorem source_heap :
 let out := caller.setLocal (.here : Idx Γ (.val .uint)) (countValue 3 (by decide))
 (out.H.length,out.heap.len P.r0 .dyn,out.heap.len CompileExamples.r1 .dyn,
 [out.heap.readAddr (.index P.r0 .dyn (countValue 0 W_pos)),
  out.heap.readAddr (.index P.r0 .dyn (countValue 1 (by decide))),
  out.heap.readAddr (.index CompileExamples.r1 .dyn (countValue 0 W_pos))])=
 (2,2,1,[some (P.uint 7 (by decide)),some (P.uint 9 (by decide)),some (P.uint 4 (by decide))]) := by
 with_unfolding_all rfl

def badCount : Val P.C Γ .uint :=
 .readMem (.index .dyn (.var reference rfl) (.simple (.lit 3 rfl)))
def badValue : CompiledVal 1 F badCount := (Memory.compileVal 1 F badCount).get (by rfl)

theorem bad_selected : Memory.compileVal 1 F badCount=some badValue := rfl

theorem bad_eval : badCount.evalT caller=.error .revert := by
 with_unfolding_all rfl

theorem bad_arguments : (DisjointScalarEntry.args rfl reference badCount).evalT caller=.error .revert :=
 (DisjointScalarEntry.revert (c:=5) rfl caller reference badCount badValue bad_eval P.base before initial (by decide) (by decide)).1

theorem bad_prefix (suffix : List Instr) :
 run (DisjointScalarEntry.code 1 5 reference badValue ++ suffix) before=.revert :=
 (DisjointScalarEntry.revert (c:=5) rfl caller reference badCount badValue bad_eval P.base before initial (by decide) (by decide)).2 suffix

theorem bad_call (depth : Nat) :
 (call rfl reference badCount (.here : Idx Γ (.val .uint)) "scalarCountdown" depth).run caller=.error .revert := by
 change TRun.call (DisjointScalarEntry.args rfl reference badCount) (.val .uint (.user "result") (some .here))
   (ScalarRecursiveSource.body CountdownWitness.A rfl depth).ext
   (ScalarRecursiveSource.body CountdownWitness.A rfl depth).runR caller=_
 unfold TRun.call
 simp only [bad_arguments,error_bind]

theorem bad_target : run (code 1 5 reference badValue (.here : Idx Γ (.val .uint)) 9 8) before=.revert :=
 bad_prefix _

theorem argument_failure_not_exhausted :
 (call rfl reference badCount (.here : Idx Γ (.val .uint)) "scalarCountdown" 0).run caller≠.error .exhausted := by
 rw [bad_call]
 intro wrong
 cases wrong

end Solidity.Backend.InternalFlow.RuntimeFrame.DisjointScalarReturn.Client
