import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingActivation

/-! Actual allocating recursive source returns at arbitrary sufficient quotation
indices. The recursion uses the existing intrinsic call semantics; no target
simulation or approved-domain certificate is asserted. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSource
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes

/-- Every successful activation allocates exactly one object. Caller locals are
restored with the actual composed heap extension; every older object is kept
because this particular body only allocates and reads. -/
theorem success {C : Contract} (depth : Nat) (σ : State C (Parameters A))
 (count : Nat) (bound : count<W) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (reads : count≤σ.heap.len ref .dyn) (enough : count<depth) :
 ∃ out, (AllocatingActivation.body depth).run σ=.ok out ∧
   out.st.H.length=σ.H.length+count ∧
   out.st.env=TEnv.wk out.ext (Parameters A) σ.env ∧
   Heap.Keeps out.ext σ.heap out.st.heap := by
 induction count generalizing depth σ with
 | zero =>
   cases depth with
   | zero => omega
   | succ depth =>
     refine ⟨⟨σ,List.prefix_refl _⟩,AllocatingActivation.source_zero σ depth counter,?_,?_,Heap.Keeps.refl σ.heap⟩
     · change σ.H.length=σ.H.length+0
       omega
     · exact (TEnv.wk_self (List.prefix_refl σ.H) (Parameters A) σ.env).symm
 | succ count ih =>
   cases depth with
   | zero => omega
   | succ depth =>
     let parent := AllocatingActivation.allocated σ
     let e := AllocatingActivation.extension σ
     let inherited := ref.wk e
     let child : State C (Parameters A) := parent.withEnv (countValue count (by omega),(some inherited,()))
     have parameters := AllocatingActivation.allocated_parameters σ count bound ref counter alias
     have kept : Heap.Keeps e σ.heap parent.heap := Heap.keeps_alloc σ.heap (AllocatingActivation.object σ)
     have length : child.heap.len inherited .dyn=σ.heap.len ref .dyn := kept.len ref .dyn
     have readable : count≤child.heap.len inherited .dyn := by rw [length];omega
     obtain ⟨out,runChild,grown,locals,contents⟩ := ih depth child (by omega) inherited rfl rfl readable (by omega)
     have args := next_eval rfl parent count bound inherited parameters.1 parameters.2
     have native := call_return (nextArgs A rfl) .none .refl (AllocatingActivation.body depth).runR
       parent child.env args out runChild
     let returned := exported (CallRet.none : CallRet (Parameters A) [] (Parameters A)) Ext.refl parent child.env out
     have call : (.call "allocatingCountdown" (nextArgs A rfl) .none (AllocatingActivation.body depth) :
         Stmt C (Parameters A) (Parameters A)).run parent=.ok returned := native
     let final : Solidity.Out C σ.H (Parameters A) := ⟨returned.st,e.trans returned.ext⟩
     refine ⟨final,?_,?_,?_,?_⟩
     · rw [AllocatingActivation.source_positive σ depth count bound ref counter alias (by omega),call]
       rfl
     · change out.st.H.length=σ.H.length+(count+1)
       change out.st.H.length=(σ.H++([.array (.prim .bool)] : HTy)).length+count at grown
       simpa only [List.length_append,List.length_singleton,Nat.add_assoc,Nat.add_comm 1 count] using grown
     · change TEnv.wk ((List.prefix_refl parent.H).trans out.ext) (Parameters A) parent.env=
         TEnv.wk (e.trans ((List.prefix_refl parent.H).trans out.ext)) (Parameters A) σ.env
       exact TEnv.wk_trans e ((List.prefix_refl parent.H).trans out.ext) (Parameters A) σ.env
     · exact kept.trans contents

/-- Valid reads do not turn insufficient quotation into success or revert.
There is no successful failed State in this conclusion. -/
theorem exhaustion {C : Contract} (depth : Nat) (σ : State C (Parameters A))
 (count : Nat) (bound : count<W) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (reads : count≤σ.heap.len ref .dyn) (short : depth≤count) :
 (AllocatingActivation.body depth).run σ=.error .exhausted := by
 induction depth generalizing σ count with
 | zero => exact AllocatingActivation.base_exhausts σ
 | succ depth ih =>
   cases count with
   | zero => omega
   | succ count =>
     let parent := AllocatingActivation.allocated σ
     let e := AllocatingActivation.extension σ
     let inherited := ref.wk e
     let child : State C (Parameters A) := parent.withEnv (countValue count (by omega),(some inherited,()))
     have parameters := AllocatingActivation.allocated_parameters σ count bound ref counter alias
     have kept : Heap.Keeps e σ.heap parent.heap := Heap.keeps_alloc σ.heap (AllocatingActivation.object σ)
     have length : child.heap.len inherited .dyn=σ.heap.len ref .dyn := kept.len ref .dyn
     have readable : count≤child.heap.len inherited .dyn := by rw [length];omega
     have nested := ih child count (by omega) inherited rfl rfl readable (by omega)
     have args := next_eval rfl parent count bound inherited parameters.1 parameters.2
     have failed : (.call "allocatingCountdown" (nextArgs A rfl) .none (AllocatingActivation.body depth) :
         Stmt C (Parameters A) (Parameters A)).run parent=.error .exhausted := by
       change TRun.call (nextArgs A rfl) .none .refl (AllocatingActivation.body depth).runR parent=_
       unfold TRun.call
       simp only [args,ok_bind,CallRet.enterT]
       change (do
         let out ← (AllocatingActivation.body depth).run child
         pure (exported CallRet.none Ext.refl parent child.env out)) = _
       rw [nested]
       rfl
     rw [AllocatingActivation.source_positive σ depth count bound ref counter alias (by omega),failed]
     rfl

/-- Actual evaluated call arguments and native export lift the recursive
allocation law to the complete caller context, with no tail/result oracle. -/
theorem call_success {C : Contract} {Γ : Ctx} (f : Name) (args : Args C Γ (Parameters A))
 (depth : Nat) (caller : State C Γ) (count : Nat) (bound : count<W) (ref : HRef caller.H A)
 (evaluated : args.evalT caller=.ok (countValue count bound,(some ref,())))
 (reads : count≤caller.heap.len ref .dyn) (enough : count<depth) :
 ∃ out, (InterfaceV1.recursiveSource f args .none AllocatingActivation.step depth).run caller=.ok out ∧
   out.st.H.length=caller.H.length+count ∧ out.st.env=TEnv.wk out.ext Γ caller.env ∧
   Heap.Keeps out.ext caller.heap out.st.heap := by
 let child : State C (Parameters A) := caller.withEnv (countValue count bound,(some ref,()))
 obtain ⟨out,executed,grown,locals,kept⟩ := success depth child count bound ref rfl rfl reads enough
 have native := call_return args .none .refl (AllocatingActivation.body depth).runR caller child.env evaluated out executed
 refine ⟨exported CallRet.none Ext.refl caller child.env out,?_,grown,?_,kept⟩
 · exact native
 · rfl

theorem call_exhaustion {C : Contract} {Γ : Ctx} (f : Name) (args : Args C Γ (Parameters A))
 (depth : Nat) (caller : State C Γ) (count : Nat) (bound : count<W) (ref : HRef caller.H A)
 (evaluated : args.evalT caller=.ok (countValue count bound,(some ref,())))
 (reads : count≤caller.heap.len ref .dyn) (short : depth≤count) :
 (InterfaceV1.recursiveSource f args .none AllocatingActivation.step depth).run caller=.error .exhausted := by
 let child : State C (Parameters A) := caller.withEnv (countValue count bound,(some ref,()))
 have failed := exhaustion depth child count bound ref rfl rfl reads short
 change TRun.call args .none .refl (AllocatingActivation.body depth).runR caller=_
 unfold TRun.call
 simp only [evaluated,ok_bind,CallRet.enterT]
 change (do
   let out ← (AllocatingActivation.body depth).run child
   pure (exported CallRet.none Ext.refl caller child.env out)) = _
 rw [failed]
 rfl

namespace Checks
open CountdownWitness

def call (depth : Nat) : Stmt P.C P.Γ P.Γ :=
 InterfaceV1.recursiveSource "allocatingCountdown" CountdownWitness.args .none AllocatingActivation.step depth

theorem read_bound : 2≤caller.heap.len P.r0 .dyn := by
 change 2≤callee.heap.len P.r0 .dyn
 rw [HeapDomain.Checks.length_zero]
 omega

/-- The actual output is selected from proved native execution, not supplied
as a desired endpoint or obtained by replaying the entire concrete family. -/
noncomputable def returned : Solidity.Out P.C caller.H P.Γ :=
 (call_success "allocatingCountdown" CountdownWitness.args 3 caller 2 (by decide) P.r0
   CountdownWitness.arguments read_bound (by decide)).choose

theorem specification : (call 3).run caller=.ok returned ∧
 returned.st.H.length=caller.H.length+2 ∧ returned.st.env=TEnv.wk returned.ext P.Γ caller.env ∧
 Heap.Keeps returned.ext caller.heap returned.st.heap :=
 (call_success "allocatingCountdown" CountdownWitness.args 3 caller 2 (by decide) P.r0
   CountdownWitness.arguments read_bound (by decide)).choose_spec

theorem ordered_bindings :
 ((TEnv.get (.here : Idx P.Γ (.val .uint)) returned.st.env).val,
  (TEnv.get (.there .here : Idx P.Γ (.mem CountdownWitness.A)) returned.st.env).map HRef.id,
  (TEnv.get (.there (.there .here) : Idx P.Γ (.mem CountdownWitness.A)) returned.st.env).map HRef.id,
  (TEnv.get (.there (.there (.there .here)) : Idx P.Γ (.mem CountdownWitness.A)) returned.st.env).map HRef.id)=
 (2,some 0,some 0,some 1) := by
 rw [specification.2.2.1]
 rfl

/-- Complete old-object contents in order, using the actual returned extension.
No arbitrary mutating body is assigned this heap-preservation property. -/
theorem old_objects :
 returned.st.heap.len (P.r0.wk returned.ext) .dyn=2 ∧
 returned.st.heap.readAddr (.index (P.r0.wk returned.ext) .dyn (countValue 0 W_pos))=some (P.uint 7 (by decide)) ∧
 returned.st.heap.readAddr (.index (P.r0.wk returned.ext) .dyn (countValue 1 (by decide)))=some (P.uint 9 (by decide)) ∧
 returned.st.heap.len (Evm.Memory.CompileExamples.r1.wk returned.ext) .dyn=1 ∧
 returned.st.heap.readAddr (.index (Evm.Memory.CompileExamples.r1.wk returned.ext) .dyn (countValue 0 W_pos))=some (P.uint 4 (by decide)) := by
 have kept : Heap.Keeps returned.ext caller.heap returned.st.heap := specification.2.2.2
 refine ⟨?_,?_,?_,?_,?_⟩
 · exact (kept.len P.r0 .dyn).trans HeapDomain.Checks.length_zero
 · have old : caller.heap.readAddr (.index P.r0 .dyn (countValue 0 W_pos))=some (P.uint 7 (by decide)) := by
     with_unfolding_all rfl
   have same := kept.readAddr (.index P.r0 .dyn (countValue 0 W_pos))
   rw [old] at same
   exact same
 · have old : caller.heap.readAddr (.index P.r0 .dyn (countValue 1 (by decide)))=some (P.uint 9 (by decide)) := by
     with_unfolding_all rfl
   have same := kept.readAddr (.index P.r0 .dyn (countValue 1 (by decide)))
   rw [old] at same
   exact same
 · exact (kept.len Evm.Memory.CompileExamples.r1 .dyn).trans HeapDomain.Checks.length_one
 · have old : caller.heap.readAddr (.index Evm.Memory.CompileExamples.r1 .dyn (countValue 0 W_pos))=some (P.uint 4 (by decide)) := by
     with_unfolding_all rfl
   have same := kept.readAddr (.index Evm.Memory.CompileExamples.r1 .dyn (countValue 0 W_pos))
   rw [old] at same
   exact same

theorem allocation_count : returned.st.H.length=4 := by
 have size := specification.2.1
 change returned.st.H.length=2+2 at size
 exact size

theorem wrong_alias : (TEnv.get (.there .here : Idx P.Γ (.mem CountdownWitness.A)) returned.st.env).map HRef.id≠some 1 := by
 have aliases := congrArg (fun x => x.2.1) ordered_bindings
 change (TEnv.get (.there .here : Idx P.Γ (.mem CountdownWitness.A)) returned.st.env).map HRef.id=some 0 at aliases
 rw [aliases]
 decide

theorem wrong_scalar : (TEnv.get (.here : Idx P.Γ (.val .uint)) returned.st.env).val≠1 := by
 have scalar := congrArg (fun x => x.1) ordered_bindings
 change (TEnv.get (.here : Idx P.Γ (.val .uint)) returned.st.env).val=2 at scalar
 rw [scalar]
 decide

theorem omitted_allocation : returned.st.H.length≠2 := by rw [allocation_count];decide

theorem wrong_old_content : returned.st.heap.readAddr (.index (P.r0.wk returned.ext) .dyn
 (countValue 1 (by decide)))≠some (P.uint 4 (by decide)) := by
 rw [old_objects.2.2.1]
 decide

theorem wrong_reference_bound : ¬2≤caller.heap.len Evm.Memory.CompileExamples.r1 .dyn := by
 change ¬2≤callee.heap.len Evm.Memory.CompileExamples.r1 .dyn
 rw [HeapDomain.Checks.length_one]
 decide

theorem shallow : (call 2).run caller=.error .exhausted :=
 call_exhaustion "allocatingCountdown" CountdownWitness.args 2 caller 2 (by decide) P.r0
   CountdownWitness.arguments read_bound (by decide)

theorem shallow_not_revert : (call 2).run caller≠.error .revert := by rw [shallow];intro bad;cases bad

theorem shallow_not_success (out : Solidity.Out P.C caller.H P.Γ) : (call 2).run caller≠.ok out := by
 rw [shallow];intro bad;cases bad

/-- The populated caller is reached by the existing real assignment prefix,
then the actual recursive call returns with both new objects. -/
def program : Prog P.C P.Γ P.Γ :=
 .cons (.assignLocal .here (.simple (.lit 2 rfl))) (.cons (call 3) .nil)

theorem prefix_then_call : program.run P.σ=.ok returned := by
 have started := CountdownWitness.source_prefix
 have nested := specification.1
 change (Stmt.assignLocal (.here : Idx P.Γ (.val .uint)) (.simple (.lit 2 rfl))).runR P.σ=
   .ok ⟨caller,List.prefix_refl _⟩ at started
 change (call 3).runR caller=.ok returned at nested
 change TRun.seq (Stmt.assignLocal (.here : Idx P.Γ (.val .uint)) (.simple (.lit 2 rfl))).runR
   (TRun.seq (call 3).runR TRun.nil) P.σ=_
 simp only [TRun.seq,started,nested,TRun.nil,Except.map]
 rfl

end Checks

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSource

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSource.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSource.success
