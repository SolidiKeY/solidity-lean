import Solidity.Backend.InternalFlow.RuntimeFrameV3MutatingPrefixes
import Solidity.Backend.InternalFlow.RuntimeFrameResultAgreement

/-! Actual mutating allocating recursive source returns at arbitrary sufficient quotation
indices. The recursion uses the existing intrinsic call semantics; no target
simulation or approved-domain certificate is asserted. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.MutatingSource
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes

/-- Every successful activation allocates exactly one object. Caller locals are
restored with the actual composed heap extension; all older array lengths are preserved
through real writes and allocations, while their contents may change. -/
theorem success {C : Contract} (depth : Nat) (σ : State C (Parameters A))
 (count : Nat) (bound : count<W) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (reads : count≤σ.heap.len ref .dyn) (enough : count<depth) :
 ∃ out, (MutatingActivation.body depth).run σ=.ok out ∧
   out.st.H.length=σ.H.length+count ∧
   out.st.env=TEnv.wk out.ext (Parameters A) σ.env ∧
   (∀ {R : RefTy} {E : Ty} (old : HRef σ.H R) (a : ArrTy R E),
     out.st.heap.len (old.wk out.ext) a=σ.heap.len old a) := by
 induction count generalizing depth σ with
 | zero =>
   cases depth with
   | zero => omega
   | succ depth =>
     refine ⟨⟨σ,List.prefix_refl _⟩,MutatingActivation.source_zero σ depth counter,?_,?_,(fun _ _ => rfl)⟩
     · change σ.H.length=σ.H.length+0
       omega
     · exact (TEnv.wk_self (List.prefix_refl σ.H) (Parameters A) σ.env).symm
 | succ count ih =>
   cases depth with
   | zero => omega
   | succ depth =>
     let mutated := MutatingActivation.changed σ ref count
     let parent := AllocatingActivation.allocated mutated
     let e := AllocatingActivation.extension mutated
     let inherited := ref.wk e
     let child : State C (Parameters A) := parent.withEnv (countValue count (by omega),(some inherited,()))
     have parameters := AllocatingActivation.allocated_parameters mutated count bound ref counter alias
     have kept : Heap.Keeps e mutated.heap parent.heap := Heap.keeps_alloc mutated.heap (AllocatingActivation.object mutated)
     have lengths : ∀ {R : RefTy} {E : Ty} (old : HRef σ.H R) (a : ArrTy R E),
         child.heap.len (old.wk e) a=σ.heap.len old a := by
       intro R E old a
       exact (kept.len old a).trans (MutatingActivation.lengths σ ref count (by omega) (by omega) old a)
     have length : child.heap.len inherited .dyn=σ.heap.len ref .dyn := lengths ref .dyn
     have readable : count≤child.heap.len inherited .dyn := by rw [length];omega
     obtain ⟨out,runChild,grown,locals,contents⟩ := ih depth child (by omega) inherited rfl rfl readable (by omega)
     have args := next_eval rfl parent count bound inherited parameters.1 parameters.2
     have native := call_return (nextArgs A rfl) .none .refl (MutatingActivation.body depth).runR
       parent child.env args out runChild
     let returned := exported (CallRet.none : CallRet (Parameters A) [] (Parameters A)) Ext.refl parent child.env out
     have call : (.call "mutatingCountdown" (nextArgs A rfl) .none (MutatingActivation.body depth) :
         Stmt C (Parameters A) (Parameters A)).run parent=.ok returned := native
     let final : Solidity.Out C σ.H (Parameters A) := ⟨returned.st,e.trans returned.ext⟩
     refine ⟨final,?_,?_,?_,?_⟩
     · rw [MutatingActivation.source_positive σ depth count bound ref counter alias (by omega),call]
       rfl
     · change out.st.H.length=σ.H.length+(count+1)
       change out.st.H.length=(σ.H++([.array (.prim .bool)] : HTy)).length+count at grown
       simpa only [List.length_append,List.length_singleton,Nat.add_assoc,Nat.add_comm 1 count] using grown
     · change TEnv.wk ((List.prefix_refl parent.H).trans out.ext) (Parameters A) parent.env=
         TEnv.wk (e.trans ((List.prefix_refl parent.H).trans out.ext)) (Parameters A) σ.env
       exact TEnv.wk_trans e ((List.prefix_refl parent.H).trans out.ext) (Parameters A) σ.env
     · intro R E old a
       exact (contents (old.wk e) a).trans (lengths old a)

/-- Valid reads do not turn insufficient quotation into success or revert.
There is no successful failed State in this conclusion. -/
theorem exhaustion {C : Contract} (depth : Nat) (σ : State C (Parameters A))
 (count : Nat) (bound : count<W) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (reads : count≤σ.heap.len ref .dyn) (short : depth≤count) :
 (MutatingActivation.body depth).run σ=.error .exhausted := by
 induction depth generalizing σ count with
 | zero => exact MutatingActivation.base_exhausts σ
 | succ depth ih =>
   cases count with
   | zero => omega
   | succ count =>
     let mutated := MutatingActivation.changed σ ref count
     let parent := AllocatingActivation.allocated mutated
     let e := AllocatingActivation.extension mutated
     let inherited := ref.wk e
     let child : State C (Parameters A) := parent.withEnv (countValue count (by omega),(some inherited,()))
     have parameters := AllocatingActivation.allocated_parameters mutated count bound ref counter alias
     have kept : Heap.Keeps e mutated.heap parent.heap := Heap.keeps_alloc mutated.heap (AllocatingActivation.object mutated)
     have lengths : ∀ {R : RefTy} {E : Ty} (old : HRef σ.H R) (a : ArrTy R E),
         child.heap.len (old.wk e) a=σ.heap.len old a := by
       intro R E old a
       exact (kept.len old a).trans (MutatingActivation.lengths σ ref count (by omega) (by omega) old a)
     have length : child.heap.len inherited .dyn=σ.heap.len ref .dyn := lengths ref .dyn
     have readable : count≤child.heap.len inherited .dyn := by rw [length];omega
     have nested := ih child count (by omega) inherited rfl rfl readable (by omega)
     have args := next_eval rfl parent count bound inherited parameters.1 parameters.2
     have failed : (.call "mutatingCountdown" (nextArgs A rfl) .none (MutatingActivation.body depth) :
         Stmt C (Parameters A) (Parameters A)).run parent=.error .exhausted := by
       change TRun.call (nextArgs A rfl) .none .refl (MutatingActivation.body depth).runR parent=_
       unfold TRun.call
       simp only [args,ok_bind,CallRet.enterT]
       change (do
         let out ← (MutatingActivation.body depth).run child
         pure (exported CallRet.none Ext.refl parent child.env out)) = _
       rw [nested]
       rfl
     rw [MutatingActivation.source_positive σ depth count bound ref counter alias (by omega),failed]
     rfl

/-- Actual evaluated call arguments and native export lift the recursive
allocation law to the complete caller context, with no tail/result oracle. -/
theorem call_success {C : Contract} {Γ : Ctx} (f : Name) (args : Args C Γ (Parameters A))
 (depth : Nat) (caller : State C Γ) (count : Nat) (bound : count<W) (ref : HRef caller.H A)
 (evaluated : args.evalT caller=.ok (countValue count bound,(some ref,())))
 (reads : count≤caller.heap.len ref .dyn) (enough : count<depth) :
 ∃ out, (InterfaceV1.recursiveSource f args .none MutatingActivation.step depth).run caller=.ok out ∧
   out.st.H.length=caller.H.length+count ∧ out.st.env=TEnv.wk out.ext Γ caller.env ∧
   (∀ {R : RefTy} {E : Ty} (old : HRef caller.H R) (a : ArrTy R E),
     out.st.heap.len (old.wk out.ext) a=caller.heap.len old a) := by
 let child : State C (Parameters A) := caller.withEnv (countValue count bound,(some ref,()))
 obtain ⟨out,executed,grown,locals,kept⟩ := success depth child count bound ref rfl rfl reads enough
 have native := call_return args .none .refl (MutatingActivation.body depth).runR caller child.env evaluated out executed
 refine ⟨exported CallRet.none Ext.refl caller child.env out,?_,grown,?_,kept⟩
 · exact native
 · rfl

theorem call_exhaustion {C : Contract} {Γ : Ctx} (f : Name) (args : Args C Γ (Parameters A))
 (depth : Nat) (caller : State C Γ) (count : Nat) (bound : count<W) (ref : HRef caller.H A)
 (evaluated : args.evalT caller=.ok (countValue count bound,(some ref,())))
 (reads : count≤caller.heap.len ref .dyn) (short : depth≤count) :
 (InterfaceV1.recursiveSource f args .none MutatingActivation.step depth).run caller=.error .exhausted := by
 let child : State C (Parameters A) := caller.withEnv (countValue count bound,(some ref,()))
 have failed := exhaustion depth child count bound ref rfl rfl reads short
 change TRun.call args .none .refl (MutatingActivation.body depth).runR caller=_
 unfold TRun.call
 simp only [evaluated,ok_bind,CallRet.enterT]
 change (do
   let out ← (MutatingActivation.body depth).run child
   pure (exported CallRet.none Ext.refl caller child.env out)) = _
 rw [failed]
 rfl


/-- Successful quotations agree on the whole dependent Out. Errors are not identified. -/
theorem bodies {C : Contract} (n k : Nat) :
 ResultAgreement.Steps (MutatingActivation.body (C:=C) n).runR (MutatingActivation.body k).runR := by
 induction n generalizing k with
 | zero => intro σ;exact ResultAgreement.error_left .exhausted _
 | succ n ih =>
   cases k with
   | zero => intro σ;exact ResultAgreement.error_right _ .exhausted
   | succ k =>
     change ResultAgreement.Steps
       (TRun.seq (TRun.ite nonzero .refl
         (TRun.seq MutatingActivation.write.runR
           (TRun.seq (DomainTransport.scopedNew .bool AllocatingActivation.lengthExpr).runR
             (TRun.seq GuardedRecursion.probe.runR
               (TRun.seq (TRun.call (nextArgs A rfl) .none .refl (MutatingActivation.body n).runR) TRun.nil))))
         .refl TRun.nil) TRun.nil)
       (TRun.seq (TRun.ite nonzero .refl
         (TRun.seq MutatingActivation.write.runR
           (TRun.seq (DomainTransport.scopedNew .bool AllocatingActivation.lengthExpr).runR
             (TRun.seq GuardedRecursion.probe.runR
               (TRun.seq (TRun.call (nextArgs A rfl) .none .refl (MutatingActivation.body k).runR) TRun.nil))))
         .refl TRun.nil) TRun.nil)
     exact ResultAgreement.seq
       (ResultAgreement.ite nonzero .refl .refl
         (ResultAgreement.seq (ResultAgreement.same _)
           (ResultAgreement.seq (ResultAgreement.same _)
             (ResultAgreement.seq (ResultAgreement.same _)
               (ResultAgreement.seq (ResultAgreement.call (nextArgs A rfl) .none .refl (ih k)) (ResultAgreement.same _)))))
         (ResultAgreement.same _)) (ResultAgreement.same _)

theorem source_coherence {C : Contract} {Γ : Ctx} (f : Name) (args : Args C Γ (Parameters A)) :
 InterfaceV1.RecursiveReturnCoherence f args .none MutatingActivation.step := by
 intro caller n k left right leftRun rightRun
 exact ResultAgreement.call args .none .refl (bodies n k) caller left right leftRun rightRun

namespace Checks
open CountdownWitness
abbrev A := CountdownWitness.A

def innerOut : Solidity.Out P.C MutatingPrefixes.Checks.firstState.H (Parameters A) :=
 ⟨MutatingPrefixes.Checks.parent,AllocatingActivation.extension MutatingPrefixes.Checks.mutated⟩

/-- The actual inner native return, opaque before composing its parent. -/
theorem inner : (MutatingActivation.body 2).run MutatingPrefixes.Checks.firstState=.ok innerOut := by
 have args := MutatingPrefixes.Checks.specification.2.1
 have native := call_return (nextArgs A rfl) .none .refl (MutatingActivation.body 1).runR
   MutatingPrefixes.Checks.parent MutatingPrefixes.Checks.child.env args
   ⟨MutatingPrefixes.Checks.child,List.prefix_refl _⟩ (MutatingPrefixes.Checks.child_source 0)
 have call : (.call "mutatingCountdown" (nextArgs A rfl) .none (MutatingActivation.body 1) :
   Stmt P.C (Parameters A) (Parameters A)).run MutatingPrefixes.Checks.parent=_ := native
 rw [MutatingActivation.source_positive MutatingPrefixes.Checks.firstState 1 0 (by decide)
   MutatingPrefixes.Checks.firstRef rfl rfl (by rw [MutatingPrefixes.Checks.first_length];decide)]
 change ((.call "mutatingCountdown" (nextArgs A rfl) .none (MutatingActivation.body 1) :
   Stmt P.C (Parameters A) (Parameters A)).run MutatingPrefixes.Checks.parent).map
   (fun out => (⟨out.st,(AllocatingActivation.extension MutatingPrefixes.Checks.mutated).trans out.ext⟩ :
     Solidity.Out P.C MutatingPrefixes.Checks.firstState.H (Parameters A)))=_
 rw [call]
 rfl

def rootNative := exported (CallRet.none : CallRet (Parameters A) [] (Parameters A)) Ext.refl
 MutatingActivation.Checks.parent MutatingActivation.Checks.child.env innerOut

def rootOut : Solidity.Out P.C callee.H (Parameters A) :=
 ⟨rootNative.st,(AllocatingActivation.extension MutatingActivation.Checks.mutated).trans rootNative.ext⟩

theorem root : (MutatingActivation.body 3).run callee=.ok rootOut := by
 have native := call_return (nextArgs A rfl) .none .refl (MutatingActivation.body 2).runR
   MutatingActivation.Checks.parent MutatingActivation.Checks.child.env
   MutatingActivation.Checks.specification.1 innerOut inner
 have call : (.call "mutatingCountdown" (nextArgs A rfl) .none (MutatingActivation.body 2) :
   Stmt P.C (Parameters A) (Parameters A)).run MutatingActivation.Checks.parent=.ok rootNative := native
 rw [MutatingActivation.source_positive callee 2 1 (by decide) P.r0 rfl rfl
   (by rw [HeapDomain.Checks.length_zero];decide)]
 change ((.call "mutatingCountdown" (nextArgs A rfl) .none (MutatingActivation.body 2) :
   Stmt P.C (Parameters A) (Parameters A)).run MutatingActivation.Checks.parent).map
   (fun out => (⟨out.st,(AllocatingActivation.extension MutatingActivation.Checks.mutated).trans out.ext⟩ :
     Solidity.Out P.C callee.H (Parameters A)))=_
 rw [call]
 rfl

def call (depth : Nat) : Stmt P.C P.Γ P.Γ :=
 InterfaceV1.recursiveSource "mutatingCountdown" CountdownWitness.args .none MutatingActivation.step depth

def returned : Solidity.Out P.C caller.H P.Γ :=
 exported CallRet.none Ext.refl caller callee.env rootOut

theorem actual : (call 3).run caller=.ok returned :=
 call_return CountdownWitness.args .none .refl (MutatingActivation.body 3).runR
   caller callee.env CountdownWitness.arguments rootOut root

theorem read_bound : 2≤caller.heap.len P.r0 .dyn := by
 change 2≤callee.heap.len P.r0 .dyn
 rw [HeapDomain.Checks.length_zero]
 omega

theorem all_sufficient (depth : Nat) (enough : 2<depth) :
 (call depth).run caller=.ok returned := by
 obtain ⟨out,executed,grown,locals,lengths⟩ := call_success "mutatingCountdown" CountdownWitness.args depth
   caller 2 (by decide) P.r0 CountdownWitness.arguments read_bound enough
 have same := source_coherence "mutatingCountdown" CountdownWitness.args caller depth 3 out returned executed actual
 rw [same] at executed
 exact executed

theorem ordered_bindings :
 ((TEnv.get (.here : Idx P.Γ (.val .uint)) returned.st.env).val,
  (TEnv.get (.there .here : Idx P.Γ (.mem A)) returned.st.env).map HRef.id,
  (TEnv.get (.there (.there .here) : Idx P.Γ (.mem A)) returned.st.env).map HRef.id,
  (TEnv.get (.there (.there (.there .here)) : Idx P.Γ (.mem A)) returned.st.env).map HRef.id)=
 (2,some 0,some 0,some 1) := rfl

theorem objects :
 returned.st.heap.len (P.r0.wk returned.ext) .dyn=2 ∧
 returned.st.heap.readAddr (.index (P.r0.wk returned.ext) .dyn (countValue 0 W_pos))=some (P.uint 1 (by decide)) ∧
 returned.st.heap.readAddr (.index (P.r0.wk returned.ext) .dyn (countValue 1 (by decide)))=some (P.uint 2 (by decide)) ∧
 returned.st.heap.len (Evm.Memory.CompileExamples.r1.wk returned.ext) .dyn=1 ∧
 returned.st.heap.readAddr (.index (Evm.Memory.CompileExamples.r1.wk returned.ext) .dyn (countValue 0 W_pos))=some (P.uint 4 (by decide)) :=
 MutatingPrefixes.Checks.source_objects

theorem allocation_count : returned.st.H.length=4 := rfl

theorem shallow (depth : Nat) (short : depth≤2) : (call depth).run caller=.error .exhausted :=
 call_exhaustion "mutatingCountdown" CountdownWitness.args depth caller 2 (by decide) P.r0
   CountdownWitness.arguments read_bound short

theorem shallow_not_revert (depth : Nat) (short : depth≤2) : (call depth).run caller≠.error .revert := by
 rw [shallow depth short]
 intro impossible
 cases impossible

def wrongScalar : Solidity.Out P.C caller.H P.Γ :=
 ⟨returned.st.setLocal .here (countValue 0 W_pos),returned.ext⟩
def wrongAlias : Solidity.Out P.C caller.H P.Γ :=
 ⟨returned.st.setLocal (.there .here) (some (Evm.Memory.CompileExamples.r1.wk returned.ext)),returned.ext⟩

theorem wrong_scalar (depth : Nat) (enough : 2<depth) : (call depth).run caller≠.ok wrongScalar := by
 rw [all_sufficient depth enough]
 intro wrong
 have same := Except.ok.inj wrong
 have observation := congrArg (fun out : Solidity.Out P.C caller.H P.Γ =>
   (TEnv.get (.here : Idx P.Γ (.val .uint)) out.st.env).val) same
 change (2:Int)=0 at observation
 omega

theorem wrong_alias (depth : Nat) (enough : 2<depth) : (call depth).run caller≠.ok wrongAlias := by
 rw [all_sufficient depth enough]
 intro wrong
 have same := Except.ok.inj wrong
 have observation := congrArg (fun out : Solidity.Out P.C caller.H P.Γ =>
   (TEnv.get (.there .here : Idx P.Γ (.mem A)) out.st.env).map HRef.id) same
 change (some 0 : Option Nat)=some 1 at observation
 cases observation

theorem not_keeps : ¬Heap.Keeps returned.ext caller.heap returned.st.heap := by
 intro kept
 have old : caller.heap.readAddr (.index P.r0 .dyn (countValue 0 W_pos))=some (P.uint 7 (by decide)) := by with_unfolding_all rfl
 have same := kept.readAddr (.index P.r0 .dyn (countValue 0 W_pos))
 rw [old] at same
 change returned.st.heap.readAddr (.index (P.r0.wk returned.ext) .dyn (countValue 0 W_pos))=some (P.uint 7 (by decide)) at same
 rw [objects.2.1] at same
 have values := congrArg (fun v : PrimTy.uint.Denote => v.val) (Option.some.inj same)
 change (1:Int)=7 at values
 omega

theorem root_state : rootOut.st=ParentPrefixes.sourceAt MutatingPrefixes.Checks.child 2 (by decide) := rfl

def private0 : HRef returned.st.H (.array (.prim .bool)) := ⟨2,rfl⟩
def private1 : HRef returned.st.H (.array (.prim .bool)) := ⟨3,rfl⟩

theorem private_objects :
 (returned.st.heap.len private0 .dyn,returned.st.heap.len private1 .dyn,
 [returned.st.heap.readAddr (.index private0 .dyn (countValue 0 W_pos)),
  returned.st.heap.readAddr (.index private0 .dyn (countValue 1 (by decide))),
  returned.st.heap.readAddr (.index private0 .dyn (countValue 2 (by decide))),
  returned.st.heap.readAddr (.index private1 .dyn (countValue 0 W_pos)),
  returned.st.heap.readAddr (.index private1 .dyn (countValue 1 (by decide))),
  returned.st.heap.readAddr (.index private1 .dyn (countValue 2 (by decide)))])=
 (3,3,[some false,some false,some false,some false,some false,some false]) := by
 with_unfolding_all rfl

end Checks

end Solidity.Backend.InternalFlow.RuntimeFrame.MutatingSource
