import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarRecursiveCall

/-! An actual callee write followed by native scalar recursion. Arguments are
already evaluated by the existing call semantics; no source evaluator, frame
oracle or approved-domain restriction is introduced. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulScalarSource
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
abbrev A : RefTy := .array (.prim .uint)
def replacement : PrimTy.uint.Denote := countValue 37 (by decide)
def write {C : Contract} : Stmt C (Frame A) (Frame A) :=
 .assignMem (.index .dyn (.var (.there (.there .here)) rfl) (.simple (.lit 0 rfl)))
   (.val (.simple (.lit 37 rfl)))
def body {C : Contract} (depth : Nat) : Prog C (Frame A) (Frame A) :=
 .cons write (ScalarRecursiveSource.body A rfl depth)
def invoke {C : Contract} {Γ : Ctx} (function : Name) (args : Args C Γ (Parameters A))
 (destination : Idx Γ (.val .uint)) (depth : Nat) : Stmt C Γ Γ :=
 .callRec function depth args (.val .uint (.user "result") (some destination)) (fun _ => body depth)

theorem write_source {C : Contract} (σ : State C (Frame A)) (ref : HRef σ.H A)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame A) (.mem A)) σ.env=some ref)
 (heap : Heap σ.H)
 (actual : σ.heap.writeAddr (.index ref .dyn (countValue 0 W_pos)) replacement=some heap) :
 write.run σ=.ok ⟨σ.withHeap heap,List.prefix_refl _⟩ := by
 change TRun.assignMem (.index .dyn (.var (.there (.there .here)) rfl) (.simple (.lit 0 rfl)))
   (.val (.simple (.lit 37 rfl))) σ=_
 simp only [TRun.assignMem,MSrc.mvalT,Val.evalT,Simple.evalT,MLoc.addrT,MPath.mvalT,alias,ok_bind]
 simp only [pure,Except.pure,bind,Except.bind]
 change (do
   let next ← TRes.ofOpt (σ.heap.writeAddr (.index ref .dyn (countValue 0 W_pos)) replacement)
   pure (⟨σ.withHeap next,List.prefix_refl _⟩ : Solidity.Out C σ.H (Frame A)))=_
 rw [actual]
 rfl

/-- Full native outcomes, including insufficient indices, for the actual
callee prefix. The primitive heap-write equation is the only effect input. -/
theorem all_horizons {C : Contract} {Γ : Ctx} (function : Name)
 (args : Args C Γ (Parameters A)) (destination : Idx Γ (.val .uint))
 (depth : Nat) (caller : State C Γ) (count : Nat) (bound : count<W)
 (ref : HRef caller.H A)
 (evaluated : args.evalT caller=.ok (countValue count bound,(some ref,())))
 (heap : Heap caller.H)
 (actual : caller.heap.writeAddr (.index ref .dyn (countValue 0 W_pos)) replacement=some heap) :
 (invoke function args destination depth).run caller=
 if count<depth then .ok ⟨(caller.withHeap heap).setLocal destination (countValue count bound),List.prefix_refl _⟩
 else .error .exhausted := by
 let child : State C (Frame A) :=
   (caller.withEnv (Δ:=Parameters A) (countValue count bound,(some ref,()))).push (t:=.val .uint) (PrimTy.dflt .uint)
 have wrote := write_source child ref rfl heap actual
 have recursive := ScalarRecursiveSource.all_horizons rfl depth (child.withHeap heap) count bound ref rfl rfl
 have inner : (body depth).run child=
     if count<depth then .ok ⟨finished (child.withHeap heap) count bound,List.prefix_refl _⟩ else .error .exhausted := by
   change TRun.seq write.runR (ScalarRecursiveSource.body A rfl depth).runR child=_
   simp only [TRun.seq,show write.runR child=.ok ⟨child.withHeap heap,List.prefix_refl _⟩ from wrote]
   change ((ScalarRecursiveSource.body A rfl depth).run (child.withHeap heap)).map _=_
   rw [recursive]
   by_cases enough : count<depth
   · simp only [if_pos enough,Except.map]
   · simp only [if_neg enough,Except.map]
 change TRun.call args (.val .uint (.user "result") (some destination)) (body (C:=C) depth).ext
   (body depth).runR caller=_
 have scope : (body (C:=C) depth).ext=Ext.refl := Subsingleton.elim _ _
 unfold TRun.call
 simp only [evaluated,ok_bind,CallRet.enterT,scope]
 change (do
   let out ← (body depth).run child
   pure (⟨out.st.withEnv
     ((CallRet.val .uint (.user "result") (some destination)).leaveT
       (TEnv.wk ((List.prefix_refl caller.H).trans out.ext) Γ caller.env) (TEnv.take [.val .uint] out.st.env)),
     (List.prefix_refl caller.H).trans out.ext⟩ : Solidity.Out C caller.H Γ))=_
 rw [inner]
 by_cases enough : count<depth
 · simp only [if_pos enough,ok_bind,CallRet.leaveT,TEnv.wk_self]
   rfl
 · simp only [if_neg enough,error_bind]

end Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulScalarSource

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulScalarSource.write_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulScalarSource.write_source

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulScalarSource.all_horizons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulScalarSource.all_horizons
