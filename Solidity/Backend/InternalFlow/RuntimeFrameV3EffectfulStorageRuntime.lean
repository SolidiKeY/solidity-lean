import Solidity.Backend.InternalFlow.RuntimeFrameV3EffectfulRuntime
import Solidity.Backend.InternalFlow.RuntimeFrameV3OrderedEffectfulStorage

/-! Frozen return transport for the selected heap-only effectful family,
INCLUDING fragile caller aliases. This consumes the proved storage-preserving
endpoint and keeps the SAME metadata and capacity. Original claims unchanged.
No approved-profile, arbitrary-body or full-outcome closure is supplied. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource EffectfulSourceSelection
open EffectfulRuntime (plan capacity)

theorem returned_of_eval {C : Contract} {Γ : Ctx} {b c pointer bottom L frame : Nat}
 {F : Frag Γ} {source : Stmt C Γ Γ} (selected : Selected b F source)
 (disjoint : b+Γ.length≤c) (workspace : c+3≤bottom) (below : bottom<pointer)
 {caller : State C Γ} {base : Nat → Fin W} {before : Machine} {start : Nat}
 (entry : InterfaceV1.Entry (plan selected c pointer bottom) L b frame F caller base before start)
 (value : PrimTy.uint.Denote) (evaluated : selected.count.evalT caller=.ok value)
 (ref : HRef caller.H EffectfulScalarSource.A) (alias : TEnv.get selected.reference caller.env=some ref)
 (live : 0<caller.heap.len ref .dyn) :
 InterfaceV1.Returned (plan selected c pointer bottom) L b frame caller base before start
 ⟨(OrderedEffectfulScalar.changed caller ref).setLocal selected.destination
   (countValue value.word.val value.word.isLt),List.prefix_refl _⟩ := by
 obtain ⟨apart,bottomBefore,room,fits⟩ := capacity selected entry value evaluated below
 have normalized : value=countValue value.word.val value.word.isLt := Subtype.ext (word_val value).symm
 have actualEval := evaluated
 rw [normalized] at actualEval
 have pointerBound : pointer<frame := entry.pointerBelow
 obtain ⟨after,addresses,executed,sourceRun,reached,stack,extended,destinationWord,resultWord,counterWord,referenceWord,cursor,bottomWord,growth,outside,saved⟩ :=
   OrderedEffectfulStorage.endpoint caller selected.reference ref alias live selected.count selected.value selected.destination
     value.word.val value.word.isLt actualEval base before entry.represented
     bottom pointer bottom start disjoint workspace (by omega) pointerBound (by omega) apart
     workspace (by omega) bottomBefore (by omega) room fits entry.cursor
 refine ⟨after,addresses,executed,reached,stack,extended,growth,cursor,?_⟩
 intro x low high
 change pointer≤x at low
 by_cases isPointer : x=pointer
 · subst x
   exact cursor.trans entry.cursor.symm
 · have destinationBelow : cellOf b selected.destination<c :=
     Nat.lt_of_lt_of_le (lvl_lt b selected.destination) disjoint
   have external := outside x (by omega) isPointer (by omega) (by omega) (by omega) (by omega) (.inl high)
   have heapAbove : frame≤(base ref.id).val := entry.represented.heap.above ref
   exact external.trans (upd_other before.mem w[37] (by omega))

/-- Successful source execution supplies liveness and rules out insufficient
    quotations. Neither is inserted as an admission hypothesis. -/
theorem returns {C : Contract} {Γ : Ctx} {b c pointer bottom : Nat}
 {F : Frag Γ} {source : Stmt C Γ Γ} (selected : Selected b F source)
 (disjoint : b+Γ.length≤c) (workspace : c+3≤bottom) (below : bottom<pointer)
 :
 InterfaceV1.ReturnClaim b F source (plan selected c pointer bottom) := by
 intro L frame caller base before start entry out actual
 have pointerBound : pointer<frame := entry.pointerBelow
 have checked := selected.value.cert.correct entry.represented
 rcases checked with ⟨value,word,evaluated,encoded,executed⟩ | ⟨failed,executed⟩
 · obtain ⟨ref,alias,pointerWord⟩ := entry.represented.pointers selected.reference
   by_cases live : 0<caller.heap.len ref .dyn
   · have normalized : value=countValue value.word.val value.word.isLt := Subtype.ext (word_val value).symm
     have args : (DisjointScalarEntry.args rfl selected.reference selected.count).evalT caller=
         .ok (countValue value.word.val value.word.isLt,(some ref,())) := by
       simp only [DisjointScalarEntry.args,Args.evalT,MPath.mvalT,alias,evaluated,ok_bind]
       rw [←normalized]
       rfl
     have sourceRun := EffectfulScalarSource.all_horizons selected.function
       (DisjointScalarEntry.args rfl selected.reference selected.count) selected.destination selected.depth caller
       value.word.val value.word.isLt ref args (OrderedEffectfulScalar.changed caller ref).heap
       (OrderedEffectfulScalar.write_addr caller ref live)
     have same := (selected.source_run caller).trans sourceRun
     by_cases enough : value.word.val<selected.depth
     · rw [if_pos enough] at same
       have equalOut := Except.ok.inj (actual.symm.trans same)
       subst out
       exact returned_of_eval selected disjoint workspace below entry value evaluated ref alias live
     · rw [if_neg enough] at same
       rw [same] at actual
       cases actual
   · have failed : caller.heap.writeAddr (.index ref .dyn (countValue 0 W_pos)) EffectfulScalarSource.replacement=none := by
       change (if 0<caller.heap.len ref .dyn then _ else none)=none
       exact if_neg live
     have normalized : value=countValue value.word.val value.word.isLt := Subtype.ext (word_val value).symm
     rw [normalized] at evaluated
     have sourceFailed := (selected.callee_failure caller ref alias value.word.val value.word.isLt evaluated failed
       base before entry.represented disjoint (by omega) pointer bottom).1
     rw [sourceFailed] at actual
     cases actual
 · have sourceFailed := (selected.argument_failure caller failed base before entry.represented disjoint (by omega) pointer bottom).1
   rw [sourceFailed] at actual
   cases actual


/-- The existing bare-revert claim already supports all caller fragments. -/
theorem bare_revert {C : Contract} {Γ : Ctx} {b c pointer bottom : Nat}
 {F : Frag Γ} {source : Stmt C Γ Γ} (selected : Selected b F source)
 (disjoint : b+Γ.length≤c) (workspace : c+3≤bottom) (below : bottom<pointer) :
 InterfaceV1.BareRevertClaim b F source (plan selected c pointer bottom) :=
 EffectfulRuntime.bare_revert selected disjoint workspace below

end Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.returned_of_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.returned_of_eval

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.returns

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.bare_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulStorageRuntime.bare_revert
