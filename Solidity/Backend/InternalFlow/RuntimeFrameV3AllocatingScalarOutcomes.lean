import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarSource

/-! Insufficient quotation for the actual allocating scalar family. Exhaustion
has no output State; no rollback, absence-of-effects or target divergence is
inferred. The index is quantified, never an added resource/admission cutoff. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

theorem exhaustion {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (depth : Nat) (σ : State C (Frame R)) (count : Nat) (bound : count<W) (ref : HRef σ.H R)
 (counter : TEnv.get (.there .here : Idx (Frame R) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame R) (.mem R)) σ.env=some ref)
 (short : depth≤count) : (body R hm depth).run σ=.error .exhausted := by
 induction depth generalizing σ count with
 | zero => rfl
 | succ depth ih =>
   cases count with
   | zero => omega
   | succ count =>
     let parent := allocated σ
     let inherited := ref.wk (extension σ)
     let arguments : TEnv C parent.H (Parameters R) := (countValue count (by omega),(some inherited,()))
     let child := entered parent count (by omega) inherited
     have parameters := allocated_parameters σ count bound ref counter alias
     have nested := ih child count (by omega) inherited rfl rfl (by omega)
     have args := next_eval hm parent count bound inherited parameters.1 parameters.2
     have failed : (.callRec "allocatingScalar" depth (next R hm) (result R) (fun _ => body R hm depth) :
       Stmt C (Frame R) (Frame R)).run parent=.error .exhausted := by
       change TRun.call (next R hm) (result R) (body R hm depth).ext (body R hm depth).runR parent=_
       unfold TRun.call
       simp only [args,ok_bind,result,CallRet.enterT]
       change (do
         let out ← (body R hm depth).run child
         pure (exported (result R) (body R hm depth).ext parent arguments out))=_
       rw [nested]
       rfl
     have continued : (continuation R hm depth (fun _ => body R hm depth)).run parent=.error .exhausted := by
       change TRun.seq (.callRec "allocatingScalar" depth (next R hm) (result R) (fun _ => body R hm depth) :
         Stmt C (Frame R) (Frame R)).runR (TRun.seq increment.runR TRun.nil) parent=_
       change (.callRec "allocatingScalar" depth (next R hm) (result R) (fun _ => body R hm depth) :
         Stmt C (Frame R) (Frame R)).runR parent=.error .exhausted at failed
       simp only [TRun.seq,failed]
     rw [source_positive hm σ depth count bound counter,continued]
     rfl

theorem success_iff {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (depth : Nat) (σ : State C (Frame R)) (count : Nat) (bound : count<W) (ref : HRef σ.H R)
 (counter : TEnv.get (.there .here : Idx (Frame R) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame R) (.mem R)) σ.env=some ref) :
 (∃ out,(body R hm depth).run σ=.ok out) ↔ count<depth := by
 constructor
 · rintro ⟨out,actual⟩
   by_cases enough : count<depth
   · exact enough
   · have exhausted := exhaustion hm depth σ count bound ref counter alias (by omega)
     rw [exhausted] at actual
     cases actual
 · intro enough
   obtain ⟨out,actual,rest⟩ := success hm depth σ count bound ref counter alias enough
   exact ⟨out,actual⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.exhaustion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.exhaustion

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.success_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.success_iff
