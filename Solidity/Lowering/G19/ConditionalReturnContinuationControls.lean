import Solidity.Lowering.G19.ConditionalReturnContinuation
import Solidity.Lowering.G19.ConditionalReturnControls

namespace Solidity.Lowering.G19.ConditionalReturnContinuation.Controls
open Solidity.Lowering.V07
open Source.SemanticsExamples (E0 G0 F0)
open Solidity.Backend.StructuredFlow.MappedCondition.Controls (C)
open Solidity.Backend.StructuredFlow.ConditionalSourceCompiler.Controls
  (SourceCtx TargetCtx mapping Rel sci sca tci tca)
open Solidity.Backend.StructuredFlow.ReturnTailCompiler.Controls (source caller initial)

def sourceTail : Source.RItems E0 [] false ⟨false,false⟩ SourceCtx SourceCtx :=
  .stmt (.expr (.assign (.local .here) (.bool false))) .nil

def targetTail : Prog C (.val .bool :: TargetCtx) (.val .bool :: TargetCtx) :=
  .cons (.assignLocal (.there .here) (.simple (.bool false))) .nil

def eager : Prog C TargetCtx (.val .bool :: TargetCtx) :=
  (ConditionalReturn.code tci tca .here tci tca .here).join targetTail

theorem joined (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag checked : Bool) :
    (Source.execS (G0 pipeline) {F0 with checked := checked} (fuel+8) 0 none (M := false)
      (statement (k := ⟨false,false⟩) sci sca .here sci sca .here sourceTail) (source flag).1).run
      (.nil,(source flag).2) =
      (.ok (Source.Out.ret (ConditionalAssignments.sourceAfter (source flag) sci flag .here sci sca .here).1),
        (.nil,(source flag).2)) ∧
    (code (C := C) tci tca .here tci tca .here targetTail).run (caller flag) =
      .ok ⟨ConditionalReturn.reached (caller flag) tci flag .here tci tca .here,List.prefix_refl _⟩ ∧
    (mapping.wk (Thin.drop (t := .val .bool) .refl)).Related Rel
      (ConditionalAssignments.sourceAfter (source flag) sci flag .here sci sca .here).1
      (ConditionalReturn.reached (caller flag) tci flag .here tci tca .here).env := by
  rcases correct (G0 pipeline) {F0 with checked := checked} fuel 0 none
    (M := false) (k := ⟨false,false⟩) (source flag) (caller flag) mapping Rel
    (initial flag) (fun _ _ h => h) sci sca .here sci sca .here
    tci tca .here tci tca .here rfl rfl rfl rfl rfl rfl sourceTail targetTail with ⟨src,typed,related,_,_⟩
  exact ⟨src,typed,related⟩

theorem observed (flag : Bool) :
    ConditionalReturn.Controls.observe (code (C := C) tci tca .here tci tca .here targetTail) flag =
      some [true,true,flag,true] := by
  unfold ConditionalReturn.Controls.observe
  rw [target_run (caller flag) tci tca flag .here tci tca .here targetTail rfl]
  cases flag <;> rfl

theorem eager_observed (flag : Bool) :
    ConditionalReturn.Controls.observe eager flag = some [true,false,flag,true] := by
  have beforeRun : (ConditionalReturn.code (C := C) tci tca .here tci tca .here).run (caller flag) =
      .ok ⟨ConditionalReturn.reached (caller flag) tci flag .here tci tca .here,List.prefix_refl _⟩ :=
    ConditionalReturn.target_run (caller flag) tci tca flag .here tci tca .here rfl
  unfold Prog.run at beforeRun
  unfold ConditionalReturn.Controls.observe
  rw [eager,DeferredSource.join_run]
  unfold TRun.seq
  rw [beforeRun]
  cases flag <;> rfl

theorem eager_refused (flag : Bool) :
    ConditionalReturn.Controls.observe eager flag ≠
      ConditionalReturn.Controls.observe (code (C := C) tci tca .here tci tca .here targetTail) flag := by
  rw [eager_observed,observed]
  cases flag <;> decide

/-- The skipped write is real: executing the target tail changes the caller cell. -/
theorem tail_writes (flag : Bool) :
    (targetTail.run (ConditionalReturn.reached (caller flag) tci flag .here tci tca .here)) =
      .ok ⟨(ConditionalReturn.reached (caller flag) tci flag .here tci tca .here).setLocal
        (.there .here) false,List.prefix_refl _⟩ := by rfl

end Solidity.Lowering.G19.ConditionalReturnContinuation.Controls
