import Solidity.Backend.StructuredFlow.ForContinueCompiler
import Solidity.Backend.StructuredFlow.WhileContinueCompilerControls
import Solidity.Lowering.G19.AssignmentForContinueControls

namespace Solidity.Backend.StructuredFlow.ForContinueCompiler.Controls
open Solidity.Evm Solidity.Lowering.V07 Solidity.Lowering.G19
open Source.SemanticsExamples (E0 G0 F0)
open MappedCondition.Controls (C mapping caller)
open ConditionalSourceCompiler.Controls (Rel)
open AssignmentWhileReset.Controls (source machine core entry initial)
open AssignmentForContinue.Controls (tail)

theorem joined (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag : Bool) :
    (Source.execS (G0 pipeline) F0 (fuel+7) 0 none (R := []) (M := false)
      (AssignmentForContinue.statement (l := false) .here (.there .here) tail) (source flag).1).run
      (.nil,(source flag).2) =
      (.ok (Source.Out.normal (AssignmentWhileReset.sourceAfter (source flag).1 .here (.there .here) flag)),
        (.nil,(source flag).2)) ∧
    StmtOut C 1 0 (Frag.init [.val .bool,.val .bool]) false false false
      (core.run (caller flag)) (run (emit (C := C) 0 mapping .here (.there .here) rfl rfl) (machine flag))
      (machine flag) := by
  rcases correct (G0 pipeline) F0 fuel 0 none (returns := []) (M := false) (l := false) (u := false)
    (source flag) (caller flag) mapping Rel (initial flag) (fun _ _ h => h) rfl
    .here (.there .here) rfl rfl rfl rfl tail (entry flag) rfl (by decide) with
    ⟨src,_,_,_,compiled⟩
  exact ⟨src,compiled⟩

/-- Exact equality to the already compiled reset loop, not a new expected-output oracle. -/
theorem emitted_eq : emit (C := C) 0 mapping .here (.there .here) rfl rfl =
    AssignmentWhileReset.Controls.emitted := by rfl

theorem observed (flag : Bool) : ∃ final,
    run (emit (C := C) 0 mapping .here (.there .here) rfl rfl) (machine flag) = .ok final 0 ∧
    final.mem 0 = .val (bword false) ∧ final.mem 1 = .val (bword false) ∧
    final.mem 3 = w[99] ∧ final.stack = [w[77]] := by
  exact AssignmentForContinue.Controls.observed flag

theorem body_before_post (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    (match (Source.execS (G0 pipeline) F0 (fuel+4) 0 none (AssignmentForContinue.body tail)
      (source true).1).run (.nil,(source true).2) with
    | (.ok (.cont ls),_) => (ls.get (.there .here)).key
    | _ => none) = some 1 := by
  exact AssignmentForContinue.Controls.body_donor_observed pipeline fuel

theorem post_omission_refused (pipeline : Roadmap.Pipeline) :
    (Source.execS (G0 pipeline) F0 7 0 none (R := []) (M := false)
      (AssignmentForContinue.statement (l := false) .here (.there .here) tail)
      (source true).1).run (.nil,(source true).2) ≠
    (Source.execS (G0 pipeline) F0 7 0 none AssignmentForContinue.Controls.withoutPost
      (source true).1).run (.nil,(source true).2) := by
  exact AssignmentForContinue.Controls.post_omission_refused pipeline

theorem wrong_guard_refused :
    run WhileContinueCompiler.Controls.wrongEmit (machine true) ≠
      run (emit (C := C) 0 mapping .here (.there .here) rfl rfl) (machine true) := by
  exact WhileContinueCompiler.Controls.guard_change_refused

theorem wrong_entry_refused :
    ¬ Sim C 1 0 (⟨[.ok,.dead]⟩ : Frag [.val .bool,.val .bool])
      (caller true) (machine false) := by
  exact WhileContinueCompiler.Controls.wrong_entry_refused

end Solidity.Backend.StructuredFlow.ForContinueCompiler.Controls
