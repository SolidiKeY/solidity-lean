import Solidity.Backend.StructuredFlow.DoWhileContinueCompiler
import Solidity.Backend.StructuredFlow.ForBreakCompilerControls

namespace Solidity.Backend.StructuredFlow.DoWhileContinueCompiler.Controls
open Solidity.Evm Solidity.Lowering.V07 Solidity.Lowering.G19
open AssignmentWhileBreak (code)
open ForBreakCompiler (emit)
open Source.SemanticsExamples (G0 F0)
open MappedCondition.Controls (C mapping caller snapshot frame)
open ConditionalSourceCompiler.Controls (Rel)
open AssignmentWhileReset.Controls (source machine entry initial)

/-- Both pipelines, all extra fuel and both Boolean values. The suffix
would overwrite the result if executed; continue bypasses it. -/
theorem joined (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag : Bool) :
    (Source.execS (G0 pipeline) F0 (fuel+6) 0 none (R := []) (M := false)
      (.doWhile (l := false) (u := false)
        (AssignmentDoWhileContinue.body .here (.there .here)
          (.stmt (.expr (.assign (.local .here) (.bool (!flag)))) .nil)) (.bool false)) (source flag).1).run
      (.nil,(source flag).2) =
      (.ok (Source.Out.normal ((source flag).1.set .here (.bool flag))),(.nil,(source flag).2)) ∧
    StmtOut C 1 0 (Frag.init [.val .bool,.val .bool]) false false false
      ((code mapping .here (.there .here) rfl rfl : Prog C _ _).run (caller flag))
      (run (emit (C := C) 0 mapping .here (.there .here) rfl rfl) (machine flag)) (machine flag) ∧
    run (emit (C := C) 0 mapping .here (.there .here) rfl rfl) (machine flag) =
      .ok (MappedCondition.after 0 mapping .here (.there .here) rfl rfl (machine flag)) 0 := by
  rcases correct (G0 pipeline) F0 fuel 0 none (returns := []) (M := false) (l := false) (u := false)
    (source flag) (caller flag) mapping Rel (initial flag) (fun _ _ h => h)
    .here (.there .here) rfl rfl rfl rfl (.stmt (.expr (.assign (.local .here) (.bool (!flag)))) .nil)
    (entry flag) with ⟨src,_,_,_,compiled,native⟩
  exact ⟨src,compiled,native⟩

theorem suffix_write_refused (pipeline : Roadmap.Pipeline) (flag : Bool) :
    (Source.execS (G0 pipeline) F0 6 0 none (R := []) (M := false)
      (.doWhile (l := false) (u := false)
        (AssignmentDoWhileContinue.body .here (.there .here)
          (.stmt (.expr (.assign (.local .here) (.bool (!flag)))) .nil)) (.bool false)) (source flag).1).run
      (.nil,(source flag).2) ≠ (.ok (Source.Out.normal (source flag).1),(.nil,(source flag).2)) := by
  rw [(joined pipeline 0 flag).1]
  cases flag <;> intro impossible <;> cases impossible

/-- The physical result records all five sampled cells and the sentinel/stack observation. -/
theorem observed (flag : Bool) :
    snapshot 0 (run (emit (C := C) 0 mapping .here (.there .here) rfl rfl) (machine flag)) =
      some [.val (bword flag),.val (bword flag),.val (bword flag),w[99],w[77]] := by
  exact ForBreakCompiler.Controls.observed flag

theorem omitted_body_refused :
    snapshot 0 (run [] (machine true)) ≠
      snapshot 0 (run (emit (C := C) 0 mapping .here (.there .here) rfl rfl) (machine true)) := by
  decide

end Solidity.Backend.StructuredFlow.DoWhileContinueCompiler.Controls
