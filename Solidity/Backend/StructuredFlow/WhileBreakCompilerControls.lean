import Solidity.Backend.StructuredFlow.WhileBreakCompiler
import Solidity.Lowering.G19.AssignmentWhileResetControls

namespace Solidity.Backend.StructuredFlow.WhileBreakCompiler.Controls
open Solidity.Evm Solidity.Lowering.V07 Solidity.Lowering.G19
open AssignmentWhileBreak (code)
open ForBreakCompiler (emit)
open Source.SemanticsExamples (G0 F0)
open MappedCondition.Controls (C mapping caller snapshot frame)
open ConditionalSourceCompiler.Controls (Rel)
open AssignmentWhileReset.Controls (source machine entry initial)

theorem joined (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag : Bool) :
    (Source.execS (G0 pipeline) F0 (fuel+3) 0 none (R := []) (M := false)
      (.whileLoop (l := false) (u := false) (.assign (.local .here) (.local (.there .here))) .brk)
      (source flag).1).run (.nil,(source flag).2) =
      (.ok (Source.Out.normal ((source flag).1.set .here (.bool flag))),(.nil,(source flag).2)) ∧
    StmtOut C 1 0 (Frag.init [.val .bool,.val .bool]) false false false
      ((code mapping .here (.there .here) rfl rfl : Prog C _ _).run (caller flag))
      (run (emit (C := C) 0 mapping .here (.there .here) rfl rfl) (machine flag)) (machine flag) ∧
    run (emit (C := C) 0 mapping .here (.there .here) rfl rfl) (machine flag) =
      .ok (MappedCondition.after 0 mapping .here (.there .here) rfl rfl (machine flag)) 0 := by
  rcases correct (G0 pipeline) F0 fuel 0 none (returns := []) (M := false) (l := false) (u := false)
    (source flag) (caller flag) mapping Rel (initial flag) (fun _ _ h => h)
    .here (.there .here) rfl rfl rfl rfl (entry flag) with ⟨src,_,_,_,compiled,native⟩
  exact ⟨src,compiled,native⟩

theorem observed (flag : Bool) :
    snapshot 0 (run (emit (C := C) 0 mapping .here (.there .here) rfl rfl) (machine flag)) =
      some [.val (bword flag),.val (bword flag),.val (bword flag),w[99],w[77]] := by rfl

theorem nonzero_frame (flag : Bool) :
    snapshot 128 (run (emit (C := C) 128 mapping .here (.there .here) rfl rfl) (frame 128 flag)) =
      some [.val (bword flag),.val (bword flag),.val (bword flag),w[99],w[77]] := by
  exact MappedCondition.Controls.nonzero_frame flag

/-- False does not justify dropping the assignment condition's effects. -/
theorem omitted_condition_refused :
    snapshot 0 (run [] (machine false)) ≠
      snapshot 0 (run (emit (C := C) 0 mapping .here (.there .here) rfl rfl) (machine false)) := by
  decide

theorem wrong_base_refused :
    snapshot 128 (run (emit (C := C) 0 mapping .here (.there .here) rfl rfl) (frame 128 true)) ≠
      snapshot 128 (run (emit (C := C) 128 mapping .here (.there .here) rfl rfl) (frame 128 true)) := by
  exact MappedCondition.Controls.wrong_base_refused

theorem condition_write_required (pipeline : Roadmap.Pipeline) (flag : Bool) :
    (Source.execS (G0 pipeline) F0 3 0 none (R := []) (M := false)
      (.whileLoop (l := false) (u := false) (.assign (.local .here) (.local (.there .here))) .brk)
      (source flag).1).run (.nil,(source flag).2) ≠
      (.ok (Source.Out.normal (source flag).1),(.nil,(source flag).2)) := by
  rw [(joined pipeline 0 flag).1]
  cases flag <;> intro impossible <;> cases impossible

end Solidity.Backend.StructuredFlow.WhileBreakCompiler.Controls
