import Solidity.Backend.StructuredFlow.ForBreakCompiler
import Solidity.Lowering.G19.AssignmentWhileResetControls

namespace Solidity.Backend.StructuredFlow.ForBreakCompiler.Controls
open Solidity.Evm Solidity.Lowering.V07 Solidity.Lowering.G19
open AssignmentWhileBreak (code)
open Source.SemanticsExamples (G0 F0)
open MappedCondition.Controls (C mapping caller snapshot frame)
open ConditionalSourceCompiler.Controls (Rel)
open AssignmentWhileReset.Controls (source machine entry initial)

theorem joined (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag : Bool) :
    (Source.execS (G0 pipeline) F0 (fuel+4) 0 none (R := []) (M := false)
      (AssignmentForBreak.statement (l := false) (u := false) .here (.there .here)
        (.some (.assign (.local .here) (.bool (!flag))))) (source flag).1).run
      (.nil,(source flag).2) =
      (.ok (Source.Out.normal ((source flag).1.set .here (.bool flag))),(.nil,(source flag).2)) ∧
    StmtOut C 1 0 (Frag.init [.val .bool,.val .bool]) false false false
      ((code mapping .here (.there .here) rfl rfl : Prog C _ _).run (caller flag))
      (run (emit (C := C) 0 mapping .here (.there .here) rfl rfl) (machine flag)) (machine flag) ∧
    run (emit (C := C) 0 mapping .here (.there .here) rfl rfl) (machine flag) =
      .ok (MappedCondition.after 0 mapping .here (.there .here) rfl rfl (machine flag)) 0 := by
  rcases correct (G0 pipeline) F0 fuel 0 none (returns := []) (M := false) (l := false) (u := false)
    (source flag) (caller flag) mapping Rel (initial flag) (fun _ _ h => h)
    .here (.there .here) rfl rfl rfl rfl (.some (.assign (.local .here) (.bool (!flag))))
    (entry flag) with ⟨src,_,_,_,compiled,native⟩
  exact ⟨src,compiled,native⟩

theorem observed (flag : Bool) :
    snapshot 0 (run (emit (C := C) 0 mapping .here (.there .here) rfl rfl) (machine flag)) =
      some [.val (bword flag),.val (bword flag),.val (bword flag),w[99],w[77]] := by rfl

theorem nonzero_frame (flag : Bool) :
    snapshot 128 (run (emit (C := C) 128 mapping .here (.there .here) rfl rfl) (frame 128 flag)) =
      some [.val (bword flag),.val (bword flag),.val (bword flag),w[99],w[77]] := by
  exact MappedCondition.Controls.nonzero_frame flag

theorem omitted_initializer_refused :
    snapshot 0 (run [] (machine true)) ≠
      snapshot 0 (run (emit (C := C) 0 mapping .here (.there .here) rfl rfl) (machine true)) := by decide

theorem wrong_base_refused :
    snapshot 128 (run (emit (C := C) 0 mapping .here (.there .here) rfl rfl) (frame 128 true)) ≠
      snapshot 128 (run (emit (C := C) 128 mapping .here (.there .here) rfl rfl) (frame 128 true)) := by
  exact MappedCondition.Controls.wrong_base_refused

theorem post_write_refused (pipeline : Roadmap.Pipeline) (flag : Bool) :
    (Source.execS (G0 pipeline) F0 4 0 none (R := []) (M := false)
      (AssignmentForBreak.statement (l := false) (u := false) .here (.there .here)
        (.some (.assign (.local .here) (.bool (!flag))))) (source flag).1).run
      (.nil,(source flag).2) ≠ (.ok (Source.Out.normal (source flag).1),(.nil,(source flag).2)) := by
  have outcome :
      (Source.execS (G0 pipeline) F0 4 0 none (R := []) (M := false)
        (AssignmentForBreak.statement (l := false) (u := false) .here (.there .here)
          (.some (.assign (.local .here) (.bool (!flag))))) (source flag).1).run
        (.nil,(source flag).2) =
        (.ok (Source.Out.normal ((source flag).1.set .here (.bool flag))),(.nil,(source flag).2)) :=
    (joined pipeline 0 flag).1
  rw [outcome]
  cases flag <;> intro impossible <;> cases impossible

end Solidity.Backend.StructuredFlow.ForBreakCompiler.Controls
