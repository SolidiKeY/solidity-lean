import Solidity.Backend.StructuredFlow.WhileReturnCompiler
import Solidity.Lowering.G19.AssignmentWhileResetControls

namespace Solidity.Backend.StructuredFlow.WhileReturnCompiler.Controls
open Solidity.Evm Solidity.Lowering.V07 Solidity.Lowering.G19
open AssignmentReturnFlag (code)
open MappedCondition (emit)
open Source.SemanticsExamples (G0 F0)
open MappedCondition.Controls (C mapping caller loaded snapshot frame wrongCapture)
open ConditionalSourceCompiler.Controls (Rel)
open AssignmentWhileReset.Controls (source machine entry initial)

theorem joined (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag : Bool) :
    (Source.execS (G0 pipeline) F0 (fuel+3) 0 none (M := false)
      (.whileLoop (l := false) (u := false) (.assign (.local .here) (.local (.there .here))) (.ret rfl)) (source flag).1).run
      (.nil,(source flag).2) =
      (.ok (if flag then Source.Out.ret ((source flag).1.set .here (.bool flag))
        else Source.Out.normal ((source flag).1.set .here (.bool flag))),(.nil,(source flag).2)) ∧
    StmtOut C 1 0 (Frag.init [.val .bool,.val .bool,.val .bool]) false false false
      ((code mapping .here (.there .here) rfl rfl : Prog C _ _).run (caller flag))
      (run (emit 0 mapping .here (.there .here) rfl rfl) (machine flag)) (machine flag) ∧
    run (emit 0 mapping .here (.there .here) rfl rfl) (machine flag) =
      .ok (MappedCondition.after 0 mapping .here (.there .here) rfl rfl (machine flag)) 0 := by
  rcases correct (G0 pipeline) F0 fuel 0 none (M := false) (l := false) (u := false)
    (source flag) (caller flag) mapping Rel (initial flag) (fun _ _ h => h)
    .here (.there .here) rfl rfl rfl rfl
    (entry flag) with ⟨src,_,_,_,_,compiled,native⟩
  exact ⟨src,compiled,native⟩

theorem observed (flag : Bool) :
    snapshot 0 (run (emit 0 mapping .here (.there .here) rfl rfl) (machine flag)) =
      some [.val (bword flag),.val (bword flag),.val (bword flag),w[99],w[77]] := by rfl

theorem nonzero_frame (flag : Bool) :
    snapshot 128 (run (emit 128 mapping .here (.there .here) rfl rfl) (frame 128 flag)) =
      some [.val (bword flag),.val (bword flag),.val (bword flag),w[99],w[77]] := by
  exact MappedCondition.Controls.nonzero_frame flag

theorem wrong_flag_refused :
    snapshot 0 (run wrongCapture (loaded true)) ≠
      snapshot 0 (run (emit 0 mapping .here (.there .here) rfl rfl) (loaded true)) := by
  exact MappedCondition.Controls.stale_capture_refused

theorem wrong_base_refused :
    snapshot 128 (run (emit 0 mapping .here (.there .here) rfl rfl) (frame 128 true)) ≠
      snapshot 128 (run (emit 128 mapping .here (.there .here) rfl rfl) (frame 128 true)) := by
  exact MappedCondition.Controls.wrong_base_refused

theorem true_not_fallthrough (pipeline : Roadmap.Pipeline) :
    (Source.execS (G0 pipeline) F0 3 0 none (M := false)
      (.whileLoop (l := false) (u := false) (.assign (.local .here) (.local (.there .here))) (.ret rfl)) (source true).1).run
      (.nil,(source true).2) ≠
      (.ok (Source.Out.normal ((source true).1.set .here (.bool true))),(.nil,(source true).2)) := by
  have outcome :
    (Source.execS (G0 pipeline) F0 3 0 none (M := false)
      (.whileLoop (l := false) (u := false) (.assign (.local .here) (.local (.there .here))) (.ret rfl)) (source true).1).run
      (.nil,(source true).2) =
      (.ok (Source.Out.ret ((source true).1.set .here (.bool true))),(.nil,(source true).2)) := by
    simpa only [Bool.not_true,Nat.zero_add] using (joined pipeline 0 true).1
  rw [outcome]
  intro impossible
  cases impossible

theorem false_not_return (pipeline : Roadmap.Pipeline) :
    (Source.execS (G0 pipeline) F0 3 0 none (M := false)
      (.whileLoop (l := false) (u := false) (.assign (.local .here) (.local (.there .here))) (.ret rfl)) (source false).1).run
      (.nil,(source false).2) ≠
      (.ok (Source.Out.ret ((source false).1.set .here (.bool false))),(.nil,(source false).2)) := by
  have outcome :
    (Source.execS (G0 pipeline) F0 3 0 none (M := false)
      (.whileLoop (l := false) (u := false) (.assign (.local .here) (.local (.there .here))) (.ret rfl)) (source false).1).run
      (.nil,(source false).2) =
      (.ok (Source.Out.normal ((source false).1.set .here (.bool false))),(.nil,(source false).2)) := by
    simpa only [Bool.not_false,Nat.zero_add] using (joined pipeline 0 false).1
  rw [outcome]
  intro impossible
  cases impossible

end Solidity.Backend.StructuredFlow.WhileReturnCompiler.Controls
