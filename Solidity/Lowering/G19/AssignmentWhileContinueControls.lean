import Solidity.Lowering.G19.AssignmentWhileContinue
import Solidity.Lowering.G19.AssignmentWhileResetControls

namespace Solidity.Lowering.G19.AssignmentWhileContinue.Controls
open Solidity.Lowering.V07 Solidity.Evm
open Source.SemanticsExamples (E0 G0 F0)
open Solidity.Backend.StructuredFlow.MappedCondition.Controls (C mapping caller)
open Solidity.Backend.StructuredFlow.ConditionalSourceCompiler.Controls (Rel)
open AssignmentWhileReset.Controls (source machine core emitted initial)

def tail : Source.RItems E0 [] false ⟨true,false⟩ [.bool,.bool] [.bool,.bool] :=
  .stmt (.expr (.assign (.local (.there .here)) (.bool true))) .nil

theorem joined (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag : Bool) :
    (Source.execS (G0 pipeline) F0 (fuel+8) 0 none (R := []) (M := false)
      (statement (l := false) .here (.there .here) tail) (source flag).1).run (.nil,(source flag).2) =
      (.ok (Source.Out.normal (AssignmentWhileReset.sourceAfter (source flag).1 .here (.there .here) flag)),
        (.nil,(source flag).2)) ∧
    core.run (caller flag) = .ok ⟨AssignmentWhileReset.targetAfter mapping .here (.there .here)
      rfl rfl (caller flag),List.prefix_refl _⟩ ∧
    mapping.Related Rel (AssignmentWhileReset.sourceAfter (source flag).1 .here (.there .here) flag)
      (AssignmentWhileReset.targetAfter mapping .here (.there .here) rfl rfl (caller flag)).env ∧
    (AssignmentWhileReset.targetAfter mapping .here (.there .here) rfl rfl (caller flag)).glob =
      (caller flag).glob := by
  exact correct (G0 pipeline) F0 fuel 0 none (returns := []) (M := false) (l := false) (u := false)
    (source flag) (caller flag) mapping Rel (initial flag) (fun _ _ h => h) rfl
    .here (.there .here) rfl rfl rfl rfl tail

theorem body_tail_skipped (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag : Bool) :
    (Source.execS (G0 pipeline) F0 (fuel+5) 0 none
      (body (.there .here) tail) (source flag).1).run (.nil,(source flag).2) =
      (.ok (Source.Out.cont ((source flag).1.set (.there .here) (.bool false))),
        (.nil,(source flag).2)) := by
  exact body_run (G0 pipeline) F0 fuel 0 none _ _ _ tail

theorem donor_observed (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag : Bool) :
    (match (Source.execS (G0 pipeline) F0 (fuel+5) 0 none
      (body (.there .here) tail) (source flag).1).run (.nil,(source flag).2) with
    | (.ok (.cont ls),_) => (ls.get (.there .here)).key
    | _ => none) = some 0 := by
  rw [body_tail_skipped]
  rfl

theorem wrong_donor_refused (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag : Bool) :
    (match (Source.execS (G0 pipeline) F0 (fuel+5) 0 none
      (body (.there .here) tail) (source flag).1).run (.nil,(source flag).2) with
    | (.ok (.cont ls),_) => (ls.get (.there .here)).key
    | _ => none) ≠ some 1 := by
  rw [donor_observed]
  decide

theorem observed (flag : Bool) : ∃ final, run emitted (machine flag) = .ok final 0 ∧
    final.mem 0 = .val (bword false) ∧ final.mem 1 = .val (bword false) ∧
    final.mem 3 = w[99] ∧ final.stack = [w[77]] := by
  exact AssignmentWhileReset.Controls.observed flag

theorem omitted_loop_refused : run (AssignmentWhileReset.Controls.omitted) (machine true) ≠
    run emitted (machine true) := by
  exact AssignmentWhileReset.Controls.omitted_loop_refused

end Solidity.Lowering.G19.AssignmentWhileContinue.Controls
