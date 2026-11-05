import Solidity.Lowering.G19.AssignmentForContinue
import Solidity.Lowering.G19.AssignmentWhileContinueControls

namespace Solidity.Lowering.G19.AssignmentForContinue.Controls
open Solidity.Lowering.V07 Solidity.Evm
open Source.SemanticsExamples (E0 G0 F0)
open Solidity.Backend.StructuredFlow.MappedCondition.Controls (C mapping caller)
open Solidity.Backend.StructuredFlow.ConditionalSourceCompiler.Controls (Rel)
open AssignmentWhileReset.Controls (source machine core emitted initial)

def tail : Source.RItems E0 [] false ⟨true,false⟩ [.bool,.bool] [.bool,.bool] :=
  .stmt (.expr (.assign (.local (.there .here)) (.bool false))) .nil

def withoutPost : Source.RStmt E0 [] false ⟨false,false⟩ [.bool,.bool] [.bool,.bool] :=
  .forLoop .skip (.some (.assign (.local .here) (.local (.there .here)))) .none (body tail)

theorem joined (pipeline : Roadmap.Pipeline) (fuel : Nat) (flag : Bool) :
    (Source.execS (G0 pipeline) F0 (fuel+7) 0 none (R := []) (M := false)
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

theorem body_donor_observed (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    (match (Source.execS (G0 pipeline) F0 (fuel+4) 0 none (body tail) (source true).1).run
      (.nil,(source true).2) with
    | (.ok (.cont ls),_) => (ls.get (.there .here)).key
    | _ => none) = some 1 := by
  rw [body_run]
  rfl

theorem no_post_timeout : ∀ (pipeline : Solidity.Roadmap.Pipeline),
  (Solidity.Source.execS (Solidity.Source.SemanticsExamples.G0 pipeline) Solidity.Source.SemanticsExamples.F0
    7 0 none Solidity.Lowering.G19.AssignmentForContinue.Controls.withoutPost
    (Solidity.Lowering.G19.AssignmentWhileReset.Controls.source true).1).run
      (.nil,(Solidity.Lowering.G19.AssignmentWhileReset.Controls.source true).2) =
    (.error .timeout,(.nil,(Solidity.Lowering.G19.AssignmentWhileReset.Controls.source true).2)) := by
  intros
  rfl

theorem post_omission_refused (pipeline : Roadmap.Pipeline) :
    (Source.execS (G0 pipeline) F0 7 0 none (R := []) (M := false)
      (statement (l := false) .here (.there .here) tail) (source true).1).run (.nil,(source true).2) ≠
    (Source.execS (G0 pipeline) F0 7 0 none withoutPost (source true).1).run (.nil,(source true).2) := by
  rw [source_run (G0 pipeline) F0 0 0 none (R := []) (M := false) (l := false) (u := false)
    (source true).1 (source true).2 .here (.there .here) true rfl tail,no_post_timeout]
  intro impossible
  cases impossible

theorem observed (flag : Bool) : ∃ final, run emitted (machine flag) = .ok final 0 ∧
    final.mem 0 = .val (bword false) ∧ final.mem 1 = .val (bword false) ∧
    final.mem 3 = w[99] ∧ final.stack = [w[77]] := by
  exact AssignmentWhileReset.Controls.observed flag

end Solidity.Lowering.G19.AssignmentForContinue.Controls
