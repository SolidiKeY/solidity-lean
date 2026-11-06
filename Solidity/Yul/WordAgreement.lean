import Solidity.Yul.WordLogic
import Solidity.Yul.HorizonAdapter
import Solidity.Calculus.Logic

/-! Actual agreement with the existing G51 modality operator on closed-word
complete/divergent runs. This does not embed Source.RStmt or its state/events.
One None horizon is not THalt.exhausted; all horizons None means divergence. -/
namespace Solidity.Yul.Logic
open Solidity.Yul.Closed
open Solidity.Semantics
open Solidity (Modality)

/-- Every premise refers to the actual interpreter, not a preparation oracle. -/
inductive Run (model : Model F) (program : Program F c n) (vars : Values n) :
    TRes (Closed.Outcome c n) → Prop where
  | complete (fuel : Nat) (result : Closed.Outcome c n) :
      evalStmt fuel model.environment model.words program.code program.words vars = some result →
      Run model program vars (.ok result)
  | diverge :
      (∀ fuel, evalStmt fuel model.environment model.words program.code program.words vars = none) →
      Run model program vars (.error .diverge)

theorem Run.total (model : Model F) (program : Program F c n) (vars : Values n) :
    ∃ result, Run model program vars result := by
  classical
  by_cases completed : ∃ fuel result,
      evalStmt fuel model.environment model.words program.code program.words vars = some result
  · rcases completed with ⟨fuel,result,actual⟩
    exact ⟨.ok result,.complete fuel result actual⟩
  · refine ⟨.error .diverge,.diverge ?_⟩
    intro fuel
    cases found : evalStmt fuel model.environment model.words program.code program.words vars with
    | none => rfl
    | some result => exact False.elim (completed ⟨fuel,result,found⟩)

theorem Run.unique {model : Model F} {program : Program F c n} {vars : Values n}
    {first second} (one : Run model program vars first) (two : Run model program vars second) :
    first = second := by
  cases one with
  | complete fuel result actual =>
    cases two with
    | complete other result' actual' =>
      exact congrArg Except.ok (evalStmt_completed_unique model.environment model.words
        program.code program.words vars actual actual')
    | diverge all => rw [all fuel] at actual; cases actual
  | diverge all =>
    cases two with
    | complete fuel result actual => rw [all fuel] at actual; cases actual
    | diverge all' => rfl

/-- The existing afterRunTR is used unchanged, including its panic check and
the distinction between diverge and resource exhausted. No new halt is added. -/
theorem modal_agrees {model : Model F} {program : Program F c n} {vars : Values n}
    {result} (mode : Modality) (post : Flow c → Fml n)
    (actual : Run model program vars result) :
    (Fml.modal mode model program post).holds vars ↔
      mode.afterRunTR (fun out => (post out.flow).holds out.vars) result := by
  cases actual with
  | complete fuel result completed =>
    rw [modal_completed mode model program post vars result completed]
    cases mode <;> constructor
    all_goals first
      | (intro after; exact ⟨after, by intro bad; cases bad⟩)
      | (intro after; exact after.1)
  | diverge all =>
    cases mode with
    | box =>
      constructor
      · intro _
        exact ⟨True.intro, by intro bad; cases bad⟩
      · intro _ fuel result completed
        rw [all fuel] at completed
        cases completed
    | diamond =>
      constructor
      · rintro ⟨fuel,result,completed,after⟩
        rw [all fuel] at completed
        cases completed
      · rintro ⟨bad,_⟩
        cases bad

/-- The same divergence criterion is S03's actual least-completion selector
criterion, not a fixed failed execution horizon. -/
theorem diverge_iff_firstDone (model : Model F) (program : Program F c n) (vars : Values n) :
    Run model program vars (.error .diverge) ↔
      ∀ bound, Solidity.Source.firstDone
        (fun fuel => sourceResult (evalStmt fuel model.environment model.words program.code program.words vars))
        bound = none := by
  rw [firstDone_none_iff]
  constructor
  · intro actual
    cases actual with
    | diverge all => exact all
  · intro all
    exact .diverge all

end Solidity.Yul.Logic
