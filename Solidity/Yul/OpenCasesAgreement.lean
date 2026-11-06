import Solidity.Yul.OpenAgreement

namespace Solidity.Yul.OpenRun
open Closed
open OpenFunctions (PureEnvironment)

theorem cases_step (fuel : Nat) (previous : Agreement fuel)
    {F X c n m} (coordinates : Coordinates X n m) (environment : PureEnvironment F)
    (code : Cases F X c n) (policy : Policy.CasesP .A code) (selector : Word) (state : WordState X n) :
    (OpenRun.casesRun (fuel+1) environment code policy selector state).map
        (Option.map (Coordinates.encodeOutcome coordinates)) =
      Closed.evalCases (fuel+1) (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
        (WordAdapter.cases code policy coordinates.locals coordinates.cells).code
        (WordAdapter.cases code policy coordinates.locals coordinates.cells).words selector (coordinates.pack state) := by
  cases code with
  | nil => rfl
  | cons label body rest =>
    rw [WordAdapter.cases]
    change (if selector = label
      then (OpenRun.statement fuel environment body policy.1 state).map some
      else OpenRun.casesRun fuel environment rest policy.2 selector state).map
        (Option.map (Coordinates.encodeOutcome coordinates)) =
      (if selector = label
       then (Closed.evalStmt fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
         (WordAdapter.statement body policy.1 coordinates.locals coordinates.cells).code
         (WordAdapter.statement body policy.1 coordinates.locals coordinates.cells).words
         (coordinates.pack state)).map some
       else Closed.evalCases fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
         (WordAdapter.cases rest policy.2 coordinates.locals coordinates.cells).code
         (WordAdapter.cases rest policy.2 coordinates.locals coordinates.cells).words selector (coordinates.pack state))
    by_cases selected : selector = label
    · rw [if_pos selected,if_pos selected,←previous.statement coordinates environment body policy.1 state]
      cases OpenRun.statement fuel environment body policy.1 state <;> rfl
    · rw [if_neg selected,if_neg selected]
      exact previous.casesRun coordinates environment rest policy.2 selector state

end Solidity.Yul.OpenRun
