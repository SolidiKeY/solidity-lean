import Solidity.Calculus.Decision

/-! Existing general decision verdict renderer, independent of regression guards. -/
namespace Solidity.Examples.Decision
open Solidity.Decide

def verdict {C : Contract} (φ : Fml C []) : String :=
  match decideGoal φ with
  | .proved => "proved"
  | .refuted _ => "refuted"
  | .unknown => "unknown"

end Solidity.Examples.Decision
