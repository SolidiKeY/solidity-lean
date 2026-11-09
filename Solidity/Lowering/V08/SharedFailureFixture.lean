import Solidity.Semantics.Run

/-! Shared failure extraction for V08 control fixtures. -/
namespace Solidity.Lowering.V08.SharedFailureFixture
open Solidity

theorem extract_failure {α : Type} (run : TRes α) (halt : THalt)
    (checked : run.halt? = some halt) : run = .error halt := by
  cases run with
  | ok value => cases checked
  | error actual =>
    have same : actual = halt := Option.some.inj checked
    cases same
    rfl

end Solidity.Lowering.V08.SharedFailureFixture
