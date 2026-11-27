import Solidity.Goals.FrontendValidation
namespace Solidity.Examples.Goals.FrontendValidation
open Solidity.Goals
/-- info: open Solidity.Goals.frontendValidatorsExercised ← Solidity.Frontend.validators_exercised plan f1a-frontend-validation-goal -/
#guard_msgs in #roadmap_goal frontendValidatorsExercised
#guard Solidity.Goals.FrontendValidation.validators.length == 269
end Solidity.Examples.Goals.FrontendValidation
