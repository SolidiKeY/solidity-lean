import Solidity.Tools.Goal

/-! Finish-line component 2: `Solidity.Backend.compiler_endpoint_correct`, from a typed
program and state to `Evm.run`, with no bytes in the statement (user decision H389;
owner: b1-backend-endpoint). -/

namespace Solidity.Goals

open Solidity.Goal

@[goal Solidity.Backend.compiler_endpoint_correct "b1-backend-endpoint"]
def compilerEndpointCorrect : Prop := Unstated

end Solidity.Goals
