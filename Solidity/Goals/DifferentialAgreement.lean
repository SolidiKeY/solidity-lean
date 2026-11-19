import Solidity.Tools.Goal

/-! The plan goal `differentialAgreement` (`va3-semantic-validation`), one module per goal. -/

namespace Solidity.Goals

open Solidity.Goal

@[goal Solidity.Validation.differential_agreement "va3-semantic-validation"]
def differentialAgreement : Prop := Unstated

end Solidity.Goals
