import Solidity.Tools.Goal

/-! The plan goal `docLintClean` (`g2-doc-lint`), one module per goal. -/

namespace Solidity.Goals

open Solidity.Goal

@[goal Solidity.Docs.lint_clean "g2-doc-lint"]
def docLintClean : Prop := Unstated

end Solidity.Goals
