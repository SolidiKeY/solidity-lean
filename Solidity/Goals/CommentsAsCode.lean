import Solidity.Tools.Goal

/-! The plan goal `commentsAsCode` (`g4-comments-to-code`), one module per goal. -/

namespace Solidity.Goals

open Solidity.Goal

@[goal Solidity.Docs.comments_as_code "g4-comments-to-code"]
def commentsAsCode : Prop := Unstated

end Solidity.Goals
