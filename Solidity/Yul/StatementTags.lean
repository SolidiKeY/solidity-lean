import Solidity.Source.Syntax
/-! Constructor tags over existing intrinsic syntax, used only as static
JSON decoder metadata. No syntax/state/value representation is introduced. -/
namespace Solidity.Yul.StatementTags
open Solidity.Source (Syn)
def statement {category} (tree : Syn category) : Option String := by
  apply Syn.casesOn (motive := fun category _ => Option String) tree
  case yulBlock => intros; exact some "YulBlock"
  case yulLet => intros; exact some "YulVariableDeclaration"
  case yulAssign => intros; exact some "YulAssignment"
  case yulExprStmt => intros; exact some "YulExpressionStatement"
  case yulIf => intros; exact some "YulIf"
  case yulFor => intros; exact some "YulForLoop"
  case yulSwitch => intros; exact some "YulSwitch"
  case yulFun => intros; exact some "YulFunctionDefinition"
  case yulBreak => intros; exact some "YulBreak"
  case yulContinue => intros; exact some "YulContinue"
  case yulLeave => intros; exact some "YulLeave"
  all_goals intros; exact none
end Solidity.Yul.StatementTags
