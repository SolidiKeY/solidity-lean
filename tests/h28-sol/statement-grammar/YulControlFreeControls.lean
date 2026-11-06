import Solidity.Frontend.StatementGrammarH28.YulControlFree
import Solidity.Source.Ctor

/-! Constructor-complete inhabited kernel controls for continuation absence.
These check actual printer outputs, not Yul parser or execution adequacy. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def yulControlCheck {c : Cat} (w : Syn c) : Bool :=
  match w.yield [] with
  | some (parts, []) => !parts.flatten.isEmpty &&
      parts.flatten.all (fun tok => !boundaryToken tok)
  | _ => false

def yulControlExpr : Syn .yulExpr := .yulPath "else" ["catch", "unchecked"]
def yulControlBody : Syn (.list .yulStmt) := .cons .yulLeave .nil

def yulStmtControlWitnesses : List (Syn .yulStmt) :=
  [.yulBlock yulControlBody,
   .yulLet "else" ["catch"] (.some yulControlExpr),
   .yulAssign ["else", "catch"] [["unchecked"]] yulControlExpr,
   .yulExprStmt yulControlExpr,
   .yulIf yulControlExpr yulControlBody,
   .yulFor yulControlBody yulControlExpr yulControlBody yulControlBody,
   .yulSwitch yulControlExpr (.cons (.yulCase (.dec 0) yulControlBody) .nil)
     (.some yulControlBody),
   .yulLeave, .yulBreak, .yulContinue,
   .yulFun "else" ["catch"] ["unchecked"] yulControlBody]

def yulExprControlWitnesses : List (Syn .yulExpr) :=
  [yulControlExpr, .yulCall "else" (.cons yulControlExpr .nil),
   .yulLit (.str [101, 108, 115, 101])]

def yulCaseControlWitnesses : List (Syn .yulCase) :=
  [.yulCase (.bool true) yulControlBody]

theorem yulControl_constructor_inventory :
    yulStmtControlWitnesses.map Syn.ctor =
      [.yulBlock, .yulLet, .yulAssign, .yulExprStmt, .yulIf, .yulFor,
       .yulSwitch, .yulLeave, .yulBreak, .yulContinue, .yulFun] ∧
    yulExprControlWitnesses.map Syn.ctor = [.yulPath, .yulCall, .yulLit] ∧
    yulCaseControlWitnesses.map Syn.ctor = [.yulCase] := by decide +kernel

theorem yulControl_all_constructors_inhabited :
    yulStmtControlWitnesses.all yulControlCheck = true ∧
    yulExprControlWitnesses.all yulControlCheck = true ∧
    yulCaseControlWitnesses.all yulControlCheck = true ∧
    yulStmtControlWitnesses.length + yulExprControlWitnesses.length +
      yulCaseControlWitnesses.length = 15 := by decide +kernel

def yulLiteralControlWitnesses : List (Syn .yulExpr) :=
  [.yulLit (.dec 1), .yulLit (.hex 255), .yulLit (.str [99,97,116,99,104]),
   .yulLit (.hexStr [117,110,99,104,101,99,107,101,100]), .yulLit (.bool false)]

theorem yulControl_all_literal_alternatives :
    yulLiteralControlWitnesses.length = 5 ∧
    yulLiteralControlWitnesses.all yulControlCheck = true := by decide +kernel

theorem yulControl_optional_alternatives :
    yulControlCheck (Syn.yulLet "x" [] .none) = true ∧
    yulControlCheck (Syn.yulSwitch yulControlExpr .nil .none) = true ∧
    yulControlCheck (Syn.yulFun "f" [] [] .nil) = true ∧
    yulControlCheck (Syn.yulCall "f" .nil) = true := by decide +kernel

theorem yulControl_list_option_actual_yields :
    (Syn.nil : Syn (.list .yulStmt)).yield [] = some ([], []) ∧
    (Syn.cons .yulLeave .nil).yield [] = some ([[.yulKw .leave]], []) ∧
    (Syn.none : Syn (.opt .yulExpr)).yield [] = some ([], []) ∧
    (Syn.some (.yulLit (.bool true))).yield [] = some ([[.bool true]], []) := by
  decide +kernel

theorem yulControl_payload_spelling_is_atomic :
    yulControlExpr.yield [] = some
      ([[.ident "else", .punct .period, .ident "catch", .punct .period,
         .ident "unchecked"]], []) ∧
    (Syn.yulLit (.str [101,108,115,101])).yield [] =
      some ([[.str [101,108,115,101]]], []) := by decide +kernel

theorem assemblyControl_all_flag_alternatives :
    ([Syn.assembly (k := .body) false [] yulControlBody,
      Syn.assembly true [] yulControlBody,
      Syn.assembly false ["else", "catch", "unchecked"] yulControlBody,
      Syn.assembly true ["else", "catch", "unchecked"] yulControlBody]).all
      yulControlCheck = true := by decide +kernel

theorem yulControl_actual_keywords_rejected :
    ¬ ControlFree [.kw .else_] ∧ ¬ ControlFree [.kw .catch_] ∧
      ¬ ControlFree [.kw .unchecked] := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    intro h
    exact controlFree_no_boundary h _ rfl (.head _)

theorem yulControl_solidity_stmt_category_rejected :
    YulControlCat (.stmt .body) = false := rfl

theorem yulControl_arbitrary_yul_tree (s : Syn .yulStmt) (L M : List Choice)
    (parts : List (List Tok)) (hy : s.yield L = some (parts, M)) :
    Tok.kw .else_ ∉ parts.flatten ∧ Tok.kw .catch_ ∉ parts.flatten ∧
      Tok.kw .unchecked ∉ parts.flatten :=
  ⟨yul_yield_no_continuations s rfl L M parts hy _ rfl,
   yul_yield_no_continuations s rfl L M parts hy _ rfl,
   yul_yield_no_continuations s rfl L M parts hy _ rfl⟩

#print axioms yulControl_constructor_inventory
#print axioms yulControl_all_constructors_inhabited
#print axioms yulControl_all_literal_alternatives
#print axioms yulControl_optional_alternatives
#print axioms yulControl_list_option_actual_yields
#print axioms yulControl_payload_spelling_is_atomic
#print axioms assemblyControl_all_flag_alternatives
#print axioms yulControl_actual_keywords_rejected
#print axioms yulControl_solidity_stmt_category_rejected
#print axioms yulControl_arbitrary_yul_tree
end Solidity.Frontend.StatementGrammarH28
