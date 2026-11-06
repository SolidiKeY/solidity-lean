import Solidity.Source.Syntax

/-! Gate G0 typed list observations. Motives generalise every Syn category;
public views retain the exact element category. No alternate AST is introduced. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source

private def listCellResult : Cat → Type
  | .list c => Option (Syn c × Syn (.list c))
  | _ => PUnit

private def listCellAt {category : Cat} (tree : Syn category) :
    listCellResult category := by
  apply Syn.casesOn (motive := fun category _ => listCellResult category) tree
  case nil => intro category; exact none
  case cons => intro category first rest; exact some (first, rest)
  all_goals intros; exact PUnit.unit

def g0ListCell {c : Cat} (xs : Syn (.list c)) : Option (Syn c × Syn (.list c)) :=
  listCellAt xs

private def listValuesResult : Cat → Type
  | .list c => List (Syn c)
  | _ => PUnit

private def listValuesAt {category : Cat} (tree : Syn category) :
    listValuesResult category := by
  apply Syn.casesOn (motive := fun category _ => listValuesResult category) tree
  case nil => intro category; exact []
  case cons =>
    intro category first rest
    exact first :: listValuesAt rest
  all_goals intros; exact PUnit.unit
termination_by structural tree

def g0ListValues {c : Cat} (xs : Syn (.list c)) : List (Syn c) :=
  listValuesAt xs

private def listLengthAt {category : Cat} (tree : Syn category) : Nat := by
  apply Syn.casesOn (motive := fun _ _ => Nat) tree
  case cons =>
    intro category first rest
    exact listLengthAt rest + 1
  all_goals intros; exact 0
termination_by structural tree

def g0ListLength {c : Cat} (xs : Syn (.list c)) : Nat := listLengthAt xs

theorem g0ListCell_nil {c : Cat} : g0ListCell (Syn.nil (c := c)) = none := rfl

theorem g0ListCell_cons {c : Cat} (x : Syn c) (xs : Syn (.list c)) :
    g0ListCell (.cons x xs) = some (x, xs) := rfl

theorem g0ListValues_nil {c : Cat} : g0ListValues (Syn.nil (c := c)) = [] := rfl

theorem g0ListValues_cons {c : Cat} (x : Syn c) (xs : Syn (.list c)) :
    g0ListValues (.cons x xs) = x :: g0ListValues xs := rfl

theorem g0ListLength_nil {c : Cat} : g0ListLength (Syn.nil (c := c)) = 0 := rfl

theorem g0ListLength_cons {c : Cat} (x : Syn c) (xs : Syn (.list c)) :
    g0ListLength (.cons x xs) = g0ListLength xs + 1 := rfl

end Solidity.Frontend.StatementGrammarH28
