import Solidity.Yul.PlacementCheck
set_option Elab.async false
namespace Solidity.Yul.Checks.Placement
open Solidity.Source (Syn)
open Solidity.Yul.Placement

def one (statement : Syn .yulStmt) : Syn (.list .yulStmt) := .cons statement .nil
def loop (pre post body : Syn (.list .yulStmt)) : Syn .yulStmt :=
  .yulFor pre (.yulLit (.dec 0)) post body
def fn (body : Syn (.list .yulStmt)) : Syn .yulStmt := .yulFun "helper" [] [] body
def verdict {α : Type} : Except Error α → Except Error Unit
  | .ok _ => .ok ()
  | .error e => .error e

example : verdict (check rootContext .yulLeave) = .error .leaveOutsideFunction := rfl
example : verdict (check rootContext .yulBreak) = .error .breakOutsideLoop := rfl
example : verdict (check rootContext .yulContinue) = .error .continueOutsideLoop := rfl
example : verdict (check ⟨true, .outside⟩ .yulLeave) = .ok () := rfl
example : verdict (check ⟨false, .body⟩ .yulBreak) = .ok () := rfl
example : verdict (check ⟨false, .body⟩ .yulContinue) = .ok () := rfl
example : verdict (check ⟨false, .init⟩ .yulBreak) = .error .breakInInit := rfl
example : verdict (check ⟨false, .post⟩ .yulBreak) = .error .breakInPost := rfl
example : verdict (check ⟨false, .init⟩ .yulContinue) = .error .continueInInit := rfl
example : verdict (check ⟨false, .post⟩ .yulContinue) = .error .continueInPost := rfl
example : verdict (check rootContext (fn (one .yulLeave))) = .ok () := rfl
example : verdict (check rootContext (fn (one .yulBreak))) = .error .breakOutsideLoop := rfl
example : verdict (check ⟨false, .body⟩ (fn (one .yulBreak))) = .error .breakOutsideLoop := rfl
example : verdict (check rootContext (loop .nil .nil (one .yulBreak))) = .ok () := rfl
example : verdict (check rootContext (loop .nil (one .yulBreak) .nil)) = .error .breakInPost := rfl
example : verdict (check rootContext (loop (one .yulBreak) .nil .nil)) = .error .breakInInit := rfl
example : verdict (check rootContext (loop .nil .nil (one .yulContinue))) = .ok () := rfl
example : verdict (check rootContext (loop .nil (one .yulContinue) .nil)) = .error .continueInPost := rfl
example : verdict (check rootContext (loop (one (fn .nil)) .nil .nil)) = .error .functionInInit := rfl
example : verdict (check rootContext (loop (one (.yulBlock (one (fn .nil)))) .nil .nil)) = .error .functionInInit := rfl
example : verdict (check rootContext
    (loop (one (loop .nil .nil (one (fn .nil)))) .nil .nil)) = .ok () := rfl
example : verdict (check rootContext
    (loop (one (loop .nil (one (fn .nil)) .nil)) .nil .nil)) = .ok () := rfl
example : verdict (check ⟨false, .body⟩ (loop (one .yulBreak) .nil .nil)) = .error .breakInInit := rfl
example : verdict (check ⟨false, .body⟩ (loop .nil (one .yulContinue) .nil)) = .error .continueInPost := rfl
example : verdict (check rootContext (fn (one (loop (one .yulLeave) .nil .nil)))) = .ok () := rfl
example : verdict (check rootContext (loop (one .yulLeave) .nil .nil)) = .error .leaveOutsideFunction := rfl
example : verdict (check rootContext (fn (one (fn (one .yulLeave))))) = .ok () := rfl
example : verdict (check rootContext (.yulIf (.yulLit (.dec 0)) (one .yulBreak))) = .error .breakOutsideLoop := rfl
example : verdict (check rootContext
    (.yulSwitch (.yulLit (.dec 0)) (.cons (.yulCase (.dec 1) (one .yulLeave)) .nil) .none)) =
      .error .leaveOutsideFunction := rfl
example : verdict (check ⟨true, .outside⟩
    (.yulSwitch (.yulLit (.dec 0)) (.cons (.yulCase (.dec 1) (one .yulLeave)) .nil) .none)) = .ok () := rfl
example : verdict (check rootContext (.none (c := .list .yulStmt))) = .ok () := rfl
example : verdict (check rootContext (.yulLit (.dec 0))) = .error .nonYulStatement := rfl
example : verdict (check rootContext (.nil (c := .yulExpr))) = .error .nonYulStatement := rfl
example : verdict (check rootContext (loop .nil (one (fn .nil)) .nil)) = .ok () := rfl
example : verdict (check rootContext (loop .nil .nil
    (.cons (loop .nil .nil (one .yulBreak)) (one .yulBreak)))) = .ok () := rfl
example : verdict (checkBlock (.cons (loop .nil .nil (one .yulBreak)) (one .yulBreak))) =
    .error .breakOutsideLoop := rfl
example : verdict (check rootContext (loop .nil .nil
    (.cons (fn (one .yulLeave)) (one .yulBreak)))) = .ok () := rfl
example : verdict (check rootContext (loop
    (one (loop .nil .nil (one .yulBreak))) .nil .nil)) = .ok () := rfl
example : verdict (check rootContext (loop .nil
    (one (loop .nil .nil (one .yulBreak))) .nil)) = .ok () := rfl
example : verdict (check rootContext (fn (one (loop .nil (one .yulLeave) .nil)))) = .ok () := rfl

example : verdict (check rootContext (loop
    (.cons (loop .nil .nil (one (fn .nil))) (one (fn .nil))) .nil .nil)) =
      .error .functionInInit := rfl
example : verdict (check rootContext (loop .nil
    (.cons (loop .nil .nil (one .yulBreak)) (one .yulBreak)) .nil)) =
      .error .breakInPost := rfl
example : verdict (check rootContext (loop .nil
    (.cons (loop .nil .nil (one .yulBreak)) (one .yulContinue)) .nil)) =
      .error .continueInPost := rfl
example : verdict (check rootContext (loop
    (.cons (loop .nil .nil (one .yulBreak)) (one .yulBreak)) .nil .nil)) =
      .error .breakInInit := rfl

end Solidity.Yul.Checks.Placement
