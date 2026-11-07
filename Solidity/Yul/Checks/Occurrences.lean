import Solidity.Yul.OccurrenceSyntax
import Solidity.Yul.Checks.BlockTyping
import Solidity.Yul.Checks.WordSyntax
/-! Occurrence isolation relative to an original Solidity-local name list;
actual identity/provenance and general Source admission remain separate. -/
namespace Solidity.Yul.Checks.Occurrences
open Solidity.Source (Syn)
open Solidity.Yul.Checks.BlockTyping
open Solidity.Frontend.Checked

def isolated {category} (names : List String) (inside : Bool) (term : Syn category) : Bool :=
  (OccurrenceCheck.check names inside term).isOk
def captured {category} (names : List String) (inside : Bool) (term : Syn category) : Option String :=
  match OccurrenceCheck.check names inside term with
  | .error (.localCapture name) => some name
  | _ => none

def paramRead := fn "helper" ["x"] ["r"] [assign "r" (varExpr "x")]
def returnWrite := fn "helper" [] ["x"] [assign "x" (lit 7)]
def helper (body : List (Syn .yulStmt)) := fn "helper" [] [] body

example : isolated ["x"] false paramRead = false := by decide
example : isolated ["x"] false returnWrite = false := by decide
example : captured ["x"] false paramRead = some "x" := by decide
example : captured ["x"] false returnWrite = some "x" := by decide
example : isolated ["x"] false (fn "helper" ["x"] [] []) = true := by decide
example : isolated ["x"] false (fn "helper" [] ["x"] []) = true := by decide
example : isolated ["x"] false (fn "x" [] [] []) = true := by decide
example : isolated ["x"] false (pop (call "x" [])) = true := by decide
example : isolated ["x"] false (helper [pop (call "x" [])]) = true := by decide
example : isolated ["x"] false (fn "helper" ["msg"] ["r"] [assign "r" (varExpr "msg")]) =
    true := by decide
example : isolated ["x"] false (pop (varExpr "x")) = true := by decide
example : isolated ["x"] false (assign "x" (lit 7)) = true := by decide
example : isolated ["x"] false (helper [pop (varExpr "x")]) = false := by decide
example : isolated ["x"] false (helper [assign "x" (lit 7)]) = false := by decide
example : isolated ["x"] false (helper [pop (.yulPath "x" ["slot"])]) = false := by decide
example : captured ["x"] false (helper [pop (.yulPath "x" ["slot"])]) = some "x.slot" := by decide
example : isolated ["x"] true (.yulPath "x" ["address"]) = false := by decide
example : isolated ["x"] true (.yulPath "x" ["unknown"]) = true := by decide
example : isolated ["x"] true (.yulPath "x" ["slot", "offset"]) = true := by decide
example : isolated ["x.slot"] true (.yulPath "x" ["slot"]) = false := by decide
example : isolated [] true (varExpr "x") = true := by decide
example : isolated ["x"] true (varExpr "missing") = true := by decide
example : isolated ["x"] true (call "x" [lit 1]) = true := by decide
example : isolated ["x"] true (call "helper" [varExpr "x"]) = false := by decide
example : isolated ["x"] false (helper [pop (call "add" [lit 1, varExpr "x"])]) = false := by decide
example : isolated ["x"] false (helper [decl "own" (varExpr "x")]) = false := by decide
example : isolated ["x"] false (helper [.yulIf (varExpr "x") .nil]) = false := by decide
example : isolated ["x"] false (helper [loop [pop (varExpr "x")] (lit 0) [] []]) = false := by decide
example : isolated ["x"] false (helper [loop [] (varExpr "x") [] []]) = false := by decide
example : isolated ["x"] false (helper [loop [] (lit 0) [assign "x" (lit 1)] []]) = false := by decide
example : isolated ["x"] false (helper [loop [] (lit 0) [] [pop (varExpr "x")]]) = false := by decide
example : isolated ["x"] false (helper [.yulSwitch (varExpr "x") .nil .none]) = false := by decide
example : isolated ["x"] false (helper [.yulSwitch (lit 0)
    (.cons (.yulCase (.dec 0) (list [pop (varExpr "x")])) .nil) .none]) = false := by decide
example : isolated ["x"] false (helper [.yulSwitch (lit 0) .nil
    (.some (list [pop (varExpr "x")]))]) = false := by decide
example : isolated ["x"] false (helper [fn "nested" ["x"] ["r"] [assign "r" (varExpr "x")]]) =
    false := by decide
example : isolated ["x"] false (helper [fn "nested" [] [] [], pop (varExpr "x")]) = false := by decide

/-- Empty malformed paths have no occurrence; AssignmentCheck still refuses
their shape. This component makes neither shape nor reference-resolution claims. -/
example : (OccurrenceCheck.checkPaths ["x"] true [[]]).isOk = true := by decide
example : (OccurrenceCheck.checkPaths ["x"] true [["own"], ["x"]]).isOk = false := by decide
example : (OccurrenceCheck.checkPaths ["x"] true [["x", "length"]]).isOk = false := by decide
example : isolated ["x"] false (Syn.lit (.bool true)) = false := by decide

example : (Solidity.Yul.WordSyntax.prepare ["x"] (list [paramRead])).isOk = true := by decide
example : (Solidity.Yul.OccurrenceSyntax.prepare ["x"] ["x"] (list [paramRead])).isOk =
    false := by decide
example : (Solidity.Yul.OccurrenceSyntax.prepare ["x"] [] (list [paramRead])).isOk =
    true := by decide

def witness : Solidity.Yul.OccurrenceSyntax.Prepared ["x"] ["x"] (list mulDiv) :=
  ((Solidity.Yul.OccurrenceSyntax.prepare ["x"] ["x"] (list mulDiv)).toOption).get
    (by decide +kernel)
theorem inhabited : Nonempty (Solidity.Yul.OccurrenceSyntax.Prepared ["x"] ["x"] (list mulDiv)) :=
  ⟨witness⟩
example : (witness.run 16).map (fun outcome => outcome.flow.isNormal) = some true := by decide +kernel
example : Solidity.Yul.WordSyntax.prepare ["x"] (list mulDiv) = .ok witness.words := witness.old_result

def text := Solidity.Yul.Checks.WordSyntax.text
/-- info: 'Solidity.Yul.OccurrenceSyntax.Prepared.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.OccurrenceSyntax.Prepared.unique

/-- info: 'Solidity.Yul.OccurrenceSyntax.Prepared.run_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.OccurrenceSyntax.Prepared.run_unique

end Solidity.Yul.Checks.Occurrences
