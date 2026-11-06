import Solidity.Yul.WordSyntax
import Solidity.Yul.Checks.BlockTyping
namespace Solidity.Yul.Checks.WordSyntax
open Solidity.Source (Syn)
open Solidity.Frontend.Checked
open Solidity.Yul.Checks.BlockTyping

def verdict {α : Type} : Except Solidity.Yul.WordSyntax.Error α → String
  | .ok _ => "prepared"
  | .error (.input _) => "input"
  | .error (.policy (.compilerDependent name)) => "compiler:" ++ name
  | .error (.policy (.needsTier .A)) => "tier:A"
  | .error (.policy (.needsTier .B)) => "tier:B"
  | .error (.policy (.needsTier .C)) => "tier:C"
  | .error (.policy .unsupportedCallcode) => "callcode"
  | .error (.policy .nonMemorySafe) => "safety"
  | .error (.policy (.unknownBuiltin name)) => "unknown:" ++ name

def prepared (body : List (Syn .yulStmt)) : String :=
  verdict (Solidity.Yul.WordSyntax.prepare [] (list body))

example : prepared mulDiv = "prepared" := by decide
example : prepared mutualCalls = "prepared" := by decide
example : prepared [decl "x" (call "div" [lit 7, lit 0])] = "prepared" := by decide
example : prepared [decl "x" (varExpr "x")] = "input" := by decide
example : prepared [decl "remaining" (call "gas" [])] = "compiler:gas" := by decide
example : prepared [decl "size" (call "msize" [])] = "compiler:msize" := by decide
example : prepared [decl "position" (call "pc" [])] = "compiler:pc" := by decide
example : prepared [decl "size" (call "codesize" [])] = "compiler:codesize" := by decide
example : prepared [.yulExprStmt (call "codecopy" [lit 0, lit 0, lit 0])] =
    "compiler:codecopy" := by decide
example : prepared [decl "loaded" (call "mload" [lit 0])] = "tier:B" := by decide
example : prepared [.yulExprStmt (call "mstore" [lit 0, lit 7])] = "tier:B" := by decide
example : prepared [decl "ok" (call "callcode"
    [lit 100, lit 0, lit 0, lit 0, lit 0, lit 0, lit 0])] = "callcode" := by decide

/-- Function declarations have no executable statement node, but their REAL
bodies remain in the emitted group and cannot bypass effect/resource checks. -/
example : prepared [fn "unused" [] ["r"] [assign "r" (call "gas" [])]] =
    "compiler:gas" := by decide
example : prepared [fn "unused" [] ["r"] [assign "r" (call "mload" [lit 0])]] =
    "tier:B" := by decide
example : prepared [.yulIf (lit 0) (list [pop (call "gas" [])])] =
    "compiler:gas" := by decide
example : prepared [loop [] (lit 0) [pop (call "codesize" [])] []] =
    "compiler:codesize" := by decide

def text := "assembly (\"memory-safe\") { let answer:=mulDiv(7,11,3) function mulDiv(a,b,d)->r{r:=div(mul(a,b),d)} }"
/-- info: 'Solidity.Yul.ClosedSyntax.Checked.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.ClosedSyntax.Checked.unique

/-- info: 'Solidity.Yul.ClosedSyntax.Checked.finalNames_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.ClosedSyntax.Checked.finalNames_unique

/-- info: 'Solidity.Yul.WordSyntax.Prepared.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.WordSyntax.Prepared.unique

/-- info: 'Solidity.Yul.WordSyntax.Prepared.program_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.WordSyntax.Prepared.program_unique

/-- info: 'Solidity.Yul.WordSyntax.Prepared.run_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.WordSyntax.Prepared.run_unique

end Solidity.Yul.Checks.WordSyntax
