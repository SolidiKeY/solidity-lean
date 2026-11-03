import Solidity.Yul.WordSyntax
import Solidity.Yul.Checks.BlockTyping
set_option Elab.async false
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
def parsed : Solidity.Yul.WordSyntax.Parsed [] (ascii text) :=
  ((Solidity.Yul.WordSyntax.parse [] (ascii text)).toOption).get (by decide +kernel)

example : parsed.parsed.flags = ["memory-safe"] := by decide +kernel
example : (parsed.prepared.run 16).map (fun result => result.flow.isNormal) =
    some true := by decide +kernel

theorem parsed_inhabited : Nonempty (Solidity.Yul.WordSyntax.Parsed [] (ascii text)) := ⟨parsed⟩
example (mode : Solidity.Modality)
    (post : Solidity.Yul.Closed.Flow ClosedSyntax.rootControl → Logic.Fml 0) :
    ∃ premise, Nonempty (Logic.Rule
      (.modal mode Solidity.Yul.WordSyntax.emptyModel parsed.prepared.program post) premise) :=
  parsed.prepared.rule_exists mode post

/-- Preparation is NOT admission. Flags are preserved and Source occurrence
attachment remains unproved, even if outside names were correctly supplied. -/
example : (Solidity.Yul.WordSyntax.parse []
    (ascii "assembly {let x:=7 pop(x)}")).toOption.isSome = true := by decide +kernel
example : (Solidity.Yul.WordSyntax.parse ["x"]
    (ascii "assembly (\"memory-safe\") {function helper(x)->r{r:=x}}")).toOption.isSome =
    true := by decide +kernel

end Solidity.Yul.Checks.WordSyntax
