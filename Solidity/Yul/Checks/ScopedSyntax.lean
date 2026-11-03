import Solidity.Yul.ScopedSyntax
import Solidity.Yul.Checks.ScopedBlocks
import Solidity.Yul.Checks.WordSyntax
set_option Elab.async false
namespace Solidity.Yul.Checks.ScopedSyntax
open Solidity.Source (Syn)
open Solidity.Yul.Checks.BlockTyping
open Solidity.Frontend.Checked
namespace Before
export Solidity.Yul.Checks.ScopedBlocks (rootScope source witness functionSource functionWitness)
export Solidity.Yul.Checks.ScopedBlocks.Before (types declarations)
end Before

def outside : List String := Before.declarations.map Prod.fst
def localNames : List String := ["a", "m", "f", "cal", "localStore"]
namespace Scalar
def types : List ExternalType := [.value (.unsigned 31)]
def declarations : ExternalNames types := [("x", ⟨_, .here⟩)]
def names : ScopedNames.Checked declarations := ⟨by decide⟩
def scope : BlockScope.Scope types := .external names .root
end Scalar

def verdict {α : Type} : Except Solidity.Yul.ScopedSyntax.Error α → String
  | .ok _ => "prepared"
  | .error .grammar => "grammar"
  | .error .shape => "shape"
  | .error .declarations => "declarations"
  | .error .typing => "typing"
  | .error (.placement _) => "placement"
  | .error (.occurrences (.localCapture name)) => "capture:" ++ name
  | .error (.occurrences _) => "occurrences"
  | .error (.policy (.compilerDependent name)) => "compiler:" ++ name
  | .error (.policy (.needsTier .A)) => "tier:A"
  | .error (.policy (.needsTier .B)) => "tier:B"
  | .error (.policy (.needsTier .C)) => "tier:C"
  | .error (.policy .unsupportedCallcode) => "callcode"
  | .error (.policy .nonMemorySafe) => "safety"
  | .error (.policy (.unknownBuiltin name)) => "unknown:" ++ name

def prepared (tier : Tier) (body : List (Syn .yulStmt)) : String :=
  verdict (Solidity.Yul.ScopedSyntax.prepare Before.rootScope tier outside localNames (list body))

example : prepared .B [decl "copy" (.yulPath "s0" ["slot"])] = "prepared" := by decide
example : prepared .A [decl "copy" (.yulPath "s0" ["slot"])] = "tier:B" := by decide
example : prepared .A [assign "a" (lit 257)] = "prepared" := by decide
example : prepared .B [decl "a" (lit 1)] = "declarations" := by decide
example : prepared .A [fn "helper" ["a"] ["r"] [assign "r" (varExpr "a")]] =
    "capture:a" := by decide
example : prepared .A [fn "helper" [] ["a"] [assign "a" (lit 7)]] = "capture:a" := by decide
example : prepared .A [fn "a" [] [] [], .yulExprStmt (call "a" [])] = "prepared" := by decide
example : prepared .A [fn "helper" [] ["r"] [assign "r" (varExpr "k")]] =
    "prepared" := by decide
example : prepared .B [fn "helper" [] ["r"] [assign "r" (.yulPath "s0" ["slot"])]] =
    "prepared" := by decide
example : prepared .A [fn "helper" [] ["r"] [assign "r" (.yulPath "s0" ["slot"])]] =
    "tier:B" := by decide
example : prepared .A [fn "same" [] [] [], fn "same" [] [] []] = "declarations" := by decide
example : prepared .A [decl "add" (lit 1)] = "declarations" := by decide
example : prepared .A [decl "fresh" (lit 1), block [decl "fresh" (lit 2)]] =
    "declarations" := by decide
example : prepared .A [decl "outer" (lit 1), fn "helper" [] ["r"]
    [assign "r" (varExpr "outer")]] = "typing" := by decide
example : prepared .A [.yulBreak] = "placement" := by decide
example : prepared .A [.yulContinue] = "placement" := by decide
example : prepared .A [.yulLeave] = "placement" := by decide
example : prepared .A [loop [fn "bad" [] [] []] (lit 0) [] []] = "placement" := by decide
example : prepared .A [switch (lit 0) [.dec 0, .dec 0]] = "typing" := by decide
example : prepared .A [decl "loaded" (call "mload" [lit 0])] = "tier:B" := by decide
example : prepared .B [decl "loaded" (call "mload" [lit 0])] = "prepared" := by decide
example : prepared .B [decl "size" (call "returndatasize" [])] = "tier:C" := by decide
example : prepared .C [decl "size" (call "returndatasize" [])] = "prepared" := by decide
example : prepared .C [decl "remaining" (call "gas" [])] = "compiler:gas" := by decide
example : prepared .C [decl "size" (call "msize" [])] = "compiler:msize" := by decide
example : prepared .C [decl "position" (call "pc" [])] = "compiler:pc" := by decide
example : prepared .C [decl "size" (call "codesize" [])] = "compiler:codesize" := by decide
example : prepared .C [.yulExprStmt (call "codecopy" [lit 0, lit 0, lit 0])] =
    "compiler:codecopy" := by decide
example : prepared .C [decl "ok" (call "callcode"
    [lit 0, lit 0, lit 0, lit 0, lit 0, lit 0, lit 0])] = "callcode" := by decide
example : prepared .C [fn "unused" [] ["r"] [assign "r" (call "gas" [])]] =
    "compiler:gas" := by decide
example : prepared .B [fn "helper" [] ["r"] [assign "r" (.yulPath "cal" ["length"])]] =
    "capture:cal.length" := by decide

def openWitness := (Solidity.Yul.ScopedSyntax.prepare Before.rootScope .B outside localNames
  Before.source).toOption.get (by decide)
theorem open_inhabited : Nonempty (Solidity.Yul.ScopedSyntax.Prepared Before.rootScope .B
    outside localNames Before.source) := ⟨openWitness⟩
example : openWitness.typing = Before.witness := openWitness.typing.unique _
example : Solidity.Yul.ScopedSyntax.prepare Before.rootScope .B outside localNames Before.source =
    .ok openWitness := openWitness.complete

def closedSource := list (mulDiv ++ [.yulIf
  (call "iszero" [call "eq" [varExpr "answer", lit 25]])
  (list [loop [] (lit 1) [] []])])
def closedWitness : Solidity.Yul.ScopedSyntax.Prepared .closed .A ["x"] ["x"] closedSource :=
  ((Solidity.Yul.ScopedSyntax.prepare .closed .A ["x"] ["x"] closedSource).toOption).get
    (by decide +kernel)
theorem closed_inhabited :
    Nonempty (Solidity.Yul.ScopedSyntax.Prepared .closed .A ["x"] ["x"] closedSource) := ⟨closedWitness⟩
example : (closedWitness.closedRun 16).map (fun outcome => outcome.flow.isNormal) =
    some true := by decide +kernel
example : Solidity.Yul.WordSyntax.prepare ["x"] closedSource = .ok closedWitness.closedWords :=
  closedWitness.closed_old_result

def text := Solidity.Yul.Checks.WordSyntax.text
def parsed : Solidity.Yul.ScopedSyntax.Parsed .closed .A ["x"] ["x"] (ascii text) :=
  ((Solidity.Yul.ScopedSyntax.parse .closed .A ["x"] ["x"] (ascii text)).toOption).get
    (by decide +kernel)
theorem parsed_inhabited :
    Nonempty (Solidity.Yul.ScopedSyntax.Parsed .closed .A ["x"] ["x"] (ascii text)) := ⟨parsed⟩
example : parsed.parsed.flags = ["memory-safe"] := by decide +kernel
example : (parsed.prepared.closedRun 16).isSome = true := by decide +kernel
/-- Flags are retained here, not admitted; the frontend safety guard is separate. -/
example : (Solidity.Yul.ScopedSyntax.parse .closed .A [] []
    (ascii "assembly {let n:=257 pop(n)}")).isOk = true := by decide +kernel


/-- Original namespace contains x, but its current function projection is
ACTUALLY empty. Word execution/rules therefore require no closed-scope tag. -/
def projectedWitness : Solidity.Yul.ScopedSyntax.Prepared Scalar.scope.function .A
    ["x"] ["x"] closedSource :=
  ((Solidity.Yul.ScopedSyntax.prepare Scalar.scope.function .A ["x"] ["x"] closedSource).toOption).get
    (by decide +kernel)
theorem projected_inhabited : Nonempty (Solidity.Yul.ScopedSyntax.Prepared Scalar.scope.function .A
    ["x"] ["x"] closedSource) := ⟨projectedWitness⟩
example : (projectedWitness.wordRun 16).isSome = true := by decide +kernel
example : closedWitness.wordRun 16 = closedWitness.closedRun 16 := closedWitness.wordRun_closed _
example (mode : Solidity.Modality)
    (post : Closed.Flow ClosedSyntax.rootControl → Logic.Fml 0) :
    ∃ premise, Nonempty (Logic.Rule
      (.modal mode Solidity.Yul.WordSyntax.emptyModel projectedWitness.wordProgram post) premise) :=
  projectedWitness.word_rule_exists mode post

end Solidity.Yul.Checks.ScopedSyntax
