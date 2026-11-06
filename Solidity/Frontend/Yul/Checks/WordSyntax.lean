import Solidity.Yul.Checks.WordSyntax
import Solidity.Frontend.Yul.WordParse

namespace Solidity.Yul.Checks.WordSyntax
open Solidity.Source (Syn)
open Solidity.Frontend.Checked
open Solidity.Yul.Checks.BlockTyping

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
