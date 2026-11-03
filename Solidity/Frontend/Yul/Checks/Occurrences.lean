import Solidity.Yul.Checks.Occurrences
import Solidity.Frontend.Yul.OccurrenceParse

namespace Solidity.Yul.Checks.Occurrences
open Solidity.Source (Syn)
open Solidity.Yul.Checks.BlockTyping
open Solidity.Frontend.Checked

def parsed : Solidity.Yul.OccurrenceSyntax.Parsed ["x"] ["x"] (ascii text) :=
  ((Solidity.Yul.OccurrenceSyntax.parse ["x"] ["x"] (ascii text)).toOption).get
    (by decide +kernel)
theorem parsed_inhabited : Nonempty (Solidity.Yul.OccurrenceSyntax.Parsed ["x"] ["x"] (ascii text)) :=
  ⟨parsed⟩
example : parsed.parsed.flags = ["memory-safe"] := by decide +kernel
example : (parsed.prepared.run 16).map (fun outcome => outcome.flow.isNormal) =
    some true := by decide +kernel
example : (Solidity.Yul.OccurrenceSyntax.parse ["x"] ["x"]
    (ascii "assembly (\"memory-safe\"){function helper(x)->r{r:=x}}")).isOk = false := by decide +kernel
example : (Solidity.Yul.OccurrenceSyntax.parse ["x"] ["x"]
    (ascii "assembly (\"memory-safe\"){function x(){} function helper(){x()}}")).isOk =
    true := by decide +kernel

end Solidity.Yul.Checks.Occurrences
