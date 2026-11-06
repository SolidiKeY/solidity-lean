import Solidity.Yul.Checks.ScopedSyntax
import Solidity.Frontend.Yul.ScopedParse

namespace Solidity.Yul.Checks.ScopedSyntax
open Solidity.Source (Syn)
open Solidity.Yul.Checks.BlockTyping
open Solidity.Frontend.Checked

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
