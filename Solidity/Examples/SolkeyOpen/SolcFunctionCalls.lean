import Solidity.Calculus.Closers
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface

/-!
# solkey open problems: `SolcFunctionCalls`

Source: <https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/semantics/open/SolcFunctionCalls.sol>.
Changes: the unused internal functions dropped; the `else` branch braced.  A function solkey tags `@custom:key box` or specifies has the obligation `spec!{f}`; an untagged
one solkey's diamond, `msg.value == 0 → wt(storage) → ⟨ f(); ⟩ true`.
-/

namespace Solidity.Examples.SolkeyOpen.SolcFunctionCalls

def SolcFunctionCalls : Contract := contract!{
  uint a;
  function functionsRecursiveUnbounded() public {
    if (a > 0) { a = a - 1; functionsRecursiveUnbounded(); } else { assert(a == 0); }
  }
}

local instance : InContract := ⟨SolcFunctionCalls⟩
open scoped Scoped

/-- Unknown: `sol_prove` unfolds the recursion without end (a timeout in its compiled walk, after the
512-step stage) and `sol_refute` finds no witness.  Missing: a rule that closes a recursive call by
induction under `⊢` (`countdownNoPanic`, `Examples/Tactics/Recursion.lean`, proves this countdown's
box by induction over the frames; the diamond also owes termination). -/
def functionsRecursiveUnbounded_obligation : Fml SolcFunctionCalls [] := dl!{ msg.value == 0 → wt(storage) → ⟨ functionsRecursiveUnbounded(); ⟩ true }

end Solidity.Examples.SolkeyOpen.SolcFunctionCalls
