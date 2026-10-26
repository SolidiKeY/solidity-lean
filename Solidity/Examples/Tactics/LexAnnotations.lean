import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Inspect

/-!
# Typed tuple annotations and partial-correctness proofs

The safety proof uses the ordinary invariant after the explicit annotation
erasure step. Successful termination requires the separate source-tuple
certificate demonstrated in `Examples/LexMetrics.lean`.
-/

namespace Solidity.Examples.Tactics.LexAnnotations

open scoped Scoped

def Counter : Contract := contract!{ uint n; }
local instance : InContract := ⟨Counter⟩

def sourceLoop : Prog Counter [] [] := sol[Counter]{
  /// @custom:key invariant true
  /// @custom:key decreases (n, 0)
  while (n > 0) { n−−; }
}

#guard match sourceLoop with
  | .cons (.loop (.invLex _ metrics _ _) _ _) .nil => metrics.toList.length == 2
  | _ => false

#guard match sourceLoop with
  | .cons s .nil => !(s.keyStep .box) && !(s.keyStep .diamond)
  | _ => false

/-- The source tuple does not replace the invariant's ordinary safety proof. -/
theorem ordinaryBox : ⊨ᶠ dl!{ [
    /// @custom:key invariant true
    /// @custom:key decreases (n, 0)
    while (n > 0) { n−−; };
  ] n == 0 } := by
  sol_symex
  sol_close

-- This pin exercises the calculus printer as well as the source printer.
/--
info:   ~[loopLexErase]~>
    dl{ [ /// @custom:key invariant true while (n > 0) {n−−;}; ] find(storage, n) = 0 }
-/
#guard_msgs in
#step dl!{ [
  /// @custom:key invariant true
  /// @custom:key decreases (n, 0)
  while (n > 0) { n−−; };
] n == 0 }

end Solidity.Examples.Tactics.LexAnnotations
