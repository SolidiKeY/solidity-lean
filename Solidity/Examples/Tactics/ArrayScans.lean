import Solidity.Frontend.Import
import Solidity.Frontend.Problems
import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# ABI element ranges through invariant loops

These source functions are compiled by the pinned solc. The unsigned and
signed element bounds come from the imported ABI premise, rather than a
user-written quantified precondition. The counters are introduced after
that premise. The loops supply invariants; the diamond also supplies a variant.
-/

solc_import "../../../tests/solc/ArrayScans.ast.json" hash 0x6a9a6e55b03f66f4 as Solc.ArrayScans
/-- info: 3 obligations declared scoped -/
#guard_msgs in
solc_scoped_problems Solc.ArrayScans

namespace Solidity.Examples.Tactics.ArrayScans
open scoped Solidity.Scoped

/-- A box scan uses the unsigned ABI element bound at each later counter. -/
theorem unsignedScan : ⊨ᶠ Solc.ArrayScans.unsignedScan.problem := by
  sol_prove
  all_goals sol_leaf
  all_goals sol_close

/-- The diamond checks both signed bounds and termination. Keeping its weakest
precondition together avoids repeated expansion in separate walk leaves. -/
theorem signedScan : ⊨ᶠ Solc.ArrayScans.signedScan.problem := by
  sol_symex
  sol_close

/-- A box scan checks the signed ABI upper bound at each later counter. -/
theorem signedUpperScan : ⊨ᶠ Solc.ArrayScans.signedUpperScan.problem := by
  sol_prove
  all_goals sol_leaf
  all_goals sol_close

end Solidity.Examples.Tactics.ArrayScans
