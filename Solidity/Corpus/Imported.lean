import Solidity.Corpus.Basic
import Solidity.Calculus.Problem
import Solidity.Solkey.TestSuite

/-!
# The corpus's `TestSuite` is the imported one

solkey's `TestSuite.sol` reaches Lean twice: as the hand-written contract
`TestSuite` (`Syntax.lean`), which the examples write `sol[TestSuite]{ … }`
against, and as `Solkey.TestSuite`, which `solc_import` reads from solc's
AST (`Solidity/Solkey/TestSuite.lean`) and whose obligations are derived by
`⊢` (`Solidity/TestSuite/`).  The corpus now takes its `TestSuite` rows from
the second: `scripts/solkey-port.mjs` no longer translates the source, it
reads `TestSuite/Report.lean`'s pin, and `Corpus/TestSuite.lean` states each
derived obligation at the initial storage as a corollary of its theorem.

**Why the initial storage, and not `State.testSuiteStore`.**  The
corollaries need `wt(storage)` at the store, and `wt` is read over the
imported contract's roots: `testSuiteStore` is the hand-written contract's
store, which has neither `fixedByKey` nor `boolKeyed` and names two roots
differently, so it is no storage of `Solkey.TestSuite`.  Its own initial
state is (`Solkey.TestSuite.initState_wt`).

**The two contracts agree** where they overlap: every root of the
hand-written contract is a root of the imported one, at the same type, up
to two renames (`people` is `folks` and `a` is `aux` there, since those
names mean other things in other contracts).  Struct members need no check:
both contracts read `Semantics.structDef`, and both name solkey's `Triple`
`FixedTriple`.  The imported contract has two roots more (below); `tree`,
the struct recursive through a mapping, is in neither.
-/

namespace Solidity.Corpus

open Semantics

/-- The hand-written `TestSuite`'s names for two of solkey's roots. -/
def testSuiteRenames : List (Name × Name) := [("folks", "people"), ("aux", "a")]

/-- Every root of the hand-written `TestSuite` is a root of the imported
contract, at the same type, after `testSuiteRenames`. -/
theorem testSuite_agrees :
    TestSuite.vars.all (fun (n, T) =>
      lookupBy ((lookupBy n testSuiteRenames).getD n) Solkey.TestSuite.vars == some T) = true := by
  decide +kernel

/-! The roots only the imported contract has: `fixedByKey`, and the
bool-keyed mapping, its key read as a `uint` (solc encodes a bool key as
`0` or `1`). -/

/--
info: [fixedByKey, boolKeyed]
-/
#guard_msgs in
#eval IO.println ((Solkey.TestSuite.vars.filter fun (n, _) =>
  ((testSuiteRenames.map fun (a, b) => (b, a)).lookup n |>.getD n |>
    (lookupBy · TestSuite.vars)).isNone).map (·.1))

/-! ## Obligations at a store, from `⊢` -/

/-- solkey's `\[{ f(); }\](true)` at the store `σ`: `σ ⊨ [ P ] true`. -/
abbrev Box {C : Contract} (σ : State) (P : Prog C) : Prop :=
  holds σ (.modal .box P .tt)

/-- A derived diamond obligation with no parameters holds at every
well-formed store. -/
theorem diamond_of_proved {C : Contract} {σ : State} {P : Prog C}
    (h : Proves .all [] (Problem.fml .diamond [] P)) (hw : holds σ (Fml.wt C)) :
    Diamond σ P :=
  h.valid σ hw

/-- A derived box obligation with no parameters holds at every well-formed
store. -/
theorem box_of_proved {C : Contract} {σ : State} {P : Prog C}
    (h : Proves .all [] (Problem.fml .box [] P)) (hw : holds σ (Fml.wt C)) :
    Box σ P :=
  h.valid σ hw

end Solidity.Corpus
