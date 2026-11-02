import Solidity.Frontend.Import
import Solidity.Syntax.LoopWarnings
import Solidity.Tools.ProofTree
import Solidity.Tools.Counterexample
import Solidity.Calculus.Closers

/-!
# Literal-loop notices keep unrolling

The raw/syntax checks exercise diagnostics. The validity and refutation
certificates below independently check that the same literal loop still runs
and has the same result; no option or annotation is inserted by the warning.
-/

namespace Solidity.Examples.Tactics.LoopNotices
open scoped Solidity.Scoped
local instance : InContract := ⟨StandardExample⟩

private def rawLoop (a : RawLoopSpec := {}) : RawStmt :=
  .whileLoop a (.binop .lt (.name "i") (.num 2)) []

#guard RawExpr.literalBound? (.binop .lt (.field (.name "items") "length") (.num 3)) = some "items.length < 3"
#guard RawExpr.literalBound? (.binop .gt (.name "i") (.num 0)) = some "i > 0"
#guard RawExpr.literalBound? (.binop .ge (.name "i") (.unop .neg (.num 1))) = some "i >= -1"
#guard RawExpr.literalBound? (.binop .lt (.num 0) (.name "i")) = some "0 < i"
#guard RawExpr.literalBound? (.binop .and (.name "enabled") (.binop .lt (.name "i") (.num 2))) =
  some "i < 2"
#guard RawExpr.literalBound? (.binop .or (.name "enabled") (.binop .lt (.name "i") (.num 2))) = none
#guard RawExpr.literalBound? (.binop .lt (.name "i") (.name "n")) = none
#guard (rawLoop {}).literalLoop? = some "while (i < 2)"
#guard (rawLoop { inv := [.bool true] }).literalLoop? = none
#guard (rawLoop { qinv := [default] }).literalLoop? = none
#guard (rawLoop { unwind := some 2 }).literalLoop? = none
#guard literalLoopPaths [.whileLoop { inv := [.bool true] } (.bool true) [rawLoop {}]] =
  ["body.0/block0.0: while (i < 2)"]

private def rawCalls : Contract := {
  vars := []
  funs := [
    ("f", { params := [], body := [.call (.name "g") [], .call (.name "g") []] }),
    ("g", { params := [], body := [rawLoop {}, .call (.name "f") []], mods := [{ name := "m", params := [], args := [], body := [rawLoop {}] }] }),
    ("unused", { params := [], body := [rawLoop {}] })]
  ctor := some { params := [], body := [rawLoop {}] } }

#guard calledLiteralLoops rawCalls [.call (.name "f") [], .call (.name "f") []] =
  ["g/body.0: while (i < 2)", "g/modifier0.0: while (i < 2)"]
#guard calledLiteralLoops rawCalls [.call (.name "constructor") []] =
  ["constructor/body.0: while (i < 2)"]
#guard calledLiteralLoops rawCalls [] = []

open Lean Meta in
run_meta do
  let cases : Array (Syntax × Nat) := #[
    ((← `(sol_stmt| while (i < 2) { i++; })), 1),
    ((← `(sol_stmt| while ((i) >= -1) { i−−; })), 1),
    ((← `(sol_stmt| while (0 < i) { i−−; })), 1),
    ((← `(sol_stmt| while (i < 2 && enabled) { i++; })), 1),
    ((← `(sol_stmt| while (i < 2 || enabled) { i++; })), 0),
    ((← `(sol_stmt| for (uint i = 0; i < 2; i++) { })), 1),
    ((← `(sol_stmt| for (uint i = 0; ; i++) { })), 0),
    ((← `(sol_stmt| do { i++; } while (i <= 2))), 1),
    ((← `(sol_stmt| while (i < n) { i++; })), 0),
    ((← `(sol_stmt| while (items.length < 3) { items.push(); })), 1),
    ((← `(sol_stmt| while (i < 2 seconds) { i++; })), 1),
    ((← `(sol_stmt| /// @custom:key invariant i <= 2
      while (i < 2) { i++; })), 0),
    ((← `(sol_stmt| /// @custom:key invariant \forall uint q; q == q
      while (i < 2) { i++; })), 0),
    ((← `(sol_stmt| /// @custom:key unwind 2
      while (i < 2) { i++; })), 0),
    ((← `(sol_stmt| /// @custom:key invariant i <= 2
      while (i < 2) { while (j < 2) { j++; }; i++; })), 1)]
  for (s, count) in cases do
    unless (literalLoopSyntax s).size == count do
      throwError "wrong number of located loop warnings: {s}"

private def LoopCalls : Contract := contract!{
  function f() { uint i = 0; while (i < 2) { i++; }; }
  function g() { f(); f(); }
  function unused() { uint i = 0; while (i < 3) { i++; }; }
  constructor() { uint i = 0; while (i < 1) { i++; }; }
}

private def InitCalls : Contract := contract!{
  uint seed = seeded();
  function seeded() returns (uint r) { r = 0; while (r < 2) { r++; }; }
  constructor() { }
}

/-- warning: unannotated literal-bounded loop `seeded/body.1: while (r < 2)`; keeping symbolic unrolling -/
#guard_msgs in
private def initializerCallee := sol[InitCalls]{ constructor(); }

/-- warning: unannotated literal-bounded loop `f/body.1: while (i < 2)`; keeping symbolic unrolling -/
#guard_msgs in
private def repeatedCallee := sol[LoopCalls]{ g(); g(); }

/-- warning: unannotated literal-bounded loop `constructor/body.1: while (i < 1)`; keeping symbolic unrolling -/
#guard_msgs in
private def constructorCallee := sol[LoopCalls]{ constructor(); }

#guard_msgs in
private def unusedBodySilent := sol[LoopCalls]{ uint x = 0; }

/-- warning: unannotated literal-bounded loop `while (i < 2)`; keeping symbolic unrolling -/
#guard_msgs in
private def directWhile := sol{ uint i = 0; while (i < 2) { i++; }; }

/--
warning: unannotated literal-bounded loop `while (i < 2)`; keeping symbolic unrolling
---
warning: unannotated literal-bounded loop `while (i < 2)`; keeping symbolic unrolling
-/
#guard_msgs in
private def distinctLoops := sol{ uint i = 0; while (i < 2) { i++; }; while (i < 2) { i++; }; }

/-- warning: unannotated literal-bounded loop `while (i < 2)`; keeping symbolic unrolling -/
#guard_msgs in
private def dualReading (m : Modality) : Fml StandardExample [] :=
  dl![m]{ ⟨[ uint i = 0; while (i < 2) { i++; }; ]⟩ i == 2 }

/-- warning: unannotated literal-bounded loop `while (i < 2)`; keeping symbolic unrolling -/
#guard_msgs in
/-- Solidity's literal loop terminates at two; the diamond proof excludes
vacuous success from divergence. -/
theorem exactResult : ⊨ᶠ dl!{ ⟨ uint i = 0; while (i < 2) { i++; }; ⟩ i == 2 } := by
  sol_prove

/-- warning: unannotated literal-bounded loop `while (i < 2)`; keeping symbolic unrolling -/
#guard_msgs in
/-- Solidity's same loop does not return three. -/
theorem wrongResult : ¬ (⊨ᶠ dl!{ ⟨ uint i = 0; while (i < 2) { i++; }; ⟩ i == 3 }) := by
  sol_refute

/--
warning: unannotated literal-bounded loop in imported source `loopNestedReturn/body.0: for (i < 3)`; keeping symbolic unrolling
---
warning: unannotated literal-bounded loop in imported source `loopNestedReturn/body.0/block1.0: for (j < 3)`; keeping symbolic unrolling
---
warning: unannotated literal-bounded loop in imported source `returnBeforeSiblingLoop/body.0: for (solcLocal153 < 3)`; keeping symbolic unrolling
---
warning: unannotated literal-bounded loop in imported source `returnBeforeSiblingLoop/body.1: for (solcLocal172 < 2)`; keeping symbolic unrolling
-/
#guard_msgs in
solc_import "../../../tests/solc/Loops.ast.json" hash 0x499c9a4ed86a4b11 as LoopNoticeImported.Loops

/-- warning: unannotated literal-bounded loop in imported source `constructor/body.1: while (i < 2)`; keeping symbolic unrolling -/
#guard_msgs in
solc_import "../../../tests/automation/LiteralCtorNotice.ast.json" hash 0xa7ef25dc4cfa9c6d as LoopNoticeCtorImported.LiteralCtorNotice

end Solidity.Examples.Tactics.LoopNotices
