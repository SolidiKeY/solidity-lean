import Solidity.Correctness.Lowering.Checker.IntrinsicProbe

/-!
# Actual producer outputs for the loop family

Each sample runs the real `lowerLoops` (`Lower.lean:543`) and then the real
intrinsic elaborator `elabStmtsP` and placement `SProg.chain`, at elaboration
time, from the Boolean caller context `i, a` of `Checker.RawProbe`, and quotes
the resulting program into a closed term. The kernel never unfolds the
`partial` producer; `Loops.Correct` checks the quoted outputs against the
family. Guards against the family drifting from the producer: a changed
lowering or elaboration changes these terms and breaks the acceptance proofs.
-/
namespace Solidity.Correctness.Lowering.Loops.Capture

open Checker

/-- `for (i = a; ; ) break;` -/
def forBreakInput : List RawStmt :=
  [.forLoop {} [.assign (.name "i") (.name "a")] none [] [.brk]]

/-- `for (i = a; ; a = false) break;` -/
def forBreakUpdateInput : List RawStmt :=
  [.forLoop {} [.assign (.name "i") (.name "a")] none [.assign (.name "a") (.bool false)] [.brk]]

open Lean Elab Term Meta in
/-- Run `lowerLoops` then `elabStmtsP` on `input` and quote the placed program. -/
def captureProgram (input : List RawStmt) : TermElabM Expr := do
  let lowered := (((lowerLoops none input).run RawProbe.scope).run (RawProbe.inputLocals, 1)).run {}
  let .ok ((raw, st), memo) := lowered | throwError "actual lowerLoops refused the sample"
  let elaborated := (((elabStmtsP IntrinsicProbe.C raw).run RawProbe.scope).run st).run memo
  let .ok ((ss, _), _) := elaborated | throwError "actual intrinsic elaboration refused the sample"
  let .ok p := SProg.chain (ECtx.toNCtx RawProbe.inputLocals).names IntrinsicProbe.Γ ss |
    throwError "actual intrinsic placement refused the sample"
  let (pe, ge, de) := Prog.quoteShared (mkConst ``IntrinsicProbe.C) p.2
  let family := mkLambda `Δ BinderInfo.default (mkConst ``Ctx)
    (mkAppN (mkConst ``Prog) #[mkConst ``IntrinsicProbe.C, ge, mkBVar 0])
  return mkAppN (mkConst ``Sigma.mk [0,0]) #[mkConst ``Ctx, family, de, pe]

open Lean Elab Term in
elab "capture_for_break%" : term => captureProgram forBreakInput

open Lean Elab Term in
elab "capture_for_break_update%" : term => captureProgram forBreakUpdateInput

/-- Actual output for `for (i = a; ; ) break;`. -/
def forBreak : Blk IntrinsicProbe.C IntrinsicProbe.Γ := capture_for_break%

/-- Actual output for `for (i = a; ; a = false) break;`. -/
def forBreakUpdate : Blk IntrinsicProbe.C IntrinsicProbe.Γ := capture_for_break_update%

end Solidity.Correctness.Lowering.Loops.Capture
