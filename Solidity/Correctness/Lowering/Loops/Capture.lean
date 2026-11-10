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

/-- `while (i = a) { a = false; continue; }` -/
def whileContinueInput : List RawStmt :=
  [.whileLoop {} (.assign (.name "i") (.name "a")) [.assign (.name "a") (.bool false), .cont]]

/-- `do { i = a; break; } while (a);` -/
def doBreakInput : List RawStmt :=
  [.doWhile {} [.assign (.name "i") (.name "a"), .brk] (.name "a")]

/-- `while (i = a) a = false;` -/
def whileResetInput : List RawStmt :=
  [.whileLoop {} (.assign (.name "i") (.name "a")) [.assign (.name "a") (.bool false)]]

/-- `do { i = a; continue; } while (false);` -/
def doContinueInput : List RawStmt :=
  [.doWhile {} [.assign (.name "i") (.name "a"), .cont] (.bool false)]

open Lean Elab Term Meta in
/-- Run `lowerLoops` then `elabStmtsP` on `input` and quote the placed program.
Like the Checker probes, it refuses a changed caller context or a nonempty
memo after either stage; the fresh counter is not otherwise checked. -/
def captureProgram (input : List RawStmt) : TermElabM Expr := do
  let lowered := (((lowerLoops none input).run RawProbe.scope).run (RawProbe.inputLocals, 1)).run {}
  let .ok ((raw, st), memo) := lowered | throwError "actual lowerLoops refused the sample"
  unless memo.starts.isEmpty && memo.bodies.isEmpty do
    throwError "actual lowerLoops changed the expected empty memo"
  match st.1 with
  | [("i", .val .bool), ("a", .val .bool)] => pure ()
  | _ => throwError "actual lowerLoops changed the caller context"
  let elaborated := (((elabStmtsP IntrinsicProbe.C raw).run RawProbe.scope).run st).run memo
  let .ok ((ss, st'), memo') := elaborated |
    throwError "actual intrinsic elaboration refused the sample"
  unless memo'.starts.isEmpty && memo'.bodies.isEmpty do
    throwError "actual intrinsic elaboration changed the expected empty memo"
  match st'.1 with
  | [("i", .val .bool), ("a", .val .bool)] => pure ()
  | _ => throwError "actual intrinsic elaboration did not restore the caller context"
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

open Lean Elab Term in
elab "capture_while_continue%" : term => captureProgram whileContinueInput

/-- Actual output for `while (i = a) { a = false; continue; }`. -/
def whileContinue : Blk IntrinsicProbe.C IntrinsicProbe.Γ := capture_while_continue%

open Lean Elab Term in
elab "capture_do_break%" : term => captureProgram doBreakInput

/-- Actual output for `do { i = a; break; } while (a);`. -/
def doBreak : Blk IntrinsicProbe.C IntrinsicProbe.Γ := capture_do_break%

open Lean Elab Term in
elab "capture_while_reset%" : term => captureProgram whileResetInput

open Lean Elab Term in
elab "capture_do_continue%" : term => captureProgram doContinueInput

/-- Actual output for `while (i = a) a = false;`. -/
def whileReset : Blk IntrinsicProbe.C IntrinsicProbe.Γ := capture_while_reset%

/-- Actual output for `do { i = a; continue; } while (false);`. -/
def doContinue : Blk IntrinsicProbe.C IntrinsicProbe.Γ := capture_do_continue%

/-- Actual output for `for (i = a; ; ) break;`. -/
def forBreak : Blk IntrinsicProbe.C IntrinsicProbe.Γ := capture_for_break%

/-- Actual output for `for (i = a; ; a = false) break;`. -/
def forBreakUpdate : Blk IntrinsicProbe.C IntrinsicProbe.Γ := capture_for_break_update%

end Solidity.Correctness.Lowering.Loops.Capture
