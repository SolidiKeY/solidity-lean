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
  let ((ss, st'), memo') ← match elaborated with
    | .ok r => pure r
    | .error e => throwError "actual intrinsic elaboration refused the sample: {e}"
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

/-- `while (i = a) { a = false; continue; a = true; }`: a non-empty dropped tail. -/
def whileContinueTailInput : List RawStmt :=
  [.whileLoop {} (.assign (.name "i") (.name "a"))
    [.assign (.name "a") (.bool false), .cont, .assign (.name "a") (.bool true)]]

open Lean Elab Term in
elab "capture_while_continue_tail%" : term => captureProgram whileContinueTailInput

/-- Actual output for `while (i = a) { a = false; continue; a = true; }`. -/
def whileContinueTail : Blk IntrinsicProbe.C IntrinsicProbe.Γ := capture_while_continue_tail%

/-- `for (; i = a; a = false) { continue; }`, the source shape of G19
`AssignmentForContinue`. -/
def forContinueInput : List RawStmt :=
  [.forLoop {} [] (some (.assign (.name "i") (.name "a"))) [.assign (.name "a") (.bool false)] [.cont]]

open Lean Elab Command in
/-- Refusal control: the pipeline refuses `forContinueInput`. `lowerLoops` keeps
an effectful `for` condition in the loop head (the head rewrite of
Lower.lean:493 is for `while` only) and `loopExpr` (Stmt.lean:794-802) refuses
it, so G19 `AssignmentForContinue` has no producer counterpart (G19
`AssignmentForReturn` has the same effectful `for` head and is unreachable for
the same reason). Fails if the pipeline starts accepting this input, or refuses
it for any other reason (the expected `loopExpr` message is matched). -/
elab "#check_for_continue_refused" : command => liftTermElabM do
  let refusal ← try
      discard <| captureProgram forContinueInput
      pure none
    catch e => pure (some (← e.toMessageData.toString))
  match refusal with
  | none => throwError "the pipeline now accepts an effectful for condition; extend the loop family"
  | some msg =>
    unless (msg.splitOn "a loop's condition needs a statement before it").length > 1 do
      throwError "the sample is refused for another reason: {msg}"

#check_for_continue_refused

/-! ### Function-level samples (H497)

`calleeBody` (`Arms.lean:826-838`) is the actual callee-body pass: `lowerLoops`
with the return variables, then `lowerReturns`, modifier wrapping (none here)
and block freshening. Its output is elaborated by `elabStmtsP` in the callee
frame, as `inlinedBody` does; here the frame is the caller pair `i, a`, with
no parameters, no return values and no modifiers. -/

/-- A body with no parameters, return values or modifiers. -/
def bodyDecl (body : List RawStmt) : FunDecl := { params := [], body := body }

open Lean Elab Term Meta in
/-- Run `calleeBody` then `elabStmtsP` and quote the placed program. The
elaborator may leave hidden capture locals in its named context (a statement
capture, `se1`); the caller pair must remain its base. -/
def captureFunction (body : List RawStmt) : TermElabM Expr := do
  let lowered := (((calleeBody IntrinsicProbe.C (bodyDecl body) [] false false
    RawProbe.inputLocals).run RawProbe.scope).run (RawProbe.inputLocals, 1)).run {}
  let ((raw, st), memo) ← match lowered with
    | .ok r => pure r
    | .error e => throwError "actual calleeBody refused the sample: {e}"
  unless memo.starts.isEmpty && memo.bodies.isEmpty do
    throwError "actual calleeBody changed the expected empty memo"
  match st.1 with
  | [("i", .val .bool), ("a", .val .bool)] => pure ()
  | _ => throwError "actual calleeBody changed the caller context"
  let elaborated := (((elabStmtsP IntrinsicProbe.C raw).run RawProbe.scope).run st).run memo
  let ((ss, st'), memo') ← match elaborated with
    | .ok r => pure r
    | .error e => throwError "actual intrinsic elaboration refused the sample: {e}"
  unless memo'.starts.isEmpty && memo'.bodies.isEmpty do
    throwError "actual intrinsic elaboration changed the expected empty memo"
  unless (st'.1.drop (st'.1.length - 2)).map (·.1) == ["i", "a"] do
    throwError "actual intrinsic elaboration lost the caller context"
  let .ok p := SProg.chain (ECtx.toNCtx RawProbe.inputLocals).names IntrinsicProbe.Γ ss |
    throwError "actual intrinsic placement refused the sample"
  let (pe, ge, de) := Prog.quoteShared (mkConst ``IntrinsicProbe.C) p.2
  let family := mkLambda `Δ BinderInfo.default (mkConst ``Ctx)
    (mkAppN (mkConst ``Prog) #[mkConst ``IntrinsicProbe.C, ge, mkBVar 0])
  return mkAppN (mkConst ``Sigma.mk [0,0]) #[mkConst ``Ctx, family, de, pe]

/-- `while (i = a) return;` -/
def whileReturnBody : List RawStmt := [.whileLoop {} (.assign (.name "i") (.name "a")) [.ret none]]

/-- `do { i = a; return; } while (a);` -/
def doReturnBody : List RawStmt :=
  [.doWhile {} [.assign (.name "i") (.name "a"), .ret none] (.name "a")]

/-- `if (i = a) return;` -/
def returnFlagBody : List RawStmt := [.ite (.assign (.name "i") (.name "a")) [.ret none] []]

open Lean Elab Term in
elab "capture_fn_while_return%" : term => captureFunction whileReturnBody
open Lean Elab Term in
elab "capture_fn_do_return%" : term => captureFunction doReturnBody
open Lean Elab Term in
elab "capture_fn_return_flag%" : term => captureFunction returnFlagBody

/-- Actual function-level output for `while (i = a) return;`. -/
def whileReturn : Blk IntrinsicProbe.C IntrinsicProbe.Γ := capture_fn_while_return%
/-- Actual function-level output for `do { i = a; return; } while (a);`. -/
def doReturn : Blk IntrinsicProbe.C IntrinsicProbe.Γ := capture_fn_do_return%
/-- Actual function-level output for `if (i = a) return;`. -/
def returnFlag : Blk IntrinsicProbe.C IntrinsicProbe.Γ := capture_fn_return_flag%

end Solidity.Correctness.Lowering.Loops.Capture
