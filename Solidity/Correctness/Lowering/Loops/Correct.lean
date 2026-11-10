import Solidity.Correctness.Lowering.Loops.WhileBreak
import Solidity.Correctness.Lowering.Loops.Statement
import Solidity.Correctness.Lowering.Loops.Returns
import Solidity.Correctness.Lowering.Loops.ReturnThen
import Solidity.Correctness.Lowering.Loops.ForBreak
import Solidity.Correctness.Lowering.Loops.WhileContinue
import Solidity.Correctness.Lowering.Loops.DoBreak
import Solidity.Correctness.Lowering.Loops.WhileReset
import Solidity.Correctness.Lowering.Loops.DoContinue
import Solidity.Correctness.Lowering.Loops.Capture
import Solidity.Correctness.Lowering.Checker.WhileBreak

/-!
# `lowerLoops_correct`

The generic family statement `Loops.LowerLoopsCorrect`, proved leaf by leaf
(one `Shape`/`RetShape` constructor per covered G19 leaf: nine of the eleven loop
and return-flag leaves; `AssignmentForContinue` and `AssignmentForReturn` are
refused by the pipeline, `Capture.#check_for_continue_refused`), and its connection to the actual
producer: the quoted output of running the real `lowerLoops` and then the real
intrinsic elaborator (`Checker.RawProbe.actual`, `Checker.IntrinsicProbe.actual`)
is accepted by the kernel, and the actual Source typing of the same loop is the
family's Source statement. The producer itself is never unfolded.

Partiality: theorems speak of accepted outputs only. Producer refusals
(`break`/`continue` outside a loop, `return` outside a body, jumps in `try`
inside a loop, Lower.lean:448-449, 455, 474; `lowerReturn` refusals; refusals
of `elabStmtsP` or `SProg.chain`) and non-family outputs are not covered; they
are coverage gaps, not counterexamples. Only normal outcomes are stated. The
producer link is per sample (eleven inputs; the four `return` samples run the
actual callee-body pass `calleeBody`, Arms.lean:826-838, not the call); a raw-level check exists only for
the while sample (`Checker.RawProbe.checkRaw`).
-/
namespace Solidity.Correctness.Lowering

open Solidity.Lowering.V07
open Loops

/-- The normal-outcome family, leaf by leaf. -/
theorem normalFamily_correct : Loops.NormalFamilyCorrect := by
  intro k E srcΓ returns M l u C Γ m p x names output accepted
  cases accepted
  cases k with
  | whileBreak => exact ⟨.drop .refl, WhileBreak.endpoint m p names⟩
  | forBreak => exact ⟨.drop .refl, ForBreak.endpoint m p x names⟩
  | whileContinue => exact ⟨.drop .refl, WhileContinue.endpoint m p x names⟩
  | doBreak => exact ⟨.drop (.drop .refl), DoBreak.endpoint m p x names⟩
  | whileReset => exact ⟨.drop .refl, WhileReset.endpoint m p x names⟩
  | doContinue => exact ⟨.drop .refl, DoContinue.endpoint m p x names⟩

/-- The function-level return family (H497). -/
theorem returnFamily_correct : Loops.ReturnFamilyCorrect := by
  intro k E srcΓ M l u C Γ m p x names
  cases k with
  | whileReturn => exact Returns.whileReturn_endpoint m p x names
  | doReturn => exact Returns.doReturn_endpoint m p x names
  | returnFlag => exact Returns.returnFlag_endpoint m p x names
  | whileReturnThen => exact ReturnThen.endpoint m p x names

/-- **Loop lowering correctness** on both accepted families (finish-line
component `Solidity.Goals.lowerLoopsCorrect`, owner e1-loops). -/
theorem lowerLoops_correct : Loops.LowerLoopsCorrect :=
  ⟨normalFamily_correct, returnFamily_correct⟩

namespace Loops.Coverage

open Checker

/-- Position facts of the concrete caller pair `i, a` used by the probes. -/
def whileBreakPair : Pair Checker.WhileBreak.mapping where
  i := .here
  a := .there .here
  hi := rfl
  ha := rfl
  mapI := rfl
  mapA := rfl

/-- The fresh names the actual producer and elaborator chose. -/
def whileBreakNames : Fresh := ⟨Var.fresh "brk" 1, Var.fresh "se" 2⟩

/-- Kernel acceptance of the actual `lowerLoops` + `elabStmtsP` output for
`while (i = a) break;`. Guards against the family drifting from the producer:
a changed lowering or elaboration makes this `rfl` fail. -/
theorem whileBreak_accepts {E : Source.Env} :
    Accepts (E := E) (returns := []) (M := false) (u := false) .whileBreak whileBreakPair ()
      whileBreakNames IntrinsicProbe.actual.program := rfl

/-- The actual Source typing of the same loop is the family's Source statement. -/
theorem whileBreak_source (E : Source.Env) :
    SourceAssociation.resolved E =
      Shape.whileBreak.source (E := E) (C := IntrinsicProbe.C) (returns := []) (M := false)
        (l := false) (u := false) whileBreakPair () := rfl

/-- End to end for the actual sample: raw producer output accepted by the raw
matcher, intrinsic output accepted by the family, and the endpoint against the
actual resolved Source loop. -/
theorem whileBreak_actual (E : Source.Env) :
    RawProbe.checkRaw RawProbe.input RawProbe.actual.raw 1 = true ∧
    ∃ embedding : Thin IntrinsicProbe.Γ IntrinsicProbe.actual.program.1,
      Endpoint (SourceAssociation.resolved E) Shape.whileBreak.offset
        Checker.WhileBreak.mapping IntrinsicProbe.actual.program.2 embedding := by
  refine ⟨RawProbe.accepts_actual, ?_⟩
  rw [whileBreak_source E]
  exact normalFamily_correct .whileBreak Checker.WhileBreak.mapping whileBreakPair ()
    whileBreakNames IntrinsicProbe.actual.program whileBreak_accepts

/-- Fresh flag of the `for` samples (the initializer needs no capture). -/
def forBreakNames : Fresh := ⟨Var.fresh "brk" 1, Var.fresh "se" 2⟩

/-- Kernel acceptance of the actual output for `for (i = a; ; ) break;`. -/
theorem forBreak_accepts {E : Source.Env} :
    Accepts (E := E) (returns := []) (M := false) (u := false) .forBreak whileBreakPair
      (.none, none) forBreakNames Capture.forBreak := rfl

/-- The lowered update `a = false` the actual elaborator emits. -/
def updateProg : (Δ : Ctx) × Prog IntrinsicProbe.C (.val .bool :: IntrinsicProbe.Γ) Δ :=
  ⟨_, .cons (.assignLocal (Idx.here.there.there) (.simple (.bool false))) .nil⟩

/-- Kernel acceptance of the actual output for `for (i = a; ; a = false) break;`.
The family accepts any Source update with this target update (the update never
runs); `forBreakUpdate_actual` pins the Source update to its actual typing. -/
theorem forBreakUpdate_accepts {E : Source.Env} (post : Source.ROptExpr E [.bool, .bool]) :
    Accepts (returns := []) (M := false) (u := false) .forBreak whileBreakPair
      (post, some updateProg) forBreakNames Capture.forBreakUpdate := rfl

/-- Actual Source typing of `for (i = a; ; a = false) break;`. -/
def forBreakUpdateTyping (E : Source.Env) :
    Source.StmtD (SourceAssociation.typingContext E) SourceAssociation.names
      (.forStmt (l := false) (u := false)
        (.some (.exprStmt (.assign .assign (.ident "i") (.ident "a")))) .none
        (.some (.assign .assign (.ident "a") (.lit (.bool false)))) .breakStmt)
      SourceAssociation.names :=
  .forInit (.expr (SourceAssociation.conditionTyping E) rfl) .none
    (.some (.assign (.loc (i := 1) rfl rfl) (.bool false) rfl rfl)) rfl .brk

/-- Its resolution is a family Source statement, with its actual update. -/
theorem forBreakUpdate_source (E : Source.Env) :
    ∃ post : Source.ROptExpr E [.bool, .bool], (forBreakUpdateTyping E).toR =
      Shape.forBreak.source (C := IntrinsicProbe.C) (returns := []) (M := false) (l := false)
        (u := false) whileBreakPair (post, some updateProg) := ⟨_, rfl⟩

/-- End to end for the actual `for (i = a; ; a = false) break;` sample. -/
theorem forBreakUpdate_actual (E : Source.Env) :
    ∃ embedding : Thin IntrinsicProbe.Γ Capture.forBreakUpdate.1,
      Endpoint (forBreakUpdateTyping E).toR Shape.forBreak.offset
        Checker.WhileBreak.mapping Capture.forBreakUpdate.2 embedding := by
  obtain ⟨post, eq⟩ := forBreakUpdate_source E
  rw [eq]
  exact normalFamily_correct .forBreak Checker.WhileBreak.mapping whileBreakPair
    (post, some updateProg) forBreakNames Capture.forBreakUpdate (forBreakUpdate_accepts post)

/-- Actual Source typing of `for (i = a; ; ) break;`. -/
def forBreakTyping (E : Source.Env) :
    Source.StmtD (SourceAssociation.typingContext E) SourceAssociation.names
      (.forStmt (l := false) (u := false)
        (.some (.exprStmt (.assign .assign (.ident "i") (.ident "a")))) .none .none .breakStmt)
      SourceAssociation.names :=
  .forInit (.expr (SourceAssociation.conditionTyping E) rfl) .none .none rfl .brk

/-- Its resolution is the family's Source statement. -/
theorem forBreak_source (E : Source.Env) :
    (forBreakTyping E).toR =
      Shape.forBreak.source (C := IntrinsicProbe.C) (returns := []) (M := false) (l := false)
        (u := false) whileBreakPair (.none, none) := rfl

/-- Negative control: the association is not trivial; the while family refuses
the actual `for` output (it starts with the initializer, not the flag). -/
theorem whileBreak_refuses_for {E : Source.Env} :
    ¬ Accepts (E := E) (returns := []) (M := false) (u := false) .whileBreak whileBreakPair ()
      whileBreakNames Capture.forBreak := by
  intro h
  cases h

/-- Negative control: the guarded-update variant is refused when no update is
claimed, so the update guard of Lower.lean:515-517 is observed. -/
theorem forBreak_refuses_missing_update {E : Source.Env} :
    ¬ Accepts (E := E) (returns := []) (M := false) (u := false) .forBreak whileBreakPair
      (.none, none) forBreakNames Capture.forBreakUpdate := by
  intro h
  cases h

/-- End to end for the actual `for (i = a; ; ) break;` sample. -/
theorem forBreak_actual (E : Source.Env) :
    ∃ embedding : Thin IntrinsicProbe.Γ Capture.forBreak.1,
      Endpoint (forBreakTyping E).toR Shape.forBreak.offset
        Checker.WhileBreak.mapping Capture.forBreak.2 embedding := by
  rw [forBreak_source E]
  exact normalFamily_correct .forBreak Checker.WhileBreak.mapping whileBreakPair (.none, none)
    forBreakNames Capture.forBreak forBreak_accepts

/-- Fresh names of the `while`/`continue` sample: break flag, capture
(`cnt2` is the continue flag, carried in the shape's extra data). -/
def whileContinueNames : Fresh := ⟨Var.fresh "brk" 1, Var.fresh "se" 3⟩

/-- Kernel acceptance of the actual output for `while (i = a) { a = false; continue; }`. -/
theorem whileContinue_accepts {E : Source.Env} :
    Accepts (E := E) (returns := []) (M := false) (u := false) .whileContinue whileBreakPair
      (Var.fresh "cnt" 2, ⟨_, .nil⟩) whileContinueNames Capture.whileContinue := rfl

/-- The items after `continue` are dropped by the actual producer: with a
non-empty tail `a = true;` the output is the same family member, for every
Source tail (Lower.lean:427). -/
theorem whileContinueTail_accepts {E : Source.Env} {tailΓ : Source.RCtx}
    (tail : Source.RItems E [] false ⟨true, false⟩ [.bool, .bool] tailΓ) :
    Accepts (returns := []) (M := false) (u := false) .whileContinue whileBreakPair
      (Var.fresh "cnt" 2, ⟨_, tail⟩) whileContinueNames Capture.whileContinueTail := rfl

/-- Actual Source typing of `while (i = a) { a = false; continue; }`. -/
def whileContinueTyping (E : Source.Env) :
    Source.StmtD (SourceAssociation.typingContext E) SourceAssociation.names
      (.whileStmt (l := false) (u := false) (.assign .assign (.ident "i") (.ident "a"))
        (.blockStmt (.block (.cons (.stmtItem (.simpleStmt (.exprStmt
          (.assign .assign (.ident "a") (.lit (.bool false))))))
          (.cons (.stmtItem .continueStmt) .nil)))))
      SourceAssociation.names :=
  .whileLoop (SourceAssociation.conditionTyping E) rfl
    (.block (.stmt (.expr (.assign (.loc (i := 1) rfl rfl) (.bool false) rfl rfl) rfl)
      (.stmt .cont .nil)))

/-- Its resolution is the family's Source statement (empty dropped tail). -/
theorem whileContinue_source (E : Source.Env) :
    (whileContinueTyping E).toR =
      Shape.whileContinue.source (C := IntrinsicProbe.C) (returns := []) (M := false)
        (l := false) (u := false) whileBreakPair (Var.fresh "cnt" 2, ⟨_, .nil⟩) := rfl

/-- End to end for the actual `while (i = a) { a = false; continue; }` sample. -/
theorem whileContinue_actual (E : Source.Env) :
    ∃ embedding : Thin IntrinsicProbe.Γ Capture.whileContinue.1,
      Endpoint (whileContinueTyping E).toR Shape.whileContinue.offset
        Checker.WhileBreak.mapping Capture.whileContinue.2 embedding := by
  rw [whileContinue_source E]
  exact normalFamily_correct .whileContinue Checker.WhileBreak.mapping whileBreakPair
    (Var.fresh "cnt" 2, ⟨_, .nil⟩) whileContinueNames Capture.whileContinue whileContinue_accepts

/-- The lowered condition `a` of the `do` sample, read past both flags. -/
def doCondition : Val IntrinsicProbe.C (.val .bool :: .val .bool :: IntrinsicProbe.Γ) .bool :=
  .simple (.local Idx.here.there.there.there)

/-- Kernel acceptance of the actual output for `do { i = a; break; } while (a);`.
The family accepts any Source condition with this lowered one (neither runs);
`doBreak_actual` pins the Source condition to its actual typing. -/
theorem doBreak_accepts {E : Source.Env} (c : Source.RExpr E [.bool, .bool] .bool) :
    Accepts (returns := []) (M := false) (u := false) .doBreak whileBreakPair
      (Var.fresh "first" 2, c, doCondition) whileBreakNames Capture.doBreak := rfl

/-- Actual Source typing of `do { i = a; break; } while (a);`. -/
def doBreakTyping (E : Source.Env) :
    Source.StmtD (SourceAssociation.typingContext E) SourceAssociation.names
      (.doWhile (l := false) (u := false)
        (.blockStmt (.block (.cons (.stmtItem (.simpleStmt (.exprStmt
          (.assign .assign (.ident "i") (.ident "a")))))
          (.cons (.stmtItem .breakStmt) .nil)))) (.ident "a"))
      SourceAssociation.names :=
  .doWhile rfl (.block (.stmt (.expr (SourceAssociation.conditionTyping E) rfl) (.stmt .brk .nil)))
    (.loc (i := 1) rfl rfl)

/-- Its resolution is a family Source statement, with its actual condition. -/
theorem doBreak_source (E : Source.Env) :
    ∃ c : Source.RExpr E [.bool, .bool] .bool, (doBreakTyping E).toR =
      Shape.doBreak.source (C := IntrinsicProbe.C) (returns := []) (M := false) (l := false)
        (u := false) whileBreakPair (Var.fresh "first" 2, c, doCondition) := ⟨_, rfl⟩

/-- End to end for the actual `do { i = a; break; } while (a);` sample. -/
theorem doBreak_actual (E : Source.Env) :
    ∃ embedding : Thin IntrinsicProbe.Γ Capture.doBreak.1,
      Endpoint (doBreakTyping E).toR Shape.doBreak.offset
        Checker.WhileBreak.mapping Capture.doBreak.2 embedding := by
  obtain ⟨c, eq⟩ := doBreak_source E
  rw [eq]
  exact normalFamily_correct .doBreak Checker.WhileBreak.mapping whileBreakPair
    (Var.fresh "first" 2, c, doCondition) whileBreakNames Capture.doBreak (doBreak_accepts c)

/-- Kernel acceptance of the actual output for `while (i = a) a = false;`. -/
theorem whileReset_accepts {E : Source.Env} :
    Accepts (E := E) (returns := []) (M := false) (u := false) .whileReset whileBreakPair ()
      whileBreakNames Capture.whileReset := rfl

/-- Actual Source typing of `while (i = a) a = false;`. -/
def whileResetTyping (E : Source.Env) :
    Source.StmtD (SourceAssociation.typingContext E) SourceAssociation.names
      (.whileStmt (l := false) (u := false) (.assign .assign (.ident "i") (.ident "a"))
        (.simpleStmt (.exprStmt (.assign .assign (.ident "a") (.lit (.bool false))))))
      SourceAssociation.names :=
  .whileLoop (SourceAssociation.conditionTyping E) rfl
    (.expr (.assign (.loc (i := 1) rfl rfl) (.bool false) rfl rfl) rfl)

theorem whileReset_source (E : Source.Env) :
    (whileResetTyping E).toR =
      Shape.whileReset.source (C := IntrinsicProbe.C) (returns := []) (M := false) (l := false)
        (u := false) whileBreakPair () := rfl

/-- End to end for the actual `while (i = a) a = false;` sample. -/
theorem whileReset_actual (E : Source.Env) :
    ∃ embedding : Thin IntrinsicProbe.Γ Capture.whileReset.1,
      Endpoint (whileResetTyping E).toR Shape.whileReset.offset
        Checker.WhileBreak.mapping Capture.whileReset.2 embedding := by
  rw [whileReset_source E]
  exact normalFamily_correct .whileReset Checker.WhileBreak.mapping whileBreakPair ()
    whileBreakNames Capture.whileReset whileReset_accepts

/-- Fresh first-iteration flag of the `do`/`continue` sample. -/
def doContinueNames : Fresh := ⟨Var.fresh "first" 2, Var.fresh "se" 0⟩

/-- Kernel acceptance of the actual output for `do { i = a; continue; } while (false);`. -/
theorem doContinue_accepts {E : Source.Env} :
    Accepts (E := E) (returns := []) (M := false) (u := false) .doContinue whileBreakPair
      (Var.fresh "cnt" 1, ⟨_, .nil⟩) doContinueNames Capture.doContinue := rfl

/-- Actual Source typing of `do { i = a; continue; } while (false);`. -/
def doContinueTyping (E : Source.Env) :
    Source.StmtD (SourceAssociation.typingContext E) SourceAssociation.names
      (.doWhile (l := false) (u := false)
        (.blockStmt (.block (.cons (.stmtItem (.simpleStmt (.exprStmt
          (.assign .assign (.ident "i") (.ident "a")))))
          (.cons (.stmtItem .continueStmt) .nil)))) (.lit (.bool false)))
      SourceAssociation.names :=
  .doWhile rfl (.block (.stmt (.expr (SourceAssociation.conditionTyping E) rfl) (.stmt .cont .nil)))
    (.bool false)

theorem doContinue_source (E : Source.Env) :
    (doContinueTyping E).toR =
      Shape.doContinue.source (C := IntrinsicProbe.C) (returns := []) (M := false) (l := false)
        (u := false) whileBreakPair (Var.fresh "cnt" 1, ⟨_, .nil⟩) := rfl

/-- End to end for the actual `do { i = a; continue; } while (false);` sample. -/
theorem doContinue_actual (E : Source.Env) :
    ∃ embedding : Thin IntrinsicProbe.Γ Capture.doContinue.1,
      Endpoint (doContinueTyping E).toR Shape.doContinue.offset
        Checker.WhileBreak.mapping Capture.doContinue.2 embedding := by
  rw [doContinue_source E]
  exact normalFamily_correct .doContinue Checker.WhileBreak.mapping whileBreakPair
    (Var.fresh "cnt" 1, ⟨_, .nil⟩) doContinueNames Capture.doContinue doContinue_accepts

/-! ### Function-level return samples (H497) -/

def whileReturnNames : RetFresh := ⟨Var.fresh "brk" 1, Var.fresh "ret" 2, Var.fresh "se" 3⟩
def doReturnNames : RetFresh := ⟨Var.fresh "first" 2, Var.fresh "ret" 1, Var.fresh "se" 0⟩
def returnFlagNames : RetFresh := ⟨Var.fresh "se" 1, Var.fresh "se" 0, Var.fresh "se" 0⟩

/-- Kernel acceptance of the actual `calleeBody` + `elabStmtsP` output for
`while (i = a) return;`. -/
theorem whileReturn_accepts {E : Source.Env} :
    RetAccepts (E := E) .whileReturn whileBreakPair () whileReturnNames Capture.whileReturn := rfl

theorem doReturn_accepts {E : Source.Env} (c : Source.RExpr E [.bool, .bool] .bool) :
    RetAccepts .doReturn whileBreakPair (c, doCondition) doReturnNames Capture.doReturn := rfl

theorem returnFlag_accepts {E : Source.Env} :
    RetAccepts (E := E) .returnFlag whileBreakPair () returnFlagNames Capture.returnFlag := rfl

/-- Actual Source typing of `while (i = a) return;`. -/
def whileReturnTyping (E : Source.Env) :
    Source.StmtD (SourceAssociation.typingContext E) SourceAssociation.names
      (.whileStmt (l := false) (u := false) (.assign .assign (.ident "i") (.ident "a"))
        (.returnStmt .none))
      SourceAssociation.names :=
  .whileLoop (SourceAssociation.conditionTyping E) rfl (.ret rfl)

theorem whileReturn_source (E : Source.Env) :
    (whileReturnTyping E).toR =
      RetShape.whileReturn.source (C := IntrinsicProbe.C) (M := false) (l := false) (u := false)
        whileBreakPair () := rfl

/-- Actual Source typing of `do { i = a; return; } while (a);`. -/
def doReturnTyping (E : Source.Env) :
    Source.StmtD (SourceAssociation.typingContext E) SourceAssociation.names
      (.doWhile (l := false) (u := false)
        (.blockStmt (.block (.cons (.stmtItem (.simpleStmt (.exprStmt
          (.assign .assign (.ident "i") (.ident "a")))))
          (.cons (.stmtItem (.returnStmt .none)) .nil)))) (.ident "a"))
      SourceAssociation.names :=
  .doWhile rfl (.block (.stmt (.expr (SourceAssociation.conditionTyping E) rfl)
    (.stmt (.ret rfl) .nil))) (.loc (i := 1) rfl rfl)

theorem doReturn_source (E : Source.Env) :
    ∃ c : Source.RExpr E [.bool, .bool] .bool, (doReturnTyping E).toR =
      RetShape.doReturn.source (C := IntrinsicProbe.C) (M := false) (l := false) (u := false)
        whileBreakPair (c, doCondition) := ⟨_, rfl⟩

/-- Actual Source typing of `if (i = a) return;`. -/
def returnFlagTyping (E : Source.Env) :
    Source.StmtD (k := .body) (SourceAssociation.typingContext E) SourceAssociation.names
      (.ifStmt (.assign .assign (.ident "i") (.ident "a")) (.returnStmt .none) .none)
      SourceAssociation.names :=
  .ifThen (SourceAssociation.conditionTyping E) rfl (.ret rfl)

theorem returnFlag_source (E : Source.Env) :
    (returnFlagTyping E).toR =
      RetShape.returnFlag.source (C := IntrinsicProbe.C) (M := false) (l := false) (u := false)
        whileBreakPair () := rfl

/-- End to end, function level: `while (i = a) return;`. -/
theorem whileReturn_actual (E : Source.Env) :
    RetEndpoint (whileReturnTyping E).toR RetShape.whileReturn.offset
      Checker.WhileBreak.mapping Capture.whileReturn.2 (RetShape.whileReturn.embedding _)
      (RetShape.whileReturn.witness _) := by
  rw [whileReturn_source E]
  exact returnFamily_correct .whileReturn Checker.WhileBreak.mapping whileBreakPair ()
    whileReturnNames

/-- End to end, function level: `do { i = a; return; } while (a);`. -/
theorem doReturn_actual (E : Source.Env) :
    RetEndpoint (doReturnTyping E).toR RetShape.doReturn.offset
      Checker.WhileBreak.mapping Capture.doReturn.2 (RetShape.doReturn.embedding _)
      (RetShape.doReturn.witness _) := by
  obtain ⟨c, eq⟩ := doReturn_source E
  rw [eq]
  exact returnFamily_correct .doReturn Checker.WhileBreak.mapping whileBreakPair
    (c, doCondition) doReturnNames

/-- End to end, function level: `if (i = a) return;`. -/
theorem returnFlag_actual (E : Source.Env) :
    RetEndpoint (returnFlagTyping E).toR RetShape.returnFlag.offset
      Checker.WhileBreak.mapping Capture.returnFlag.2 (RetShape.returnFlag.embedding _)
      (RetShape.returnFlag.witness _) := by
  rw [returnFlag_source E]
  exact returnFamily_correct .returnFlag Checker.WhileBreak.mapping whileBreakPair ()
    returnFlagNames

theorem whileReturnThen_accepts {E : Source.Env} :
    RetAccepts (E := E) .whileReturnThen whileBreakPair () whileReturnNames
      Capture.whileReturnThen := rfl

/-- Actual Source typing of the body `{ while (i = a) return; a = false; }`. -/
def whileReturnThenTyping (E : Source.Env) :
    Source.StmtD (k := .body) (SourceAssociation.typingContext E) SourceAssociation.names
      (.blockStmt (.block (.cons (.stmtItem (.whileStmt (.assign .assign (.ident "i") (.ident "a"))
          (.returnStmt .none)))
        (.cons (.stmtItem (.simpleStmt (.exprStmt
          (.assign .assign (.ident "a") (.lit (.bool false)))))) .nil))))
      SourceAssociation.names :=
  .block (.stmt (.whileLoop (SourceAssociation.conditionTyping E) rfl (.ret rfl))
    (.stmt (.expr (.assign (.loc (i := 1) rfl rfl) (.bool false) rfl rfl) rfl) .nil))

theorem whileReturnThen_source (E : Source.Env) :
    (whileReturnThenTyping E).toR =
      RetShape.whileReturnThen.source (C := IntrinsicProbe.C) (M := false) (l := false)
        (u := false) whileBreakPair () := rfl

/-- End to end, callee-body level: `while (i = a) return; a = false;`. The
suffix runs exactly when Source did not return. -/
theorem whileReturnThen_actual (E : Source.Env) :
    RetEndpoint (whileReturnThenTyping E).toR RetShape.whileReturnThen.offset
      Checker.WhileBreak.mapping Capture.whileReturnThen.2 (RetShape.whileReturnThen.embedding _)
      (RetShape.whileReturnThen.witness _) := by
  rw [whileReturnThen_source E]
  exact returnFamily_correct .whileReturnThen Checker.WhileBreak.mapping whileBreakPair ()
    whileReturnNames

end Loops.Coverage

#print axioms lowerLoops_correct
#print axioms normalFamily_correct
#print axioms returnFamily_correct
#print axioms Loops.Coverage.whileReturn_accepts
#print axioms Loops.Coverage.doReturn_accepts
#print axioms Loops.Coverage.returnFlag_accepts
#print axioms Loops.Coverage.whileReturn_actual
#print axioms Loops.Coverage.doReturn_actual
#print axioms Loops.Coverage.returnFlag_actual
#print axioms Loops.Coverage.whileReturnThen_accepts
#print axioms Loops.Coverage.whileReturnThen_source
#print axioms Loops.Coverage.whileReturnThen_actual
#print axioms Loops.Coverage.whileBreak_accepts
#print axioms Loops.Coverage.whileBreak_source
#print axioms Loops.Coverage.whileBreak_actual
#print axioms Loops.Coverage.forBreak_accepts
#print axioms Loops.Coverage.forBreakUpdate_accepts
#print axioms Loops.Coverage.forBreakUpdate_source
#print axioms Loops.Coverage.forBreakUpdate_actual
#print axioms Loops.Coverage.forBreak_source
#print axioms Loops.Coverage.forBreak_actual
#print axioms Loops.Coverage.whileBreak_refuses_for
#print axioms Loops.Coverage.forBreak_refuses_missing_update
#print axioms Loops.Coverage.whileContinue_accepts
#print axioms Loops.Coverage.whileContinue_source
#print axioms Loops.Coverage.whileContinue_actual
#print axioms Loops.Coverage.whileContinueTail_accepts
#print axioms Loops.Coverage.doBreak_accepts
#print axioms Loops.Coverage.doBreak_source
#print axioms Loops.Coverage.doBreak_actual
#print axioms Loops.Coverage.whileReset_accepts
#print axioms Loops.Coverage.whileReset_source
#print axioms Loops.Coverage.whileReset_actual
#print axioms Loops.Coverage.doContinue_accepts
#print axioms Loops.Coverage.doContinue_source
#print axioms Loops.Coverage.doContinue_actual

end Solidity.Correctness.Lowering
