import Solidity.Correctness.Lowering.Loops.WhileBreak
import Solidity.Correctness.Lowering.Loops.ForBreak
import Solidity.Correctness.Lowering.Loops.Capture
import Solidity.Correctness.Lowering.Checker.WhileBreak

/-!
# `lowerLoops_correct`

The generic family statement `Loops.LowerLoopsCorrect`, proved leaf by leaf
(one `Shape` constructor per G19 loop leaf), and its connection to the actual
producer: the quoted output of running the real `lowerLoops` and then the real
intrinsic elaborator (`Checker.RawProbe.actual`, `Checker.IntrinsicProbe.actual`)
is accepted by the kernel, and the actual Source typing of the same loop is the
family's Source statement. The producer itself is never unfolded.

Partiality: theorems speak of accepted outputs only. Producer refusals
(`break`/`continue` outside a loop, `return` outside a body, jumps in `try`
inside a loop, Lower.lean:448-449, 455, 474; `lowerReturn` refusals; refusals
of `elabStmtsP` or `SProg.chain`) and non-family outputs are not covered; they
are coverage gaps, not counterexamples. Only normal outcomes are stated. The
producer link is per sample (three inputs); a raw-level check exists only for
the while sample (`Checker.RawProbe.checkRaw`).
-/
namespace Solidity.Correctness.Lowering

open Solidity.Lowering.V07
open Loops

/-- **Loop lowering correctness** on the accepted family (finish-line component
`Solidity.Goals.lowerLoopsCorrect`, owner e1-loops). -/
theorem lowerLoops_correct : Loops.LowerLoopsCorrect := by
  intro k E srcΓ returns M l u C Γ m p x names output accepted
  cases accepted
  cases k with
  | whileBreak => exact ⟨.drop .refl, WhileBreak.endpoint m p names⟩
  | forBreak => exact ⟨.drop .refl, ForBreak.endpoint m p x names⟩

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
    Accepts (E := E) .whileBreak whileBreakPair () whileBreakNames
      IntrinsicProbe.actual.program := rfl

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
  exact lowerLoops_correct .whileBreak Checker.WhileBreak.mapping whileBreakPair ()
    whileBreakNames IntrinsicProbe.actual.program whileBreak_accepts

/-- Fresh flag of the `for` samples (the initializer needs no capture). -/
def forBreakNames : Fresh := ⟨Var.fresh "brk" 1, Var.fresh "se" 2⟩

/-- Kernel acceptance of the actual output for `for (i = a; ; ) break;`. -/
theorem forBreak_accepts {E : Source.Env} :
    Accepts (E := E) .forBreak whileBreakPair (.none, none) forBreakNames Capture.forBreak := rfl

/-- The lowered update `a = false` the actual elaborator emits. -/
def updateProg : (Δ : Ctx) × Prog IntrinsicProbe.C (.val .bool :: IntrinsicProbe.Γ) Δ :=
  ⟨_, .cons (.assignLocal (Idx.here.there.there) (.simple (.bool false))) .nil⟩

/-- Kernel acceptance of the actual output for `for (i = a; ; a = false) break;`.
The family accepts any Source update with this target update (the update never
runs); `forBreakUpdate_actual` pins the Source update to its actual typing. -/
theorem forBreakUpdate_accepts {E : Source.Env} (post : Source.ROptExpr E [.bool, .bool]) :
    Accepts .forBreak whileBreakPair (post, some updateProg) forBreakNames
      Capture.forBreakUpdate := rfl

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
  exact lowerLoops_correct .forBreak Checker.WhileBreak.mapping whileBreakPair
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
    ¬ Accepts (E := E) .whileBreak whileBreakPair () whileBreakNames Capture.forBreak := by
  intro h
  cases h

/-- Negative control: the guarded-update variant is refused when no update is
claimed, so the update guard of Lower.lean:515-517 is observed. -/
theorem forBreak_refuses_missing_update {E : Source.Env} :
    ¬ Accepts (E := E) .forBreak whileBreakPair (.none, none) forBreakNames
      Capture.forBreakUpdate := by
  intro h
  cases h

/-- End to end for the actual `for (i = a; ; ) break;` sample. -/
theorem forBreak_actual (E : Source.Env) :
    ∃ embedding : Thin IntrinsicProbe.Γ Capture.forBreak.1,
      Endpoint (forBreakTyping E).toR Shape.forBreak.offset
        Checker.WhileBreak.mapping Capture.forBreak.2 embedding := by
  rw [forBreak_source E]
  exact lowerLoops_correct .forBreak Checker.WhileBreak.mapping whileBreakPair (.none, none)
    forBreakNames Capture.forBreak forBreak_accepts

end Loops.Coverage

#print axioms lowerLoops_correct
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

end Solidity.Correctness.Lowering
