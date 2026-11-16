import Solidity.Correctness.Lowering.Total.Coverage
import Solidity.Correctness.Lowering.Loops.Capture

/-! Checks of `Total.Coverage` against the e1 samples: their raw inputs are
template instances at every state, and the actual producer output quoted by
the while/break probe is the one output `LowersTo` admits there. Raw only: no
elaborated program and no family membership is claimed. -/
namespace Solidity.Correctness.Lowering.Total.Coverage.Checks

section Names
variable [FreshNames]

/-- Each raw input the e1 lane ran through the actual producer
(`Checker.RawProbe.input`, `Loops.Capture`) is a template instance, so `covered`
fixes its output at every scope, state and spelling of fresh names. The return
bodies are taken as given: `calleeBody` renames them first (`renameStmts`). -/
theorem sample_inputs (st : Checker.Snapshot) (slots : List String) :
    (∃ out, Template none Checker.RawProbe.input st out (taken st 1)) ∧
    (∃ out, Template none Loops.Capture.forBreakInput st out (taken st 1)) ∧
    (∃ out, Template none Loops.Capture.forBreakUpdateInput st out (taken st 1)) ∧
    (∃ out, Template none Loops.Capture.whileContinueInput st out (taken st 2)) ∧
    (∃ out, Template none Loops.Capture.whileContinueTailInput st out (taken st 2)) ∧
    (∃ out, Template none Loops.Capture.doBreakInput st out (taken st 2)) ∧
    (∃ out, Template none Loops.Capture.whileResetInput st out (taken st 1)) ∧
    (∃ out, Template none Loops.Capture.doContinueInput st out (taken st 2)) ∧
    (∃ out, Template (some slots) Loops.Capture.whileReturnBody st out (taken st 2)) ∧
    (∃ out, Template (some slots) Loops.Capture.doReturnBody st out (taken st 2)) ∧
    (∃ out, Template (some slots) Loops.Capture.whileReturnThenBody st out (taken st 2)) ∧
    (∃ out, Template (some slots) Loops.Capture.returnFlagBody st out st) :=
  ⟨⟨_, .whileBreak _ _ _ (hasIncDec_assign _ _)⟩, ⟨_, .forBreak _ _ _⟩,
   ⟨_, .forBreakUpdate _ _ _ _ _⟩, ⟨_, .whileContinue _ _ _ _ [] _ (hasIncDec_assign _ _)⟩,
   ⟨_, .whileContinue _ _ _ _ [_] _ (hasIncDec_assign _ _)⟩, ⟨_, .doBreak _ _ _ _ _⟩,
   ⟨_, .whileReset _ _ _ _ _ (hasIncDec_assign _ _)⟩, ⟨_, .doContinue _ _ _ _ [] _⟩,
   ⟨_, .whileReturn _ _ _ (hasIncDec_assign _ _)⟩, ⟨_, .doReturn _ _ _ _ _⟩,
   ⟨_, .whileReturnThen _ _ _ _ _ (hasIncDec_assign _ _)⟩, ⟨_, .returnFlag _ _ _⟩⟩

/-- Every output of the `for`/`break` sample takes exactly one fresh name. -/
theorem forBreak_taken (sc : ElabScope) (st after : Checker.Snapshot) (out : List RawStmt)
    (h : LowersTo none Loops.Capture.forBreakInput out sc st after) : after = taken st 1 :=
  ((covered (.forBreak none _ st) sc out after).mp h).2

end Names

/-- The actual quoted producer output of the e1 while/break probe is the
relation's output at the probed state (and so its only one, `LowersTo.unique`). -/
theorem rawProbe_actual :
    LowersTo none Checker.RawProbe.input Checker.RawProbe.actual.raw Checker.RawProbe.scope
      ⟨(Checker.RawProbe.inputLocals, 1), {}⟩
      ⟨(Checker.RawProbe.actual.locals, Checker.RawProbe.actual.counter),
        Checker.RawProbe.actual.memo⟩ :=
  (Template.whileBreak none (.assign (.name "i") (.name "a"))
    ⟨(Checker.RawProbe.inputLocals, 1), {}⟩ (hasIncDec_assign _ _)).lowers Checker.RawProbe.scope


/-- No other output or outgoing state is admitted at the probed state. -/
theorem rawProbe_only (out : List RawStmt) (after : Checker.Snapshot)
    (h : LowersTo none Checker.RawProbe.input out Checker.RawProbe.scope
      ⟨(Checker.RawProbe.inputLocals, 1), {}⟩ after) :
    out = Checker.RawProbe.actual.raw ∧ after.locals.2 = Checker.RawProbe.actual.counter :=
  ⟨(LowersTo.unique rawProbe_actual h).1.symm,
    congrArg (·.locals.2) (LowersTo.unique rawProbe_actual h).2.symm⟩

end Solidity.Correctness.Lowering.Total.Coverage.Checks
