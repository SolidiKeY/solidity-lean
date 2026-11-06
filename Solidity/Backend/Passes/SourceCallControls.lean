import Solidity.Backend.Passes.SourceTypedCall
import Solidity.Source.SemanticsExamples

/-! Inhabited source-execution controls. Existing source fixtures are used as
concrete states and programs; these are kernel runs, not native observations. -/
namespace Solidity.Backend.Passes.SourceCallControls
open Solidity.Source Solidity.Source.SemanticsExamples
open Solidity.Roadmap (Outcome)
open SourceTypedCall

def target : RExpr EB [.address false] (.contract ⟨none, "I"⟩) :=
  .convExplicit (.local .here) (by decide)
def before : Locals EB.layout [.address false] × St EB :=
  (.cons (.address ext) .nil, sB)

def captured : Captured EB [] := ⟨ext, word 0, .nil, selOf "ping()"⟩

/-- Unknown nonself receiver with code: real target/value/argument capture. -/
theorem capture_nonself :
    CapturedAt (GB answerOnly) FC 6 target dPing dPing_sig (lit 0) .nil
      before before captured := by rfl

/-- The factored evaluator actually resumes at this captured source state. -/
theorem nonself_client :
    (evalE (GB answerOnly) FC 7 (.extCall target dPing dPing_sig (lit 0) .nil)).run before =
      (resume (GB answerOnly) FC 6 dPing [] captured).run before :=
  external_captured _ _ _ _ _ _ _ _ _ _ _ capture_nonself

/-- Callbacks are still present: inherited static mode refuses their write. -/
theorem static_reentry :
    let r := runAt (fun n => callAddr (GB reenterOnce) FC n ext (word 0) (selOf "ping()") true) sB 30
    outcomeOf r = some (.success []) ∧ readX r.2 = some 3 ∧
      r.2.events.contains (.reentered (.revert [])) = true := by decide +kernel

/-- Ordinary execution retains the permitted mutating callback. -/
theorem ordinary_reentry :
    let r := runAt (fun n => callAddr (GB reenterOnce) FC n ext (word 0) (selOf "ping()") false) sB 30
    outcomeOf r = some (.success []) ∧ readX r.2 = some 4 ∧ readX r.2 ≠ some 3 := by decide +kernel

/-- Arbitrary failure bytes stay callee failure bytes, with callback rollback. -/
theorem rollback_bytes :
    let r := runAt (fun n => callAddr (GB reenterThenRevert) FC n ext (word 0) (selOf "ping()") false) sB 30
    outcomeOf r = some (.revert [7]) ∧ readX r.2 = some 3 := by decide +kernel

/-- No declared result has no head-length obligation. This does not permit
ignoring a nonempty declaration's malformed result. -/
theorem zero_return :
    (extReturn (E := EB) (Γ := []) [] (.success [1])).run (.nil, sB) =
      (.ok RVal.unit, (.nil, sB)) := by rfl

theorem declared_short :
    (extReturn (E := EB) (Γ := []) [uint] (.success [1])).run (.nil, sB) =
      (.error (.revert []), (.nil, sB)) := by
  rw [SourceCallBoundary.return_short _ _ (by decide)]
  rfl

/-- A declaration actually present in the source environment, with a nonempty
parameter list. The argument converts the old `x++` value to an address. -/
def dCallOut : Decl := ⟨.function, "callOut", some "C", false, fn "callOut" pAddr .nil⟩
theorem callOut_declared : EB.declOf .function ⟨some "C", "callOut"⟩ = some dCallOut := by rfl

def effectArgs : RConvArgs EB [.address false] [.address false] :=
  .cons (.convExplicit (.convExplicit (.incDec true false (.state dX dX_ty rfl))
    (τ := .int IntTy.u160) (by decide)) (τ := .address false) (by decide)) (by decide) .nil

def effectObservation : Option (Nat × Option Int × Bool) :=
  match (capture (GB answerOnly) FC 8
      (.convExplicit (.local .here) (τ := .contract ⟨none, "C"⟩) (by decide))
      dCallOut (lit 0) effectArgs).run before with
  | (.ok c, (_, s)) => some (c.receiver.val, readX s,
      c.input == selOf "callOut(address)" ++ wordBytes (toWord 3))
  | _ => none

/-- Argument mutation precedes the checkpoint. The target stays the previously
captured nonself receiver and calldata contains the old postincrement value. -/
theorem argument_checkpoint : effectObservation = some (ext.val, some 4, true) := by decide +kernel

theorem argument_not_precapture : effectObservation ≠ some (ext.val, some 3, true) := by decide +kernel

end Solidity.Backend.Passes.SourceCallControls
