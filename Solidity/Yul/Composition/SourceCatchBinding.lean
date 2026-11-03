import Solidity.Lowering.Readonly.SourceTryEffects
import Solidity.Source.FailureRuntimeControls

/-!
# Actual Source try/catch bytes binding and canonical rethrow

The statement uses the published intrinsic Source try/catch and rethrow, not
another catch router. The environment's explicit strategy returns the payload;
the actual call, catch allocation and execS rethrow still execute. Heap indices
are logical references, not EVM pointers. This uses the fixture's toy Fixed
hash and proves no compiler, frontend, physical-layout or native correspondence.
The raw Source/session hooks and general Error/Panic selection remain separate.
-/
namespace Solidity.Yul.Composition.SourceCatchBinding
open Solidity.Source Solidity.Source.SemanticsExamples

/-- Existing nonempty heap, fnLocals alias, account journal, logs and event prefix. -/
def input : St EB := Solidity.Source.FailureExecution.RuntimeControls.input

def global (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) : Glob EB :=
  { GB (fun _ => .answer (.revert bytes)) with pipeline := pipeline }

abbrev Ctx : RCtx := [.contract ⟨none,"I"⟩,.bytes .memory,.bool]
def caller : Locals EB.layout Ctx :=
  .cons (.contract ext) Solidity.Source.FailureExecution.RuntimeControls.caller
def target : RExpr EB Ctx (.contract ⟨none,"I"⟩) := .local .here
/-- Success takes a distinguishable poison path: rethrow the OLD alias, not
new catch bytes. The actual revert path rethrows the fresh catch local. -/
def body : RStmt EB [] false .body Ctx Ctx :=
  .tryCall target dPing dPing_sig .nil
    (.stmt (.rethrow (.there .here)) .nil) true (.stmt (.rethrow .here) .nil)

def run (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) (fuel : Nat := 30) :=
  (execS (global pipeline bytes) FC fuel 0 none body caller).run
    (L0 EB,input)

def callState (bytes : Roadmap.Bytes) : St EB :=
  { input with events := input.events ++ [
      .call ext (word 0) (selOf "ping()") false,
      .answer (.revert bytes) none] }

/-- Independently specified owner heap allocation and ordered call/answer events. -/
def expected (bytes : Roadmap.Bytes) : St EB :=
  { input with
    heap := (input.heap.alloc ⟨.bytes .memory,Data.bytes bytes⟩).1
    events := input.events ++ [
      .call ext (word 0) (selOf "ping()") false,
      .answer (.revert bytes) none] }

/-- Actual external-call execution, with complete prefix and world retention. -/
theorem call_run (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) (extra : Nat := 27) :
    (callAddr (global pipeline bytes) FC (extra+2) ext (word 0) (selOf "ping()") false).run
      (L0 EB,input) = (.ok (.revert bytes),(L0 EB,callState bytes)) := rfl

theorem target_run (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) (extra : Nat := 27) :
    (evalE (global pipeline bytes) FC (extra+2) target).run (caller,input) =
      (.ok (.val (.contract ext)),(caller,input)) := rfl

theorem no_system_code (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (instanceAt (global pipeline bytes) ext : EM EB Ctx (Option String)).run
      (caller,input) = (.ok none,(caller,input)) := rfl

theorem environment_has_code (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes)
    (history : List Roadmap.Event) : (global pipeline bytes).hasCode history ext = true := rfl

theorem state_run : (EM.st : EM EB Ctx (St EB)).run (caller,input) =
    (.ok input,(caller,input)) := rfl

theorem ping_not_static :
    (dPing.fnMut == some Mutability.view || dPing.fnMut == some Mutability.pure) = false := by decide

theorem selector_eq (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (global pipeline bytes).selector (sigOf EB.layout dPing.name []) = selOf "ping()" := rfl

/-- Complete actual argument/target/call execution, not a supplied outcome. -/
theorem payload_run : ∀ (extra : Nat) (pipeline : Solidity.Roadmap.Pipeline) (bytes : Solidity.Roadmap.Bytes),
 (Solidity.Lowering.Readonly.SourceHistory.Try.payload (Solidity.Yul.Composition.SourceCatchBinding.global pipeline bytes) Solidity.Source.SemanticsExamples.FC (extra+2) Solidity.Yul.Composition.SourceCatchBinding.target Solidity.Source.SemanticsExamples.dPing .nil).run (Solidity.Yul.Composition.SourceCatchBinding.caller, Solidity.Yul.Composition.SourceCatchBinding.input) = (.ok (.revert bytes), (Solidity.Yul.Composition.SourceCatchBinding.caller, Solidity.Yul.Composition.SourceCatchBinding.callState bytes))
 := by
  intro extra pipeline bytes
  unfold Solidity.Lowering.Readonly.SourceHistory.Try.payload
  dsimp only [bind, ExceptT.bind, StateT.bind]
  dsimp only [ExceptT.run, ExceptT.mk, StateT.bind]
  have ht := Solidity.Yul.Composition.SourceCatchBinding.target_run pipeline bytes (extra := extra)
  dsimp only [ExceptT.run] at ht
  rw [ht]
  dsimp only [bind, pure, Solidity.Source.getV, Solidity.Source.RVal.get, Solidity.Source.EM.lift]
  simp only [Except.pure, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk, StateT.bind, StateT.pure, bind, pure,
    Solidity.Source.evalConvArgs, Solidity.Source.Vals.toR, Solidity.Source.encodeVals,
    Solidity.Source.encodeParts, Solidity.Source.abiLayout, Solidity.Source.abiLayout.go,
    Bool.false_eq_true, if_false, List.nil_append]
  have hc := Solidity.Yul.Composition.SourceCatchBinding.no_system_code pipeline bytes
  dsimp only [ExceptT.run] at hc
  rw [hc]
  have hs := Solidity.Yul.Composition.SourceCatchBinding.state_run
  dsimp only [ExceptT.run] at hs
  have hcall := Solidity.Yul.Composition.SourceCatchBinding.call_run pipeline bytes (extra := extra)
  dsimp only [ExceptT.run, Solidity.Source.SemanticsExamples.word] at hcall
  simp only [ExceptT.bindCont, StateT.bind, bind, hs,
    Solidity.Yul.Composition.SourceCatchBinding.environment_has_code,
    Option.isNone, Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false,
    Solidity.Source.SemanticsExamples.dPing_sig,
    Solidity.Yul.Composition.SourceCatchBinding.ping_not_static,
    List.append_nil, Solidity.Yul.Composition.SourceCatchBinding.selector_eq,
    Solidity.Source.EM.sub, ExceptT.run, ExceptT.mk, StateT.pure,
    pure, hcall]

/-- Actual typed catch allocation and full-byte rethrow at EVERY horizon≥3. -/
theorem run_rethrow_at : ∀ (extra : Nat) (pipeline : Solidity.Roadmap.Pipeline) (bytes : Solidity.Roadmap.Bytes), Solidity.Yul.Composition.SourceCatchBinding.run pipeline bytes (extra+3) = (.error (.revert bytes), (Solidity.Source.L0 Solidity.Source.SemanticsExamples.EB, Solidity.Yul.Composition.SourceCatchBinding.expected bytes))
 := by
  intro extra pipeline bytes
  unfold Solidity.Yul.Composition.SourceCatchBinding.run Solidity.Yul.Composition.SourceCatchBinding.body
  rw [Solidity.Lowering.Readonly.SourceHistory.Try.equation]
  dsimp only [bind, ExceptT.bind, StateT.bind]
  dsimp only [ExceptT.run, ExceptT.mk, StateT.bind, Solidity.Source.EM.sub]
  have hp := Solidity.Yul.Composition.SourceCatchBinding.payload_run extra pipeline bytes
  dsimp only [ExceptT.run] at hp
  rw [hp]
  rfl


theorem run_rethrow (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    run pipeline bytes = (.error (.revert bytes),(L0 EB,expected bytes)) :=
  run_rethrow_at 27 pipeline bytes

theorem completed_horizons_agree (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes)
    (first second : Nat) : run pipeline bytes (first+3) = run pipeline bytes (second+3) :=
  (run_rethrow_at first pipeline bytes).trans (run_rethrow_at second pipeline bytes).symm

theorem fresh_bytes (bytes : Roadmap.Bytes) :
    (heapBytes (E := EB) (Γ := []) 1).run (L0 EB,expected bytes) =
      (.ok bytes,(L0 EB,expected bytes)) := rfl

theorem old_alias_bytes (bytes : Roadmap.Bytes) :
    (heapBytes (E := EB) (Γ := []) 0).run (L0 EB,expected bytes) =
      (.ok [0xDE,0xAD],(L0 EB,expected bytes)) := rfl

theorem scope_state_retained (extra : Nat) (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    let after := (run pipeline bytes (extra+3)).2.2
    after.ex = input.ex ∧ after.logs = input.logs ∧ after.fnLocals = input.fnLocals ∧
      after.resource = input.resource ∧ after.heap.next = 2 := by
  rw [run_rethrow_at]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem same_length_wrong_payload (pipeline : Roadmap.Pipeline) :
    (run pipeline [0xAA,0xBB]).1 = .error (.revert [0xAA,0xBB]) ∧
    (run pipeline [0xAA,0xBB]).1 ≠ .error (.revert [0xDE,0xAD]) := by
  rw [run_rethrow]
  refine ⟨rfl, ?_⟩
  intro h
  have hd : ([0xAA,0xBB] : Roadmap.Bytes) = [0xDE,0xAD] := Halt.revert.inj (Except.error.inj h)
  cases hd

theorem zero_fuel (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    run pipeline bytes 0 = (.error .timeout,(L0 EB,input)) := rfl

theorem one_fuel (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    run pipeline bytes 1 = (.error .timeout,(L0 EB,input)) := rfl

theorem empty_rethrow (pipeline : Roadmap.Pipeline) :
    run pipeline [] = (.error (.revert []),(L0 EB,expected [])) := run_rethrow pipeline []

theorem panic_rethrow (pipeline : Roadmap.Pipeline) :
    run pipeline Solidity.Source.FailureExecution.RuntimeControls.panicBytes =
      (.error (.revert Solidity.Source.FailureExecution.RuntimeControls.panicBytes),
        (L0 EB,expected Solidity.Source.FailureExecution.RuntimeControls.panicBytes)) :=
  run_rethrow pipeline _

theorem exact_ordered_events (extra : Nat) (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (run pipeline bytes (extra+3)).2.2.events = input.events ++ [
      .call ext (word 0) (selOf "ping()") false, .answer (.revert bytes) none] := by
  rw [run_rethrow_at]
  rfl

end Solidity.Yul.Composition.SourceCatchBinding

/-- info: 'Solidity.Yul.Composition.SourceCatchBinding.call_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Composition.SourceCatchBinding.call_run

/-- info: 'Solidity.Yul.Composition.SourceCatchBinding.target_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Composition.SourceCatchBinding.target_run

/-- info: 'Solidity.Yul.Composition.SourceCatchBinding.no_system_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Composition.SourceCatchBinding.no_system_code

/-- info: 'Solidity.Yul.Composition.SourceCatchBinding.environment_has_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Composition.SourceCatchBinding.environment_has_code

/-- info: 'Solidity.Yul.Composition.SourceCatchBinding.state_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Composition.SourceCatchBinding.state_run

/-- info: 'Solidity.Yul.Composition.SourceCatchBinding.ping_not_static' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Composition.SourceCatchBinding.ping_not_static

/-- info: 'Solidity.Yul.Composition.SourceCatchBinding.selector_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Composition.SourceCatchBinding.selector_eq

/-- info: 'Solidity.Yul.Composition.SourceCatchBinding.payload_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Composition.SourceCatchBinding.payload_run

/-- info: 'Solidity.Yul.Composition.SourceCatchBinding.run_rethrow_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Composition.SourceCatchBinding.run_rethrow_at

/-- info: 'Solidity.Yul.Composition.SourceCatchBinding.run_rethrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Composition.SourceCatchBinding.run_rethrow

/-- info: 'Solidity.Yul.Composition.SourceCatchBinding.completed_horizons_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Composition.SourceCatchBinding.completed_horizons_agree

/-- info: 'Solidity.Yul.Composition.SourceCatchBinding.fresh_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Composition.SourceCatchBinding.fresh_bytes

/-- info: 'Solidity.Yul.Composition.SourceCatchBinding.old_alias_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Composition.SourceCatchBinding.old_alias_bytes

/-- info: 'Solidity.Yul.Composition.SourceCatchBinding.scope_state_retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Composition.SourceCatchBinding.scope_state_retained

/-- info: 'Solidity.Yul.Composition.SourceCatchBinding.same_length_wrong_payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Composition.SourceCatchBinding.same_length_wrong_payload

/-- info: 'Solidity.Yul.Composition.SourceCatchBinding.zero_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Composition.SourceCatchBinding.zero_fuel

/-- info: 'Solidity.Yul.Composition.SourceCatchBinding.one_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Composition.SourceCatchBinding.one_fuel

/-- info: 'Solidity.Yul.Composition.SourceCatchBinding.empty_rethrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Composition.SourceCatchBinding.empty_rethrow

/-- info: 'Solidity.Yul.Composition.SourceCatchBinding.panic_rethrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Composition.SourceCatchBinding.panic_rethrow

/-- info: 'Solidity.Yul.Composition.SourceCatchBinding.exact_ordered_events' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Composition.SourceCatchBinding.exact_ordered_events
