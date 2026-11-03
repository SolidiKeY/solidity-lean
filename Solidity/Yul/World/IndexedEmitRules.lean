import Solidity.Yul.World.IndexedEmitChecks

/-! Lean-only rules for the existing complete-carrier Box and LogStep.
This is not a new Yul/G51 embedding or universal G01 soundness theorem. -/
namespace Solidity.Yul.World.IndexedEmitRules
open Solidity.Source
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.IndexedEmitPort
open Solidity.Yul.World.ScalarEmitPort (env)

abbrev Configuration (indexed anonymous : Bool) (Δ : RCtx) :=
  AdapterRules.Configuration (Carrier (env indexed anonymous) Δ)
    (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay

def Step {indexed anonymous Γ Δ} (G : Glob (env indexed anonymous)) (static : Bool)
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint)
    (before after : Configuration indexed anonymous Δ) : Prop :=
  ∃ shared : before.observed.effects.execution=before.memory.1.1.2.ex,
    execute G static l i before.memory.1.1 before.memory.1.2 before.memory.2 before.observed shared=
      ((.ok (),after.memory),after.observed)

theorem normal_sound {indexed anonymous Γ Δ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint)
    (before : Configuration indexed anonymous Δ) :
    AdapterRules.Box (Step G false l i)
      (fun after=>after.memory=⟨⟨ScalarLocalEmit.after G (selected l i) before.memory.1.1,before.memory.1.2⟩,before.memory.2⟩ ∧
        after.observed=emitObserved before.observed (encoding G l i)) before := by
  intro result step
  obtain ⟨shared,ran⟩ := step
  rw [execute_run] at ran
  have pair:=Prod.mk.inj ran
  exact ⟨(Prod.mk.inj pair.1).2.symm,pair.2.symm⟩

theorem static_sound {indexed anonymous Γ Δ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint)
    (before : Configuration indexed anonymous Δ) :
    AdapterRules.Box (Step G true l i) (fun _=>False) before := by
  intro result step
  obtain ⟨shared,ran⟩ := step
  rw [execute_static] at ran
  have status:=(Prod.mk.inj (Prod.mk.inj ran).1).1
  cases status

/-- Actual byte equality plus bounds discharge raw memory loading. The full
ordered observations are equal, not only their event/log projections. -/
theorem raw_step_agreement {indexed anonymous Γ Δ} (G : Glob (env indexed anonymous))
    (l : Locals (env indexed anonymous).layout Γ) (i : Source.Idx Γ ReturningCall.uint)
    (before after : Configuration indexed anonymous Δ) (sourceStep : Step G false l i before after)
    (rawBefore rawAfter : AdapterRules.Configuration ByteView
      (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (samePrefix : rawBefore.observed=before.observed) (offset count : Roadmap.Word)
    (range : offset.val+count.val≤2^256)
    (bytes : readBytes rawBefore.memory offset.val count.val=(encoding G l i).data)
    (rawStep : AdapterRules.LogStep PhysicalHeapPort.port false (encoding G l i).emitter
      (encoding G l i).count (encoding G l i).topics offset count rawBefore rawAfter) :
    after.observed=rawAfter.observed := by
  have source:=normal_sound G l i before after sourceStep
  have raw:=rawStep.1
  rw [IndexedEmitMemory.raw_matched G l i _ _ _ _ range bytes,samePrefix] at raw
  exact source.2.trans (Option.some.inj raw)

theorem inhabited_step {indexed anonymous} (G : Glob (env indexed anonymous)) :
    Step G false (IndexedEmitChecks.inputs indexed anonymous) IndexedEmitChecks.index
      ⟨ScalarEmitChecks.observed indexed anonymous,⟨⟨ScalarEmitChecks.caller indexed anonymous,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩⟩
      ⟨emitObserved (ScalarEmitChecks.observed indexed anonymous) (encoding G (IndexedEmitChecks.inputs indexed anonymous) IndexedEmitChecks.index),
        ⟨⟨ScalarLocalEmit.after G ReturningCall.value (ScalarEmitChecks.caller indexed anonymous),CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩⟩ :=
  ⟨rfl,execute_run G _ _ _ _ _ _ rfl⟩

end Solidity.Yul.World.IndexedEmitRules
