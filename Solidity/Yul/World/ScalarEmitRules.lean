import Solidity.Yul.World.ScalarEmitChecks

/-! Lean-only normal-step rules using the existing AdapterRules.Box judgment
and Configuration, with the complete existing Source/physical Carrier as its
memory parameter. This is not intrinsic Yul/G51/dl registration or universal
emit adequacy. Source static error is retained by execute_static; the normal
relation below has no successor in that case. -/
namespace Solidity.Yul.World.ScalarEmitRules
open Solidity.Source
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.ScalarEmitPort

abbrev Configuration (indexed anonymous : Bool) (Γ : RCtx) :=
  AdapterRules.Configuration (Carrier (env indexed anonymous) Γ)
    (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay

def Step {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (static : Bool)
    (before after : Configuration indexed anonymous Γ) : Prop :=
  ∃ shared : before.observed.effects.execution=before.memory.1.1.2.ex,
    execute G static before.memory.1.1 before.memory.1.2 before.memory.2 before.observed shared=
      ((.ok (),after.memory),after.observed)

/-- Exact complete-carrier and complete-observation postcondition. -/
theorem normal_sound {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (before : Configuration indexed anonymous Γ) :
    AdapterRules.Box (Step G false)
      (fun after=>after.memory=⟨⟨ScalarEmitPort.after G before.memory.1.1,before.memory.1.2⟩,before.memory.2⟩ ∧
        after.observed=emitObserved before.observed (encoding G)) before := by
  intro result step
  obtain ⟨shared,ran⟩ := step
  rw [execute_run] at ran
  have pair := Prod.mk.inj ran
  exact ⟨(Prod.mk.inj pair.1).2.symm,pair.2.symm⟩

/-- The actual static Source error is not reclassified as a normal step. -/
theorem static_sound {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (before : Configuration indexed anonymous Γ) :
    AdapterRules.Box (Step G true) (fun _=>False) before := by
  intro result step
  obtain ⟨shared,ran⟩ := step
  rw [execute_static] at ran
  have status := (Prod.mk.inj (Prod.mk.inj ran).1).1
  cases status

/-- Normal Source-extension and actual raw-log transitions have equal FULL
ordered observations on the selected matching input. Raw memory is explicit
and separate, not asserted an arbitrary caller's complete heap view. -/
theorem raw_step_agreement {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (before after : Configuration indexed anonymous Γ) (sourceStep : Step G false before after)
    (rawBefore rawAfter : AdapterRules.Configuration ByteView
      (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (samePrefix : rawBefore.observed=before.observed) (sameMemory : rawBefore.memory=memory G)
    (rawStep : AdapterRules.LogStep PhysicalHeapPort.port false (encoding G).emitter
      (encoding G).count (encoding G).topics 160 (size G) rawBefore rawAfter) :
    after.observed=rawAfter.observed := by
  have source := normal_sound G before after sourceStep
  have raw := rawStep.1
  rw [samePrefix,sameMemory,raw_agreement] at raw
  exact source.2.trans (Option.some.inj raw)

theorem inhabited_step {indexed anonymous} (G : Glob (env indexed anonymous)) :
    Step G false
      ⟨ScalarEmitChecks.observed indexed anonymous,
        ⟨⟨ScalarEmitChecks.caller indexed anonymous,CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩⟩
      ⟨emitObserved (ScalarEmitChecks.observed indexed anonymous) (encoding G),
        ⟨⟨ScalarEmitPort.after G (ScalarEmitChecks.caller indexed anonymous),CallerFrameChecks.residual⟩,CallerFrameChecks.encoding⟩⟩ :=
  ⟨rfl,execute_run G _ _ _ _ rfl⟩

end Solidity.Yul.World.ScalarEmitRules
