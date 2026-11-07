import Solidity.Backend.InternalFlow.RuntimeFrameP1Lang
import Solidity.Backend.InternalFlow.RuntimeFrameP1LangV2

/-! Migration between the P1 languages: version 2 → V12's coarse `P1Lang`.

`coarse` forgets events and data, keeping the final class (success or
revert). On both sides the version-2 observation coarsens to the version-1
one: `source_coarse` for every source run, `target_coarse` for every
version-2 outcome against its frozen projection `OutV2.forget`, and
`lift_coarse` for lifted frozen code. Inputs convert both ways
(`Input.toV1` forgets the version-2 fields, `Input.ofV1` adds empty ones),
and `Input.toV1_ofV1` is the identity. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.P1LangV2
open Evm
open Solidity.Roadmap (Event Outcome Prefix)

/-- Forget events and data, keep the final class. -/
def coarse (p : Prefix Event Outcome) : Prefix Event Outcome :=
  ⟨[], p.final.map fun
    | .success _ => .success []
    | .revert _ => .revert []⟩

/-- The source observation coarsens to V12's. -/
theorem source_coarse {C : Contract} {Δ : Ctx} {H : HTy} (r : TRes (Solidity.Out C H Δ)) :
    coarse (sourcePrefix r) = P1Lang.sourcePrefix r := by
  rcases r with e | o
  · cases e <;> rfl
  · rfl

/-- The target observation coarsens to V12's on the frozen projection. -/
theorem target_coarse (self : Fin W) (k : Nat) (o : OutV2) :
    coarse (targetPrefix self k o) = P1Lang.targetPrefix o.forget := by
  cases o with
  | ok m s => cases s <;> rfl
  | ret m d => rfl
  | revert cs d => rfl
  | fault => rfl

/-- Lifted frozen code: the version-2 observation coarsens to V12's
observation of the frozen run. -/
theorem lift_coarse (self : Fin W) (k : Nat) (c : List Instr) (m : MachineV2) :
    coarse (targetPrefix self k (runV2 (lift c) m)) = P1Lang.targetPrefix (run c m.base) := by
  rw [target_coarse, forget_run_lift]

/-- A version-2 input as a V12 input: the frozen machine. -/
def Input.toV1 {C : Contract} {Γ : Ctx} (e : Input C Γ) : P1Lang.Input C Γ :=
  ⟨e.L, e.frame, e.caller, e.base, e.machine.base, e.start⟩

/-- A V12 input as a version-2 input: empty buffer, journal and replies. -/
def Input.ofV1 {C : Contract} {Γ : Ctx} (e : P1Lang.Input C Γ) : Input C Γ :=
  ⟨e.L, e.frame, e.caller, e.base, MachineV2.ofBase e.machine, e.start⟩

@[simp] theorem Input.toV1_ofV1 {C : Contract} {Γ : Ctx} (e : P1Lang.Input C Γ) :
    (Input.ofV1 e).toV1 = e := rfl

/-- On an input from V12, lifted code's version-2 observation coarsens to
V12's target observation of the same input. -/
theorem lift_coarse_ofV1 {C : Contract} {Γ : Ctx} (c : List Instr) (e : P1Lang.Input C Γ) :
    coarse (targetSem (lift c) (Input.ofV1 e)) = P1Lang.targetPrefix (run c e.machine) :=
  lift_coarse _ _ c _

/-- Coarsening loses data: the payload-carrying and bare reverts agree. -/
theorem coarse_forgets_data (d : List UInt8) :
    coarse ⟨[], some (.revert d)⟩ = coarse ⟨[], some (.revert [])⟩ := rfl

end Solidity.Backend.InternalFlow.RuntimeFrame.P1LangV2
