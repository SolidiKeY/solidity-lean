import Solidity.Goals.LoweringSession
import Solidity.Correctness.Lowering.Sim.Session.Backward

/-! The per-frame obligations of the forward session diagram (plan step
`ls2s-session-diagrams`, lane forward), and the session-level match they give.

`MatchedFrames D F P c e` is what the forward diagram needs of every frame of a
session of `P` in `e` against the lowered world of `c`: the deployment and
every action started from related boundaries reach related boundaries with
the same events, and a Source frame that does not complete shows no event.
Its invariant `Inv` implies the `D.globRel` clause of
`Shrink.Lowering.Agrees`. Nothing here derives `MatchedFrames` from
`Diagram.Simulates`; see `Session/Forward.lean`, "What is not proved".

**Provisional (H1199).** `MatchedFrames` is not frozen: the binding lane may
prototype against it, and its fields may change once the v2 statements (the
session lift with `F := P.fixed` and elaboration receipts, the Source session
at instance-less addresses) are settled. -/
namespace Solidity.Correctness.Lowering.Sim.Session

open Solidity.Roadmap (Event Outcome SessionEnv Fixed)
open Solidity.Correctness.Sim (Machine)
open Solidity.Semantics.IntrinsicSession (wire lastOutcome)
open Solidity.Goals.Shrink.Lowering (Compilation loweredCode loweredWorld boundaryState)
open Solidity.Lowering.V08.EnvironmentProjection (liftAddress)
open Solidity.ContractWorld (World)

variable [FreshNames] {E : Solidity.Source.Env}

/-- A boundary world of the lowered code of `c`. -/
abbrev LoweredWorld (c : Compilation) : Type :=
  World (Solidity.Semantics.IntrinsicSession.catalog (loweredCode c).contracts)

/-- The deployment of the lowered world, without resource failure. -/
noncomputable abbrev targetDeploy (F : Fixed) (c : Compilation) (e : SessionEnv) :=
  Solidity.Semantics.IntrinsicSession.deploy (loweredCode c).main (loweredCode c).roles
    (loweredCode c).ctor F wire { horizon := 0 } e

/-- One action of the lowered world, without resource failure. -/
noncomputable abbrev targetStep (F : Fixed) (c : Compilation) (e : SessionEnv) (h : List Event)
    (i : Nat) (w : LoweredWorld c) (a : Solidity.Roadmap.Action) :=
  Solidity.Semantics.IntrinsicSession.step (loweredCode c).entry F wire { horizon := 0 } e h i w a

/-- **The frames of a session are matched**: an invariant between Source
session states and boundary worlds of the lowered code, established by the
deployment and kept by every action, with the same events on both sides.
A Source frame that halts or times out shows no event. -/
structure MatchedFrames (D : Solidity.Goals.Shrink.Lowering.Diagram) (F : Fixed)
    (P : Solidity.Source.SrcProg E) (c : Compilation) (e : SessionEnv) where
  /-- The boundary invariant. -/
  Inv : Solidity.Source.St E → LoweredWorld c → Prop
  /-- The invariant relates the deployed instance's storage by `D.globRel`. -/
  glob : ∀ s w, Inv s w → ∀ a,
    w.accounts (liftAddress (P.fixed.createAddress e.deployer e.deployNonce)) = some a →
      D.globRel s (boundaryState a)
  /-- The deployment frame, at every Source horizon. -/
  deploy : ∀ n, match deployStep P e n with
    | .run _ _ _ s o => (targetDeploy F c e).stops = false ∧ (targetDeploy F c e).events = s.events ∧
        Inv s (targetDeploy F c e).world ∧ lastOutcome s.events = some o
    | .done p => p = ⟨[], none⟩
    | .start => True
  /-- The frame of every issued action, at every Source horizon. -/
  act : ∀ n k i s last w a, Inv s w → lastOutcome s.events = some last →
    e.requests s.events i = some a →
      match actStep P e n k i s last with
      | .run _ _ _ s' last' => (targetStep F c e s.events i w a).stops = false ∧
          s'.events = s.events ++ (targetStep F c e s.events i w a).events ∧
          Inv s' (targetStep F c e s.events i w a).world ∧ lastOutcome s'.events = some last'
      | .done p => p = ⟨s.events, none⟩
      | .start => True

/-- **The session-level match**: before the deployment both sides start; at a
boundary the histories and the issued actions agree, the worlds are related
and the last outcome is the history's; an ended Source session is observed. -/
def MatchedFrames.Matches {D : Solidity.Goals.Shrink.Lowering.Diagram} {F : Fixed}
    {P : Solidity.Source.SrcProg E} {c : Compilation} {e : SessionEnv} (fr : MatchedFrames D F P c e) :
    SourceState E → State (loweredCode c).contracts → Prop
  | .start, t => t = (targetMachine F (loweredWorld c) e).initial
  | .run _ _ i s last, t => t.history = s.events ∧ t.issued = i ∧ t.pending = .action ∧
      fr.Inv s t.world ∧ lastOutcome s.events = some last
  | .done p, t => t.observe = p

/-- Matched states observe the same prefix. -/
theorem MatchedFrames.Matches.observe {D : Solidity.Goals.Shrink.Lowering.Diagram} {F : Fixed}
    {P : Solidity.Source.SrcProg E} {c : Compilation} {e : SessionEnv} {fr : MatchedFrames D F P c e}
    {s : SourceState E} {t : State (loweredCode c).contracts} (m : fr.Matches s t) :
    t.observe = s.observe := by
  cases s with
  | start => cases m; rfl
  | run n k i s last =>
    obtain ⟨h, w, j, pend⟩ := t
    obtain ⟨rfl, -, rfl, -, -⟩ := m
    rfl
  | done p => exact m

omit [FreshNames] in
/-- The deployment starts the action budget at the horizon, with no action issued. -/
theorem deployStep_run {P : Solidity.Source.SrcProg E} {e : SessionEnv} {n n' k i : Nat}
    {s : Solidity.Source.St E} {o : Outcome} (h : deployStep P e n = .run n' k i s o) :
    n' = n ∧ k = n ∧ i = 0 := by
  unfold deployStep at h
  split at h <;> cases h
  exact ⟨rfl, rfl, rfl⟩

omit [FreshNames] in
/-- An action that goes on has issued one more action at the same horizon. -/
theorem actStep_run {P : Solidity.Source.SrcProg E} {e : SessionEnv} {n k i n' k' i' : Nat}
    {s s' : Solidity.Source.St E} {last last' : Outcome}
    (h : actStep P e n k i s last = .run n' k' i' s' last') : n' = n ∧ k' = k ∧ i' = i + 1 := by
  unfold actStep at h
  split at h
  · cases h
  · cases h; exact ⟨rfl, rfl, rfl⟩
  · split at h
    · split at h <;> cases h
      exact ⟨rfl, rfl, rfl⟩
    · cases h; exact ⟨rfl, rfl, rfl⟩

end Solidity.Correctness.Lowering.Sim.Session
