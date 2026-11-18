import Solidity.Correctness.Lowering.Sim.Session.Forward
import Solidity.Source.SessionExamples

/-! The forward session diagram and its resource record on the session of
`spin` (`Solidity.Source.SessionExamples`) against the lowered world of a
compilation, from matched frames. `MatchedFrames` is a hypothesis here as in
`Session/Forward.lean`, and these are type-level uses, not evidence of a
refinement: no frame of a concrete compilation is matched in the kernel (its
entries run the `partial` elaborator), and the family
`∀ e, MatchedFrames ..` that `spin_forward` and `spin_passCorrect` take has no
inhabitant when the deployment completes in some environment (a Source request
to an address without an instance reverts, the intrinsic one succeeds). Only
`spin_matched` asks for one environment. -/
namespace Solidity.Examples.Lowering.Sim.Session.Forward

open Solidity.Source Solidity.Source.SessionExamples
open Solidity.Correctness.Lowering.Sim (diagram)
open Solidity.Correctness.Lowering.Sim.Session
open Solidity.Roadmap (Fixed SessionEnv Outcome)
open Solidity.Roadmap.G49Final (Behaviour PassCorrect)
open Solidity.Goals.Shrink.Lowering (Compilation loweredWorld transport envAbs envAbs_sound
  envAbs_onto sourceBehaviour targetBehaviour)
open Solidity.Semantics.IntrinsicSession (runOf)

variable [FreshNames] (el : Elaborated) (F : Fixed) (c : Compilation)

/-- The diagram, once: every reachable state of `spin`'s session machine has a
matched reachable target state observing the same prefix. -/
theorem spin_matched (fr : MatchedFrames diagram F (progSpin el) c envSpin)
    {s : SourceState el.res.env} (reach : (sourceMachine (progSpin el) envSpin).Reachable s) :
    ∃ t, (targetMachine F (loweredWorld c) envSpin).Reachable t ∧ t.observe = s.observe := by
  obtain ⟨t, path, m, -⟩ := (forward fr).run reach
  exact ⟨t, path, MatchedFrames.Matches.observe m⟩

/-- The record, once: at an allowed, ready horizon of `spin`'s session the
transported bound is ready, and a completed session is the lowered run's prefix
there. -/
theorem spin_forward (fr : ∀ e, MatchedFrames diagram F (progSpin el) c e) (n : Nat)
    (allowed : envSpin.Allowed)
    (ready : (Behaviour.ofLang (sourceLang diagram F el.res.env (loweredWorld c)) (progSpin el)).Ready envSpin n)
    {o : Outcome} (done : (sessionAtEvents (progSpin el) envSpin n).final = some o) :
    (Behaviour.ofLang (targetLang F) (loweredWorld c)).Ready envSpin (transport diagram n) ∧
      (runOf F (loweredWorld c) envSpin (transport diagram n)).pfx =
        sessionAtEvents (progSpin el) envSpin n := by
  let R := forwardResources_diagram fr
  obtain ⟨s, reach, observes⟩ := R.coverage envSpin n allowed ready
  obtain ⟨t, path, m, -⟩ := (forward (fr envSpin)).run reach
  have le := R.bound envSpin n s t allowed ready reach observes path m
  rw [show (targetMachine F (loweredWorld c) envSpin).observe t = sessionAtEvents (progSpin el) envSpin n from
    (MatchedFrames.Matches.observe m).trans observes] at le
  exact ⟨R.ready envSpin n allowed ready, le.final_eq done⟩

/-- The record has the type `Sim.lang_passCorrect` consumes: with a reverse
diagram and its resources the application has the type of the `PassCorrect`
in `Shrink.Lowering.Lift`. A type check only: `fr` cannot be met as the
semantics stand (module comment), so no `PassCorrect` is obtained. -/
noncomputable def spin_passCorrect (fr : ∀ e, MatchedFrames diagram F (progSpin el) c e)
    (reverse : ∀ e, Solidity.Correctness.Sim.Diagram (targetMachine F (loweredWorld c) e)
      (sourceMachine (progSpin el) (envAbs e)))
    (R : Solidity.Correctness.Sim.BackwardResources
      (Behaviour.ofLang (sourceLang diagram F el.res.env (loweredWorld c)) (progSpin el))
      (Behaviour.ofLang (targetLang F) (loweredWorld c)) (sourceMachine (progSpin el))
      (targetMachine F (loweredWorld c)) envAbs reverse) :
    PassCorrect (sourceBehaviour diagram F (progSpin el) (loweredWorld c))
      (targetBehaviour F (loweredWorld c)) :=
  Solidity.Correctness.Sim.lang_passCorrect (sourceLang diagram F el.res.env (loweredWorld c)) (targetLang F)
    (progSpin el) (loweredWorld c) (sourceMachine (progSpin el)) (targetMachine F (loweredWorld c)) envAbs
    (envAbs_sound F (E := el.res.env)) (envAbs_onto F (E := el.res.env)) (fun e => forward (fr e))
    reverse
    (forwardResources_diagram fr) R

end Solidity.Examples.Lowering.Sim.Session.Forward
