import Solidity.Goals.LoweringSession
import Solidity.Correctness.Lowering.Sim.Session.Target

/-! The backward half of the session-level lift: the resource record.

`Shrink.Lowering.Lift` asks a `PassCorrect` between `sourceBehaviour` and
`targetBehaviour`, which are not `Behaviour.ofLang` of the two frozen languages
read verbatim. They are `Behaviour.ofLang` of `sourceLang` and `targetLang`
below (`sourceLang_behaviour`, `targetLang_behaviour`, both `rfl`), so the
record has exactly the type `Sim.lang_passCorrect` consumes.

* `targetMachine F x e`: the frozen session machine without resource failure
  (`machine₀`) at the code and world of the start `x`.
* `backwardResources`: the `BackwardResources` record for **every** reverse
  diagram family from `targetMachine` to `sourceMachine`. Coverage is
  `covers_noFail` (every guarded prefix without resource failure, reverting and
  stopped frames included); the bound is `sourceMachine_realized`. Neither
  reads the diagram, a determinism property or the lowering.
* `backward`: the frozen backward clause from a reverse diagram family.

The reverse diagram itself is not here: between these two machines none exists
for a start whose deployment completes in an environment that issues a credit
at every boundary (`Backward/NoDiagram.lean`). For such starts `backward` and
`backwardResources` are vacuous as the machines stand. -/
namespace Solidity.Correctness.Lowering.Sim.Session

open Solidity.Roadmap (Event Outcome SessionEnv Lang Fixed)
open Solidity.Roadmap.G49Final (Behaviour)
open Solidity.Semantics.IntrinsicSession (Start spec lang wire Bound)
open Solidity.Goals.Shrink.Lowering (Diagram transport envAbs sourceBehaviour targetBehaviour)
open Solidity.Correctness.Sim (Machine BackwardResources backward_of_simulation)

/-- The Source session language read as `sourceBehaviour` reads it: `Forward`
is the target's readiness at the transported bound. -/
noncomputable def sourceLang (D : Diagram) (F : Fixed) (E : Source.Env) (x : Start) :
    Lang Event Outcome :=
  { Source.sourceLangEvents E with
    Forward := fun _ e n => (Behaviour.ofLang (spec F).lang ((spec F).ofWorld x)).Ready e (transport D n) }

/-- The intrinsic session language read as `targetBehaviour` reads it: the
admissible bounds are those without resource failure. -/
noncomputable def targetLang (F : Fixed) : Lang Event Outcome :=
  { lang F with Admissible := Bound.NoFail }

theorem sourceLang_behaviour (D : Diagram) (F : Fixed) {E : Source.Env} (P : Source.SrcProg E)
    (x : Start) : Behaviour.ofLang (sourceLang D F E x) P = sourceBehaviour D F P x := rfl

theorem targetLang_behaviour (F : Fixed) (x : Start) :
    Behaviour.ofLang (targetLang F) x = targetBehaviour F x := rfl

/-- **The target machine** of a session start: the frozen session machine
without resource failure, at the start's code and world. -/
noncomputable abbrev targetMachine (F : Fixed) (x : Start) (e : SessionEnv) : Machine :=
  machine₀ x.code.main x.code.roles x.code.ctor x.code.entry F wire x.world e

/-- **The backward resource record**, for every reverse diagram family: every
admissible guarded target prefix is covered by the target machine, and every
matched source state is realized below an admissible source prefix. -/
noncomputable def backwardResources (D : Diagram) (F : Fixed) {E : Source.Env}
    (P : Source.SrcProg E) (x : Start)
    (reverse : ∀ e, Solidity.Correctness.Sim.Diagram (targetMachine F x e) (sourceMachine P (envAbs e))) :
    BackwardResources (Behaviour.ofLang (sourceLang D F E x) P) (Behaviour.ofLang (targetLang F) x)
      (sourceMachine P) (targetMachine F x) envAbs reverse where
  coverage e _ _ selected := covers_noFail x.world e selected.1
  bound e _ _ _ _ _ _ _ _ reach _ :=
    let ⟨n, admissible, _, guard, le⟩ := sourceMachine_realized P (envAbs e) reach
    ⟨n, admissible, guard, le⟩

/-- **The backward clause of the session refinement** from a reverse diagram
family: every guarded target prefix without resource failure is below a source
prefix. The source bound is realized, not transported. -/
theorem backward (D : Diagram) (F : Fixed) {E : Source.Env} (P : Source.SrcProg E) (x : Start)
    (reverse : ∀ e, Solidity.Correctness.Sim.Diagram (targetMachine F x e) (sourceMachine P (envAbs e)))
    (e : SessionEnv) (r : Bound) (allowed : e.Allowed) (noFail : r.NoFail)
    (guard : (lang F).Guard x e r) :
    ∃ n, ((lang F).sem x e r).Le ((Source.sourceLangEvents E).sem P (envAbs e) n) := by
  obtain ⟨n, _, _, le⟩ := backward_of_simulation (a := Behaviour.ofLang (sourceLang D F E x) P)
    (b := Behaviour.ofLang (targetLang F) x) reverse (backwardResources D F P x reverse) e r
    allowed noFail guard
  exact ⟨n, le⟩

end Solidity.Correctness.Lowering.Sim.Session
