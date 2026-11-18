import Solidity.Correctness.Lowering.Sim.Session.Backward.Reverse

/-! Checks of the backward lane of the session lift on a small session: the
lowered world of a compilation that resolves no deployment and no entry, in an
environment that issues a credit at every boundary.

* The backward record has the type `Sim.lang_passCorrect` consumes, and the
  certificate it yields is one between the goal's two behaviours.
* The reverse diagram that certificate needs does not exist on this session:
  its deployment reverts unresolved, every later action is a credit, and the
  Source session machine cannot follow (`no_reverse_diagram_credits`). The
  environment is allowed whenever the one it is built from is.
* Against the machine with a chosen horizon the diagram exists from the
  frame-level backward match (`FrameBackward`, a hypothesis here): on the small
  session it is used once with the record, through `lang_passCorrect`, and
  once for the backward clause and its completed-run reading. -/
namespace Solidity.Examples.Lowering.Sim.Session.Backward

open Solidity.Roadmap (SessionEnv Fixed Address)
open Solidity.Roadmap.G49Final (Behaviour PassCorrect)
open Solidity.Semantics.IntrinsicSession (Start deploy wire Bound lang)
open Solidity.Goals.Shrink.Lowering
open Solidity.Correctness.Sim (ForwardResources lang_passCorrect)
open Solidity.Correctness.Lowering.Sim.Session

variable [FreshNames]

/-- The record is consumed by `lang_passCorrect` as it is, and the certificate
is one between `sourceBehaviour` and `targetBehaviour`. -/
noncomputable example (D : Diagram) (F : Fixed) {E : Source.Env} (P : Source.SrcProg E) (x : Start)
    (forward : ∀ e, Solidity.Correctness.Sim.Diagram (sourceMachine P (envAbs e)) (targetMachine F x e))
    (reverse : ∀ e, Solidity.Correctness.Sim.Diagram (targetMachine F x e) (sourceMachine P (envAbs e)))
    (resources : ForwardResources (Behaviour.ofLang (sourceLang D F E x) P)
      (Behaviour.ofLang (targetLang F) x) (sourceMachine P) (targetMachine F x) envAbs forward) :
    PassCorrect (sourceBehaviour D F P x) (targetBehaviour F x) :=
  lang_passCorrect (sourceLang D F E x) (targetLang F) P x (sourceMachine P) (targetMachine F x)
    envAbs (fun e => envAbs_sound F (E := E) e) (fun e => envAbs_onto F (E := E) e) forward reverse resources
    (backwardResources D F P x reverse)

/-- A compilation of `C` that resolves nothing. -/
def noCode (C : Contract) : Compilation := ⟨C, fun _ => none, fun _ => none⟩

/-- The environment `e` issuing a credit of the deployment value to the
deployer at every boundary. -/
def credits (e : SessionEnv) : SessionEnv :=
  { e with requests := fun _ _ => some (.credit e.deployer e.deployValue) }

example (e : SessionEnv) (allowed : e.Allowed) : (credits e).Allowed := allowed

/-- The unresolved deployment reverts and the session goes on. -/
theorem noCode_deploys (C : Contract) (F : Fixed) (e : SessionEnv) :
    (deploy (loweredWorld (noCode C)).code.main (loweredWorld (noCode C)).code.roles
      (loweredWorld (noCode C)).code.ctor F wire { horizon := 0 } e).stops = false := by
  simp [deploy, loweredWorld, loweredCode, noCode, Compilation.ctorProg]

/-- **No reverse diagram on the small session**, for any Source program. -/
example (C : Contract) (F : Fixed) {E : Source.Env} (P : Source.SrcProg E) (e : SessionEnv)
    (D : Solidity.Correctness.Sim.Diagram (targetMachine F (loweredWorld (noCode C)) (credits e))
      (sourceMachine P (envAbs (credits e)))) : False :=
  no_reverse_diagram_credits P F _ _ (noCode_deploys C F _) (fun _ _ => ⟨_, _, rfl⟩) D

/-- So the reverse premise of `lang_passCorrect` fails for the frozen machines,
already on allowed environments. -/
example (C : Contract) (F : Fixed) {E : Source.Env} (P : Source.SrcProg E) (e : SessionEnv)
    (allowed : e.Allowed) :
    ¬ ∀ e', e'.Allowed → Nonempty (Solidity.Correctness.Sim.Diagram
      (targetMachine F (loweredWorld (noCode C)) e') (sourceMachine P (envAbs e'))) := fun all =>
  let ⟨D⟩ := all (credits e) allowed
  no_reverse_diagram_credits P F _ _ (noCode_deploys C F _) (fun _ _ => ⟨_, _, rfl⟩) D

/-- The frame-level backward match of the small session, in every environment. -/
abbrev Frames (C : Contract) (F : Fixed) {E : Source.Env} (P : Source.SrcProg E) : Type :=
  ∀ e, FrameBackward P (loweredCode (noCode C)).main (loweredCode (noCode C)).roles
    (loweredCode (noCode C)).ctor (loweredCode (noCode C)).entry F wire e

/-- **The diagram and the record, once**: with any forward half, the reverse
diagram of the small session and its record give the session certificate. -/
noncomputable example (D : Diagram) (C : Contract) (F : Fixed) {E : Source.Env}
    (P : Source.SrcProg E) (fb : Frames C F P)
    (forward : ∀ e, Solidity.Correctness.Sim.Diagram (sourceMachine P (envAbs e))
      (boundedTarget F (loweredWorld (noCode C)) e))
    (resources : ForwardResources (Behaviour.ofLang (sourceLang D F E (loweredWorld (noCode C))) P)
      (Behaviour.ofLang (targetLang F) (loweredWorld (noCode C))) (sourceMachine P)
      (boundedTarget F (loweredWorld (noCode C))) envAbs forward) :
    PassCorrect (sourceBehaviour D F P (loweredWorld (noCode C)))
      (targetBehaviour F (loweredWorld (noCode C))) :=
  let reverse : ∀ e, Solidity.Correctness.Sim.Diagram (boundedTarget F (loweredWorld (noCode C)) e)
      (sourceMachine P (envAbs e)) := fun e => reverseDiagram (fb e)
  lang_passCorrect (sourceLang D F E _) (targetLang F) P (loweredWorld (noCode C)) (sourceMachine P)
    (boundedTarget F _) envAbs (fun e => envAbs_sound F (E := E) e)
    (fun e => envAbs_onto F (E := E) e) forward reverse resources (boundedResources D F P _ reverse)

/-- A session of the small world that ends is a Source session that ends with
the same history and outcome: the backward clause on a completed run. -/
example (D : Diagram) (C : Contract) (F : Fixed) {E : Source.Env} (P : Source.SrcProg E)
    (fb : Frames C F P) (e : SessionEnv) (r : Bound) (allowed : e.Allowed) (noFail : r.NoFail)
    (guard : (lang F).Guard (loweredWorld (noCode C)) e r) (o : Solidity.Roadmap.Outcome)
    (done : ((lang F).sem (loweredWorld (noCode C)) e r).final = some o) :
    ∃ n, (Source.sourceLangEvents E).sem P e n = (lang F).sem (loweredWorld (noCode C)) e r :=
  let ⟨n, le⟩ := backward_of_frames D F P (loweredCode (noCode C)) fb e r allowed noFail guard
  ⟨n, le.final_eq done⟩

end Solidity.Examples.Lowering.Sim.Session.Backward
