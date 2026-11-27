import Solidity.Source.FailureEvaluatorApprox
import Solidity.Source.HorizonDeploy

/-! Actual fixed-plan initializer, base-argument, modifier-body and deployment
horizon transport. No alternate semantics or execution oracle. This does not
consume the deployment transaction-fate ordinal or prove session/P8 adequacy.
Proof basis: Source/HorizonDeploy.lean SHA256 ea72b085442795d463b71d315c3af764e4fd6170329febb94e2d6906b7ec8d34. -/
namespace Solidity.Source.FailureExecution.PlannedDeploy
open EM
open Solidity.Roadmap (Address Word Bytes)
variable {E : Env} {points : Roadmap.Evm.FailurePoints}

theorem runInits_grow (G : Glob E) (F : Fr) (n : Nat) : ∀ (l : List (RInit E)), Grow (runInits (plan := some points) G F n l)
  | [] => Grow.pure _
  | _ :: rest => Grow.bind (Grow.sub _ ((PlannedGrow.growAt G (points := points) n).evalE F _)) fun _ =>
      Grow.bind (storeRV_grow F n _ _ _) fun _ => runInits_grow G F n rest

theorem runInits_approx (G : Glob E) (F : Fr) (n : Nat) : ∀ (l : List (RInit E)),
    Approx (runInits (plan := some points) G F n l) (runInits (plan := some points) G F (n + 1) l)
  | [] => Approx.refl (Grow.pure _)
  | _ :: rest => Approx.bind (Approx.sub _ ((PlannedApprox.approxAt G (points := points) n).evalE F _)) fun _ =>
      Approx.bind (storeRV_approx F n _ _ _) fun _ => runInits_approx G F n rest

theorem giveArgs_grow (G : Glob E) (F : Fr) (n : Nat) (X : String) (lX : Locals E.layout (G.prog.ctorLocals X)) :
    ∀ (bs : List (RBaseArg E (G.prog.ctorLocals X))) (acc : CtorLocals G), Grow (giveArgs (plan := some points) G F n X lX bs acc)
  | [], _ => Grow.pure _
  | ba :: rest, acc => by
    simp only [giveArgs]
    split
    · exact giveArgs_grow G F n X lX rest acc
    · refine Grow.bind (Grow.sub _ ((PlannedGrow.growAt G (points := points) n).evalConvArgs F _)) fun _ => ?_
      split
      · exact giveArgs_grow G F n X lX rest _
      · exact Grow.halt _

theorem giveArgs_approx (G : Glob E) (F : Fr) (n : Nat) (X : String) (lX : Locals E.layout (G.prog.ctorLocals X)) :
    ∀ (bs : List (RBaseArg E (G.prog.ctorLocals X))) (acc : CtorLocals G),
      Approx (giveArgs (plan := some points) G F n X lX bs acc) (giveArgs (plan := some points) G F (n + 1) X lX bs acc)
  | [], _ => Approx.refl (Grow.pure _)
  | ba :: rest, acc => by
    simp only [giveArgs]
    split
    · exact giveArgs_approx G F n X lX rest acc
    · refine Approx.bind (Approx.sub _ ((PlannedApprox.approxAt G (points := points) n).evalConvArgs F _)) fun _ => ?_
      split
      · exact giveArgs_approx G F n X lX rest _
      · exact Approx.refl (Grow.halt _)

theorem collectArgs_grow (G : Glob E) (F : Fr) (n : Nat) : ∀ (Xs : List String) (acc : CtorLocals G),
    Grow (collectArgs (plan := some points) G F n Xs acc)
  | [], _ => Grow.pure _
  | X :: Xs, acc => Grow.bind (ctorLocalsOf_grow G acc X) fun lX =>
      Grow.bind (giveArgs_grow G F n X lX _ acc) fun acc' => collectArgs_grow G F n Xs acc'

theorem collectArgs_approx (G : Glob E) (F : Fr) (n : Nat) : ∀ (Xs : List String) (acc : CtorLocals G),
    Approx (collectArgs (plan := some points) G F n Xs acc) (collectArgs (plan := some points) G F (n + 1) Xs acc)
  | [], _ => Approx.refl (Grow.pure _)
  | X :: Xs, acc => Approx.bind (Approx.refl (ctorLocalsOf_grow G acc X)) fun lX =>
      Approx.bind (giveArgs_approx G F n X lX _ acc) fun acc' => collectArgs_approx G F n Xs acc'

theorem runCtorBody_grow (G : Glob E) (F : Fr) (n : Nat) (acc : CtorLocals G) (X : String) :
    Grow (runCtorBody (plan := some points) G F n acc X) := by
  have gn := PlannedGrow.growAt G (points := points) n
  unfold runCtorBody
  grow_go [check_grow, frame_grow, gn.runMods, ctorLocalsOf_grow]

theorem runCtorBody_approx (G : Glob E) (F : Fr) (n : Nat) (acc : CtorLocals G) (X : String) :
    Approx (runCtorBody (plan := some points) G F n acc X) (runCtorBody (plan := some points) G F (n + 1) acc X) := by
  have ih := PlannedApprox.approxAt G (points := points) n
  unfold runCtorBody
  split
  · exact Approx.refl (Grow.pure _)
  · refine Approx.bind (Approx.refl (ctorLocalsOf_grow G acc X)) fun lX => ?_
    split
    · exact Approx.bind (ih.runMods _ _ _ _) fun _ => Approx.refl (Grow.pure _)
    · exact Approx.refl (Grow.halt _)

theorem construct_grow (G : Glob E) (F : Fr) (n : Nat) (c : String) (lc : Locals E.layout (G.prog.ctorLocals c)) :
    Grow (construct (plan := some points) G F n c lc) := by
  unfold construct
  split
  · refine Grow.bind (Grow.forIn _ _ fun X _ => Grow.bind (runInits_grow G F n _) fun _ => Grow.pure _)
      fun _ => ?_
    refine Grow.bind (collectArgs_grow G F n _ _) fun acc => ?_
    exact Grow.bind (Grow.forIn _ _ fun X _ => Grow.bind (runCtorBody_grow G F n acc X) fun _ => Grow.pure _)
      fun _ => Grow.pure _
  · refine Grow.bind (collectArgs_grow G F n _ _) fun acc => ?_
    exact Grow.bind (Grow.forIn _ _ fun X _ => Grow.bind (runInits_grow G F n _) fun _ =>
      Grow.bind (runCtorBody_grow G F n acc X) fun _ => Grow.pure _) fun _ => Grow.pure _

theorem construct_approx (G : Glob E) (F : Fr) (n : Nat) (c : String) (lc : Locals E.layout (G.prog.ctorLocals c)) :
    Approx (construct (plan := some points) G F n c lc) (construct (plan := some points) G F (n + 1) c lc) := by
  unfold construct
  split
  · refine Approx.bind (Approx.forIn _ _ fun X _ => Approx.bind (runInits_approx G F n _) fun _ =>
      Approx.refl (Grow.pure _)) fun _ => ?_
    refine Approx.bind (collectArgs_approx G F n _ _) fun acc => ?_
    exact Approx.bind (Approx.forIn _ _ fun X _ => Approx.bind (runCtorBody_approx G F n acc X) fun _ =>
      Approx.refl (Grow.pure _)) fun _ => Approx.refl (Grow.pure _)
  · refine Approx.bind (collectArgs_approx G F n _ _) fun acc => ?_
    exact Approx.bind (Approx.forIn _ _ fun X _ => Approx.bind (runInits_approx G F n _) fun _ =>
      Approx.bind (runCtorBody_approx G F n acc X) fun _ => Approx.refl (Grow.pure _))
      fun _ => Approx.refl (Grow.pure _)

theorem deploy_grow (G : Glob E) (n : Nat) (c : String) (addr sender : Address) (value : Word) (args : Bytes) :
    Grow (deploy (plan := some points) G n c addr sender value args) := by
  unfold deploy
  grow_go [check_grow, frame_grow, construct_grow, decodeArgs_grow, mark_grow, rollbackTo_grow]


theorem deploy_approx (G : Glob E) (n : Nat) (c : String) (addr sender : Address)
    (value : Word) (args : Bytes) :
    Approx (deploy (plan := some points) G n c addr sender value args)
      (deploy (plan := some points) G (n+1) c addr sender value args) := by
  unfold deploy
  dsimp only
  refine Approx.bind (Approx.refl mark_grow) fun saved => ?_
  refine Approx.bind (Approx.refl Grow.st) fun state => ?_
  split <;> refine Approx.bind (Approx.refl (by grow_go [])) fun _ => ?_ <;>
    refine Approx.attempt_bind (frame_approx _ ?_)
      (fun _ => Approx.refl (by grow_go [check_grow, rollbackTo_grow])) (fun _ => ⟨rfl,rfl⟩) <;>
    split <;> refine Approx.bind (Approx.refl (by grow_go [])) fun _ => ?_ <;>
    split <;> refine Approx.bind (Approx.refl (by grow_go [])) fun _ => ?_ <;>
    refine Approx.bind (Approx.refl (decodeArgs_grow _ _ _)) fun _ => ?_ <;>
    split <;> first | exact construct_approx G _ n c _ | exact Approx.refl (Grow.halt _)

theorem deploy_events_mono (G : Glob E) (c : String) (addr sender : Address)
    (value : Word) (args : Bytes) (locals : Locals E.layout []) (state : St E)
    {horizon later : Nat} (more : horizon ≤ later) :
    ((deploy (plan := some points) G horizon c addr sender value args).run (locals,state)).2.2.events <+:
      ((deploy (plan := some points) G later c addr sender value args).run (locals,state)).2.2.events := by
  have approx := Approx.mono (fun n => deploy_approx (points := points) G n c addr sender value args)
    (fun n => deploy_grow (points := points) G n c addr sender value args) more
  rcases approx.2.2 (locals,state) with cut | same
  · exact cut.2
  · rw [same]
    exact List.prefix_refl _

theorem deploy_stable (G : Glob E) (c : String) (addr sender : Address)
    (value : Word) (args : Bytes) (locals : Locals E.layout []) (state : St E)
    {horizon later : Nat} (more : horizon ≤ later)
    (completed : ((deploy (plan := some points) G horizon c addr sender value args).run
      (locals,state)).1 ≠ .error .timeout) :
    (deploy (plan := some points) G later c addr sender value args).run (locals,state) =
      (deploy (plan := some points) G horizon c addr sender value args).run (locals,state) := by
  have approx := Approx.mono (fun n => deploy_approx (points := points) G n c addr sender value args)
    (fun n => deploy_grow (points := points) G n c addr sender value args) more
  rcases approx.2.2 (locals,state) with cut | same
  · exact False.elim (completed cut.1)
  · exact same.symm

end Solidity.Source.FailureExecution.PlannedDeploy
