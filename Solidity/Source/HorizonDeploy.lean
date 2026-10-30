import Solidity.Source.Horizon

/-!
# Deployments show a prefix of their events (S05 item 2)

`Horizon.lean` proves that a transaction not completed at a horizon shows a
prefix of its events at every larger one (`runTx_events_mono`).  The same
holds for a deployment (`deploy_events_mono`): construction (initializers,
base arguments, constructor bodies under their modifiers) only appends
events and approximates itself at the next horizon, from `growAt` and
`approxAt`.  `Session.lean` uses it to show the events of an unfinished
deployment.
-/

namespace Solidity.Source

open Solidity.Roadmap (Address Word Bytes Event Outcome)
open EM

variable {E : Env}

theorem Grow.forIn {Γ : RCtx} {α β : Type} (l : List α) (b : β) {f : α → β → EM E Γ (ForInStep β)}
    (h : ∀ a b, Grow (f a b)) : Grow (forIn l b f) := by
  induction l generalizing b with
  | nil => exact Grow.pure _
  | cons a as ih =>
    simp only [List.forIn_cons]
    refine Grow.bind (h a b) fun r => ?_
    cases r with
    | done _ => exact Grow.pure _
    | yield b' => exact ih b'

section
variable {Γ : RCtx}

theorem storeRV_grow (F : Fr) (n : Nat) (τ : STy) (p : SPath) {σ : STy} (v : RVal E.layout σ) :
    Grow (storeRV (Γ := Γ) F n τ p v) := by
  unfold storeRV
  grow_go [storeVal_grow, storeData_grow, writeAt_grow]

theorem storeRV_const (F : Fr) (n : Nat) (τ : STy) (p : SPath) {σ : STy} (v : RVal E.layout σ) :
    Const (storeRV (Γ := Γ) F n τ p v) := by
  unfold storeRV
  const_go [storeVal_const, storeData_const, writeAt_const]

theorem storeRV_approx (F : Fr) (n : Nat) (τ : STy) (p : SPath) {σ : STy} (v : RVal E.layout σ) :
    Approx (storeRV (Γ := Γ) F n τ p v) (storeRV F (n + 1) τ p v) :=
  Approx.of_below (storeRV_below F n τ p v) (storeRV_const F n τ p v) (storeRV_const F (n + 1) τ p v)

theorem ctorLocalsOf_grow (G : Glob E) (acc : CtorLocals G) (X : String) :
    Grow (ctorLocalsOf (Γ := Γ) G acc X) := by
  unfold ctorLocalsOf
  grow_go []

end

theorem runInits_grow (G : Glob E) (F : Fr) (n : Nat) : ∀ (l : List (RInit E)), Grow (runInits G F n l)
  | [] => Grow.pure _
  | _ :: rest => Grow.bind (Grow.sub _ ((growAt G n).evalE F _)) fun _ =>
      Grow.bind (storeRV_grow F n _ _ _) fun _ => runInits_grow G F n rest

theorem runInits_approx (G : Glob E) (F : Fr) (n : Nat) : ∀ (l : List (RInit E)),
    Approx (runInits G F n l) (runInits G F (n + 1) l)
  | [] => Approx.refl (Grow.pure _)
  | _ :: rest => Approx.bind (Approx.sub _ ((approxAt G n).evalE F _)) fun _ =>
      Approx.bind (storeRV_approx F n _ _ _) fun _ => runInits_approx G F n rest

theorem giveArgs_grow (G : Glob E) (F : Fr) (n : Nat) (X : String) (lX : Locals E.layout (G.prog.ctorLocals X)) :
    ∀ (bs : List (RBaseArg E (G.prog.ctorLocals X))) (acc : CtorLocals G), Grow (giveArgs G F n X lX bs acc)
  | [], _ => Grow.pure _
  | ba :: rest, acc => by
    simp only [giveArgs]
    split
    · exact giveArgs_grow G F n X lX rest acc
    · refine Grow.bind (Grow.sub _ ((growAt G n).evalConvArgs F _)) fun _ => ?_
      split
      · exact giveArgs_grow G F n X lX rest _
      · exact Grow.halt _

theorem giveArgs_approx (G : Glob E) (F : Fr) (n : Nat) (X : String) (lX : Locals E.layout (G.prog.ctorLocals X)) :
    ∀ (bs : List (RBaseArg E (G.prog.ctorLocals X))) (acc : CtorLocals G),
      Approx (giveArgs G F n X lX bs acc) (giveArgs G F (n + 1) X lX bs acc)
  | [], _ => Approx.refl (Grow.pure _)
  | ba :: rest, acc => by
    simp only [giveArgs]
    split
    · exact giveArgs_approx G F n X lX rest acc
    · refine Approx.bind (Approx.sub _ ((approxAt G n).evalConvArgs F _)) fun _ => ?_
      split
      · exact giveArgs_approx G F n X lX rest _
      · exact Approx.refl (Grow.halt _)

theorem collectArgs_grow (G : Glob E) (F : Fr) (n : Nat) : ∀ (Xs : List String) (acc : CtorLocals G),
    Grow (collectArgs G F n Xs acc)
  | [], _ => Grow.pure _
  | X :: Xs, acc => Grow.bind (ctorLocalsOf_grow G acc X) fun lX =>
      Grow.bind (giveArgs_grow G F n X lX _ acc) fun acc' => collectArgs_grow G F n Xs acc'

theorem collectArgs_approx (G : Glob E) (F : Fr) (n : Nat) : ∀ (Xs : List String) (acc : CtorLocals G),
    Approx (collectArgs G F n Xs acc) (collectArgs G F (n + 1) Xs acc)
  | [], _ => Approx.refl (Grow.pure _)
  | X :: Xs, acc => Approx.bind (Approx.refl (ctorLocalsOf_grow G acc X)) fun lX =>
      Approx.bind (giveArgs_approx G F n X lX _ acc) fun acc' => collectArgs_approx G F n Xs acc'

theorem runCtorBody_grow (G : Glob E) (F : Fr) (n : Nat) (acc : CtorLocals G) (X : String) :
    Grow (runCtorBody G F n acc X) := by
  have gn := growAt G n
  unfold runCtorBody
  grow_go [gn.runMods, ctorLocalsOf_grow]

theorem runCtorBody_approx (G : Glob E) (F : Fr) (n : Nat) (acc : CtorLocals G) (X : String) :
    Approx (runCtorBody G F n acc X) (runCtorBody G F (n + 1) acc X) := by
  have ih := approxAt G n
  unfold runCtorBody
  split
  · exact Approx.refl (Grow.pure _)
  · refine Approx.bind (Approx.refl (ctorLocalsOf_grow G acc X)) fun lX => ?_
    split
    · exact Approx.bind (ih.runMods _ _ _ _) fun _ => Approx.refl (Grow.pure _)
    · exact Approx.refl (Grow.halt _)

theorem construct_grow (G : Glob E) (F : Fr) (n : Nat) (c : String) (lc : Locals E.layout (G.prog.ctorLocals c)) :
    Grow (construct G F n c lc) := by
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
    Approx (construct G F n c lc) (construct G F (n + 1) c lc) := by
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
    Grow (deploy G n c addr sender value args) := by
  unfold deploy
  grow_go [construct_grow, decodeArgs_grow, mark_grow, rollbackTo_grow]

theorem deploy_approx (G : Glob E) (n : Nat) (c : String) (addr sender : Address) (value : Word) (args : Bytes) :
    Approx (deploy G n c addr sender value args) (deploy G (n + 1) c addr sender value args) := by
  unfold deploy
  dsimp only
  refine Approx.bind (Approx.refl mark_grow) fun m => ?_
  refine Approx.bind (Approx.refl Grow.st) fun s => ?_
  split <;> refine Approx.bind (Approx.refl (by grow_go [])) fun _ => ?_ <;>
    refine Approx.attempt_bind ?_ (fun _ => Approx.refl (by grow_go [rollbackTo_grow])) (fun _ => ⟨rfl, rfl⟩) <;>
    split <;> refine Approx.bind (Approx.refl (by grow_go [])) fun _ => ?_ <;>
    split <;> refine Approx.bind (Approx.refl (by grow_go [])) fun _ => ?_ <;>
    refine Approx.bind (Approx.refl (decodeArgs_grow _ _ _)) fun _ => ?_ <;>
    split <;> first | exact construct_approx G _ n c _ | exact Approx.refl (Grow.halt _)

/-- **A deployment's events grow with its horizon**: the events at horizon
`k` are a prefix of those at every `k' ≥ k` (a completed run's are equal). -/
theorem deploy_events_mono (G : Glob E) (c : String) (addr sender : Address) (value : Word) (args : Bytes)
    (s : St E) {k k' : Nat} (hk : k ≤ k') :
    (runAt (fun f => deploy G f c addr sender value args) s k).2.events <+:
      (runAt (fun f => deploy G f c addr sender value args) s k').2.events := by
  have ha := Approx.mono (f := fun f => deploy G f c addr sender value args)
    (fun n => deploy_approx G n c addr sender value args) (fun n => deploy_grow G n c addr sender value args) hk
  simp only [runAt]
  rcases ha.2.2 (L0 E, s) with ⟨_, he⟩ | he
  · exact he
  · rw [he]; exact List.prefix_refl _

/-- info: 'Solidity.Source.deploy_events_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deploy_events_mono

end Solidity.Source
