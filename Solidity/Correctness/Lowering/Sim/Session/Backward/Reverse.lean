import Solidity.Correctness.Lowering.Sim.Session.Backward.Bounded

/-! The reverse diagram of the session lift (plan step `ls2s-session-diagrams`,
lane backward): from the session machine with a chosen horizon
(`boundedMachine`) to the Source session machine, and the backward record and
clause it gives.

The frame-level content is one hypothesis, `FrameBackward` (factory decision
H1200: kept as a hypothesis here, proved by its own plan step): a relation
between a boundary of the target and a running Source session (same history,
same action index, the last outcome), such that every deployment and every
action the target completes is completed by the Source session with a related
boundary at every large enough horizon. Frames that stop the target
(exhaustion, divergence) and the end of the session need no premise.

Nothing here assumes determinism of either side: the target step is a function
(`next`), and the Source horizon is chosen at the Source machine's first step,
when the target's budget is known (`follow_start`). -/
namespace Solidity.Correctness.Lowering.Sim.Session

open Solidity.Roadmap (Event Outcome SessionEnv Fixed Bytes)
open Solidity.Roadmap.G49Final (Behaviour)
open Solidity.Semantics.IntrinsicSession
open Solidity.ContractWorld (Entry Role)
open Solidity.Goals.Shrink.Lowering (Diagram envAbs)
open Solidity.Correctness.Sim (Star BackwardResources backward_of_simulation)

section Reverse

variable {E : Source.Env} (P : Source.SrcProg E)
  {contracts : List Contract} (main : Nat) (roles : Fin contracts.length → Role)
  (ctor : (k : Fin contracts.length) → Bytes → Option (Prog contracts[k] [] []))
  (entry : (k : Fin contracts.length) → Bytes → Option (Entry contracts[k] Bytes))
  (F : Fixed) (wire : Wire) (e : SessionEnv)

set_option quotPrecheck false in
local notation "nxt" => next main roles ctor entry F wire { horizon := 0 } e

/-- **The frame-level backward match** of a fresh session in `e`. -/
structure FrameBackward where
  /-- A target boundary and a running Source session: action index, state, last outcome. -/
  R : State contracts → Nat → Source.St E → Outcome → Prop
  obs : ∀ {t i s last}, R t i s last →
    t.pending = .action ∧ t.history = s.events ∧ t.issued = i ∧ lastOutcome t.history = some last
  /-- A deployment the target completes is completed by the Source session. -/
  deploy : ∀ t, nxt (State.start roles e .fresh) = some t → t.pending = .action →
    ∃ j s o, (∀ n, j ≤ n → deployStep P e n = .run n n 0 s o) ∧ R t 0 s o
  /-- An action the target completes is completed by the Source session. -/
  act : ∀ t t' i s last, R t i s last → nxt t = some t' → t'.pending = .action →
    ∃ j i' s' last', (∀ n, j ≤ n → ∀ b, actStep P e n b i s last = .run n b i' s' last') ∧
      R t' i' s' last'

/-- The Source state shows the target state's prefix, and its final observation. -/
def Obs (t : State contracts) (s : SourceState E) : Prop :=
  t.observe.events <+: s.observe.events ∧ ∀ o, t.observe.final = some o → s.observe = t.observe

/-- The Source state follows the target state for `k` steps. -/
def Follows : Nat → State contracts → SourceState E → Prop
  | 0, t, s => Obs t s
  | k + 1, t, s => Obs t s ∧
    ∀ t', nxt t = some t' → ∃ s', Star (SourceStep P e) s s' ∧ Follows k t' s'

variable {P main roles ctor entry F wire e}

theorem Follows.obs : ∀ {k : Nat} {t : State contracts} {s : SourceState E},
    Follows P main roles ctor entry F wire e k t s → Obs t s
  | 0, _, _, h => h
  | _ + 1, _, _, h => h.1

/-- A target state without successor is followed by any state that shows it. -/
theorem follows_stuck {t : State contracts} {s : SourceState E} (stuck : nxt t = none)
    (obs : Obs t s) : ∀ k, Follows P main roles ctor entry F wire e k t s
  | 0 => obs
  | _ + 1 => ⟨obs, fun t' h => by rw [stuck] at h; cases h⟩

/-- After a pending action: the session is idle, the frame stopped it, or the
next action is pending. -/
theorem next_action {h : List Event} {w : ContractWorld.World (catalog contracts)} {n : Nat}
    {t' : State contracts} (edge : nxt ⟨h, w, n, .action⟩ = some t') :
    (e.requests h n = none ∧ t' = ⟨h, w, n, .idle⟩) ∨ t' = ⟨h, w, n, .stopped⟩ ∨
      t'.pending = .action := by
  cases next_a : e.requests h n with
  | none =>
    simp only [next, next_a, Option.some.injEq] at edge
    exact .inl ⟨rfl, edge.symm⟩
  | some a =>
    simp only [next, next_a, Option.some.injEq] at edge
    split at edge <;> subst edge
    · exact .inr (.inl rfl)
    · exact .inr (.inr rfl)

/-- After the pending deployment: its frame stopped the session, or the first
action is pending. -/
theorem next_deploy {t' : State contracts} (edge : nxt (State.start roles e .fresh) = some t') :
    t' = ⟨[], initial roles e, 0, .stopped⟩ ∨ t'.pending = .action := by
  simp only [State.start, next, Option.some.injEq] at edge
  split at edge <;> subst edge
  · exact .inl rfl
  · exact .inr rfl

theorem actStep_idle {n k i : Nat} {s : Source.St E} {last : Outcome}
    (idle : e.requests s.events i = none) :
    actStep P e n k i s last = .done ⟨s.events, some last⟩ := by
  simp only [actStep, idle]

/-- **A running Source session follows a related boundary** for `k` steps, at
every large enough horizon and budget. -/
theorem follow_action (fb : FrameBackward P main roles ctor entry F wire e) :
    ∀ (k : Nat) (t : State contracts) (i : Nat) (s : Source.St E) (last : Outcome),
      fb.R t i s last → ∃ N, ∀ n, N ≤ n → ∀ b, k ≤ b →
        Follows P main roles ctor entry F wire e k t (.run n b i s last) := by
  intro k
  induction k with
  | zero =>
    intro t i s last r
    obtain ⟨act, hist, _, _⟩ := fb.obs r
    exact ⟨0, fun n _ b _ => ⟨by simp [State.observe, SourceState.observe, hist],
      fun o h => by simp [State.observe, act] at h⟩⟩
  | succ k ih =>
    intro t i s last r
    obtain ⟨act, hist, issued, lastOut⟩ := fb.obs r
    have shows : ∀ n b, Obs t (SourceState.run n b i s last) := fun n b =>
      ⟨by simp [State.observe, SourceState.observe, hist],
        fun o h => by simp [State.observe, act] at h⟩
    cases edge : nxt t with
    | none => exact ⟨0, fun n _ b _ => follows_stuck edge (shows n b) _⟩
    | some t' =>
      rcases t with ⟨h, w, m, pend⟩
      cases act; cases hist; cases issued
      rcases next_action edge with ⟨idle, rfl⟩ | rfl | pending
      · refine ⟨0, fun n _ b le => ⟨shows n b, fun t'' h'' => ?_⟩⟩
        rw [edge] at h''; cases h''
        obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
        refine ⟨.done ⟨s.events, some last⟩, .single ?_, follows_stuck rfl ⟨List.prefix_refl _, ?_⟩ _⟩
        · have step := SourceStep.act (P := P) (env := e) n b m s last
          rwa [actStep_idle idle] at step
        · intro o _
          simp [State.observe, SourceState.observe, lastOut]
      · refine ⟨0, fun n _ b _ => ⟨shows n b, fun t'' h'' => ?_⟩⟩
        rw [edge] at h''; cases h''
        exact ⟨_, .refl _, follows_stuck rfl ⟨List.prefix_refl _, fun o h => by
          simp [State.observe] at h⟩ _⟩
      · obtain ⟨j, i', s', last', steps, r'⟩ := fb.act _ _ _ _ _ r edge pending
        obtain ⟨N, follows⟩ := ih t' i' s' last' r'
        refine ⟨max j N, fun n le b leb => ⟨shows n b, fun t'' h'' => ?_⟩⟩
        rw [edge] at h''; cases h''
        obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
        refine ⟨.run n b i' s' last', .single ?_, follows n (by omega) b (by omega)⟩
        have step := SourceStep.act (P := P) (env := e) n b m s last
        rwa [steps n (by omega) b] at step

/-- **The Source start follows the target start** for every budget: the Source
horizon is chosen once the deployment is seen to complete. -/
theorem follow_start (fb : FrameBackward P main roles ctor entry F wire e) :
    ∀ k, Follows P main roles ctor entry F wire e k (State.start roles e .fresh) .start
  | 0 => ⟨List.nil_prefix, fun o h => by simp [State.observe, State.start] at h⟩
  | k + 1 => ⟨⟨List.nil_prefix, fun o h => by simp [State.observe, State.start] at h⟩, fun t' edge => by
    rcases next_deploy edge with rfl | pending
    · exact ⟨.start, .refl _, follows_stuck (t := ⟨[], initial roles e, 0, .stopped⟩) rfl
        ⟨List.nil_prefix, fun o h => by simp [State.observe] at h⟩ _⟩
    · obtain ⟨j, s, o, deploys, r⟩ := fb.deploy t' edge pending
      obtain ⟨N, follows⟩ := follow_action fb k t' 0 s o r
      refine ⟨.run (max (max j N) k) (max (max j N) k) 0 s o, .single ?_,
        follows _ (by omega) _ (by omega)⟩
      have step := SourceStep.deploy (P := P) (env := e) (max (max j N) k)
      rwa [deploys _ (by omega)] at step⟩

/-- **The reverse diagram**: the Source session machine simulates the fresh
session machine with a chosen horizon. -/
def reverseDiagram (fb : FrameBackward P main roles ctor entry F wire e) :
    Solidity.Correctness.Sim.Diagram (boundedMachine main roles ctor entry F wire .fresh e)
      (sourceMachine P (envAbs e)) where
  matchState
    | none, s => s = .start
    | some (k, t), s => Follows P main roles ctor entry F wire e k t s
  initial := rfl
  step t t' s edge related := by
    cases edge with
    | choose k => cases related; exact ⟨.start, .refl _, follow_start fb k⟩
    | step edge => exact related.2 _ edge
  events t s related := by
    rcases t with _ | ⟨k, t⟩
    · exact List.nil_prefix
    · exact (Follows.obs related).1
  final t s o related done := by
    rcases t with _ | ⟨k, t⟩
    · cases done
    · exact (Follows.obs related).2 o done

end Reverse

/-- The target machine with a chosen horizon at a session start. -/
noncomputable abbrev boundedTarget (F : Fixed) (x : Start) (e : SessionEnv) :
    Solidity.Correctness.Sim.Machine :=
  boundedMachine x.code.main x.code.roles x.code.ctor x.code.entry F
    Solidity.Semantics.IntrinsicSession.wire x.world e

/-- **The backward resource record** over the machine with a chosen horizon,
for every reverse diagram family; the type `lang_passCorrect` consumes. -/
noncomputable def boundedResources (D : Diagram) (F : Fixed) {E : Source.Env}
    (P : Source.SrcProg E) (x : Start)
    (reverse : ∀ e, Solidity.Correctness.Sim.Diagram (boundedTarget F x e) (sourceMachine P (envAbs e))) :
    BackwardResources (Behaviour.ofLang (sourceLang D F E x) P) (Behaviour.ofLang (targetLang F) x)
      (sourceMachine P) (boundedTarget F x) envAbs reverse where
  coverage e _ _ selected := bounded_covers _ _ _ _ F _ x.world e selected.1
  bound e _ _ _ _ _ _ _ _ reach _ :=
    let ⟨n, admissible, _, guard, le⟩ := sourceMachine_realized P (envAbs e) reach
    ⟨n, admissible, guard, le⟩

/-- **The backward clause of the session refinement** of a compilation's
lowered world, from the frame-level backward match alone: every guarded target
prefix without resource failure is below a Source prefix. -/
theorem backward_of_frames (D : Diagram) (F : Fixed) {E : Source.Env} (P : Source.SrcProg E)
    (code : Solidity.Goals.IntrinsicSession.Code)
    (fb : ∀ e, FrameBackward P code.main code.roles code.ctor code.entry F
      Solidity.Semantics.IntrinsicSession.wire e)
    (e : SessionEnv) (r : Bound) (allowed : e.Allowed) (noFail : r.NoFail)
    (guard : (lang F).Guard ⟨code, .fresh⟩ e r) :
    ∃ n, ((lang F).sem ⟨code, .fresh⟩ e r).Le ((Source.sourceLangEvents E).sem P (envAbs e) n) := by
  obtain ⟨n, _, _, le⟩ := backward_of_simulation
    (a := Behaviour.ofLang (sourceLang D F E ⟨code, .fresh⟩) P)
    (b := Behaviour.ofLang (targetLang F) ⟨code, .fresh⟩) (fun e => reverseDiagram (fb e))
    (boundedResources D F P ⟨code, .fresh⟩ fun e => reverseDiagram (fb e)) e r allowed noFail guard
  exact ⟨n, le⟩

end Solidity.Correctness.Lowering.Sim.Session
