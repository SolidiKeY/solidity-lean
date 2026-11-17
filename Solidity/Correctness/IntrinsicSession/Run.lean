import Solidity.Correctness.IntrinsicSession.Step

/-!
# The intrinsic session run

Definitions for the concrete intrinsic session semantics (H556 option A, plan
step `is0d-session-run`), part 2 of 2 of the session run; nothing here is a
goal. The path is under `Solidity/Correctness` for the reason `Step.lean`
states.

`run main roles ctor entry F wire w e r` iterates the one-action step of
`Step.lean` along `SessionEnv.requests` and gives one `Run`:

* `pfx`: the `Prefix Event Outcome` reached;
* `worlds`: the worlds reached at transaction boundaries, in order: the one
  after the deployment and the one after every action that completed (a
  dropped request and a credit included);
* `frames`: the executed frames in order, reverting ones included.

A session world (`SessionWorld`) is `fresh` (the session starts with the
deployment from `initial`, whatever the horizon) or a `boundary` world (the
session resumes there with action `0` and the empty history). The bound's
horizon counts the actions after the deployment. The prefix is final once
`requests` answers `none`; its final observation is the last outcome of the
history (`lastOutcome`), none when the history has no outcome. A reverted
deployment is an outcome like any other and the session goes on. A frame
that exhausts or diverges is recorded, shows no event and stops the session
without a final observation.

`go` is the iteration from any boundary (history, action index, world); it
returns the whole history and the worlds and frames from there on.

A larger bound extends the run in all three projections (`run_mono`):
`run_consistent`, `worlds_mono` and `frames_mono` are its parts, and
`directed` gives bounds without resource failure a common upper bound.
-/

namespace Solidity.Semantics.IntrinsicSession

open Solidity.Roadmap
open Solidity.ContractWorld (World Entry Role)

/-- The outcome a completed deployment or transaction shows. -/
def outcomeIn : Event → Option Outcome
  | .deploy _ _ _ o _ => some o
  | .tx _ _ _ _ _ o => some o
  | _ => none

/-- The last completed outcome of a history. -/
def lastOutcome (h : List Event) : Option Outcome := (h.filterMap outcomeIn).getLast?

/-- Where a session starts: nothing deployed, or a world at a transaction
boundary. -/
inductive SessionWorld (contracts : List Contract) where
  | fresh
  | boundary (w : World (catalog contracts))

/-- One run of a session: the prefix reached, the worlds reached at
transaction boundaries and the executed frames. -/
structure Run (contracts : List Contract) where
  pfx : Prefix Event Outcome
  worlds : List (World (catalog contracts))
  frames : List (Frame (catalog contracts))

/-- The run `ρ` after a step that reached `w` and ran `fs`. -/
def Run.after {contracts : List Contract} (w : World (catalog contracts))
    (fs : List (Frame (catalog contracts))) (ρ : Run contracts) : Run contracts :=
  { pfx := ρ.pfx, worlds := w :: ρ.worlds, frames := fs ++ ρ.frames }

section Run

variable {contracts : List Contract} (main : Nat) (roles : Fin contracts.length → Role)
  (ctor : (k : Fin contracts.length) → Bytes → Option (Prog contracts[k] [] []))
  (entry : (k : Fin contracts.length) → Bytes → Option (Entry contracts[k] Bytes))
  (F : Fixed) (wire : Wire)

/-- The run from a boundary (the history `h`, `n` actions issued, the world
`w`) through at most the given number of further actions. -/
noncomputable def go (r : Bound) (e : SessionEnv) (h : List Event) (n : Nat)
    (w : World (catalog contracts)) : Nat → Run contracts
  | 0 => ⟨⟨h, none⟩, [], []⟩
  | k + 1 =>
    match e.requests h n with
    | none => ⟨⟨h, lastOutcome h⟩, [], []⟩
    | some a =>
      let s := step entry F wire r e h n w a
      if s.stops then ⟨⟨h, none⟩, [], s.frames⟩
      else (go r e (h ++ s.events) (n + 1) s.world k).after s.world s.frames

/-- **The intrinsic session run** of the session world `w` in the environment
`e` at the bound `r`. -/
noncomputable def run (w : SessionWorld contracts) (e : SessionEnv) (r : Bound) : Run contracts :=
  match w with
  | .boundary w => go entry F wire r e [] 0 w r.horizon
  | .fresh =>
    let s := deploy main roles ctor F wire r e
    if s.stops then ⟨⟨[], none⟩, [], s.frames⟩
    else (go entry F wire r e s.events 0 s.world r.horizon).after s.world s.frames

/-! ## Unfolding -/

variable {main roles ctor entry F wire} {r : Bound} {e : SessionEnv} {h : List Event} {n : Nat}
  {w : World (catalog contracts)}

theorem go_zero : go entry F wire r e h n w 0 = ⟨⟨h, none⟩, [], []⟩ := rfl

/-- No further action: the prefix is final. -/
theorem go_idle {k : Nat} (idle : e.requests h n = none) :
    go entry F wire r e h n w (k + 1) = ⟨⟨h, lastOutcome h⟩, [], []⟩ := by
  simp only [go, idle]

/-- An action whose frame exhausts or diverges stops the session. -/
theorem go_stops {k : Nat} {a : Action} (next : e.requests h n = some a)
    (stops : (step entry F wire r e h n w a).stops = true) :
    go entry F wire r e h n w (k + 1) =
      ⟨⟨h, none⟩, [], (step entry F wire r e h n w a).frames⟩ := by
  simp only [go, next, stops, if_true]

/-- A completed action: its events, world and frames, then the run from the
next boundary. -/
theorem go_step {k : Nat} {a : Action} (next : e.requests h n = some a)
    (completes : (step entry F wire r e h n w a).stops = false) :
    go entry F wire r e h n w (k + 1) =
      let s := step entry F wire r e h n w a
      (go entry F wire r e (h ++ s.events) (n + 1) s.world k).after s.world s.frames := by
  simp only [go, next, completes, Bool.false_eq_true, if_false]

theorem run_boundary :
    run main roles ctor entry F wire (.boundary w) e r = go entry F wire r e [] 0 w r.horizon :=
  rfl

/-- A deployment that exhausts or diverges stops the session. -/
theorem run_fresh_stops (stops : (deploy main roles ctor F wire r e).stops = true) :
    run main roles ctor entry F wire .fresh e r =
      ⟨⟨[], none⟩, [], (deploy main roles ctor F wire r e).frames⟩ := by
  simp only [run, stops, if_true]

/-- A completed deployment: its event, world and frames, then the run from the
first boundary. -/
theorem run_fresh (completes : (deploy main roles ctor F wire r e).stops = false) :
    run main roles ctor entry F wire .fresh e r =
      let s := deploy main roles ctor F wire r e
      (go entry F wire r e s.events 0 s.world r.horizon).after s.world s.frames := by
  simp only [run, completes, Bool.false_eq_true, if_false]

end Run

/-! ## Consistency and monotonicity

A larger bound observes more actions with the same failures, so its run
extends the smaller one in all three projections at once (`run_mono`). -/

/-- `a` is below `b`: its prefix is a prefix of `b`'s, and its worlds and
frames lead `b`'s. -/
def Run.Le {contracts : List Contract} (a b : Run contracts) : Prop :=
  a.pfx.Le b.pfx ∧ a.worlds <+: b.worlds ∧ a.frames <+: b.frames

theorem Run.Le.refl {contracts : List Contract} (a : Run contracts) : a.Le a :=
  ⟨Prefix.Le.refl _, List.prefix_refl _, List.prefix_refl _⟩

theorem Run.Le.after {contracts : List Contract} {a b : Run contracts}
    (w : World (catalog contracts)) (fs : List (Frame (catalog contracts))) (le : a.Le b) :
    (a.after w fs).Le (b.after w fs) :=
  ⟨le.1, List.cons_prefix_cons.2 ⟨rfl, le.2.1⟩, (List.prefix_append_right_inj fs).2 le.2.2⟩

section Mono

variable {contracts : List Contract} {main : Nat} {roles : Fin contracts.length → Role}
  {ctor : (k : Fin contracts.length) → Bytes → Option (Prog contracts[k] [] [])}
  {entry : (k : Fin contracts.length) → Bytes → Option (Entry contracts[k] Bytes)}
  {F : Fixed} {wire : Wire} {r r' : Bound} {e : SessionEnv}

/-- A run from a boundary keeps the boundary's history. -/
theorem go_extends : ∀ (k : Nat) (h : List Event) (n : Nat) (w : World (catalog contracts)),
    h <+: (go entry F wire r e h n w k).pfx.events
  | 0, _, _, _ => List.prefix_refl _
  | k + 1, h, n, w => by
    simp only [go]
    split
    · exact List.prefix_refl _
    · split
      · exact List.prefix_refl _
      · exact (List.prefix_append _ _).trans (go_extends k _ _ _)

/-- More actions extend the run from a boundary. -/
theorem go_mono : ∀ (k k' : Nat) (h : List Event) (n : Nat) (w : World (catalog contracts)),
    k ≤ k' → (go entry F wire r e h n w k).Le (go entry F wire r e h n w k')
  | 0, k', h, n, w, _ => ⟨⟨go_extends k' h n w, .inl rfl⟩, List.nil_prefix, List.nil_prefix⟩
  | k + 1, 0, _, _, _, le => absurd le (Nat.not_succ_le_zero k)
  | k + 1, k' + 1, h, n, w, le => by
    simp only [go]
    split
    · exact Run.Le.refl _
    · split
      · exact Run.Le.refl _
      · exact (go_mono k k' _ _ _ (Nat.le_of_succ_le_succ le)).after _ _

/-- The step reads the bound's failures only. -/
theorem step_bound (same : r.fails = r'.fails) (h : List Event) (n : Nat)
    (w : World (catalog contracts)) (a : Action) :
    step entry F wire r e h n w a = step entry F wire r' e h n w a := by
  cases a <;> simp only [step, request, same]

theorem go_bound (same : r.fails = r'.fails) :
    ∀ (k : Nat) (h : List Event) (n : Nat) (w : World (catalog contracts)),
      go entry F wire r e h n w k = go entry F wire r' e h n w k
  | 0, _, _, _ => rfl
  | k + 1, h, n, w => by
    simp only [go, step_bound same, go_bound same k]

/-- The deployment reads the bound's deployment failure only. -/
theorem deploy_bound (same : r.deployFails = r'.deployFails) :
    deploy main roles ctor F wire r e = deploy main roles ctor F wire r' e := by
  simp only [deploy, same]

/-- **A larger bound extends the run** in its prefix, worlds and frames. -/
theorem run_mono (w : SessionWorld contracts) (le : r ≤ r') :
    (run main roles ctor entry F wire w e r).Le (run main roles ctor entry F wire w e r') := by
  cases w with
  | boundary w =>
    simp only [run, go_bound le.2.2]
    exact go_mono _ _ _ _ _ le.1
  | fresh =>
    simp only [run, deploy_bound le.2.1, go_bound le.2.2]
    split
    · exact Run.Le.refl _
    · exact (go_mono _ _ _ _ _ le.1).after _ _

end Mono

section Interface

variable {contracts : List Contract} (main : Nat) (roles : Fin contracts.length → Role)
  (ctor : (k : Fin contracts.length) → Bytes → Option (Prog contracts[k] [] []))
  (entry : (k : Fin contracts.length) → Bytes → Option (Entry contracts[k] Bytes))
  (F : Fixed) (wire : Wire) (w : SessionWorld contracts) (e : SessionEnv) {r r' : Bound}

/-- **Consistent**: the prefixes of one world and environment, in the bound
order (the shape `Roadmap.Lang.consistent` needs). -/
theorem run_consistent :
    Prefixes.Consistent fun r => (run main roles ctor entry F wire w e r).pfx :=
  fun _ _ le => (run_mono w le).1

/-- The boundary worlds at a smaller bound lead those at a larger one. -/
theorem worlds_mono (le : r ≤ r') :
    (run main roles ctor entry F wire w e r).worlds <+:
      (run main roles ctor entry F wire w e r').worlds :=
  (run_mono w le).2.1

/-- The executed frames at a smaller bound lead those at a larger one. -/
theorem frames_mono (le : r ≤ r') :
    (run main roles ctor entry F wire w e r).frames <+:
      (run main roles ctor entry F wire w e r').frames :=
  (run_mono w le).2.2

end Interface

/-- Admissible bounds without resource failure have common upper bounds. -/
theorem directed {r r' : Bound} (good : r.Admissible ∧ r.NoFail) (good' : r'.Admissible ∧ r'.NoFail) :
    ∃ r'' : Bound, (r''.Admissible ∧ r''.NoFail) ∧ r ≤ r'' ∧ r' ≤ r'' :=
  let ⟨r'', noFail, le, le'⟩ := Bound.directed good.2 good'.2
  ⟨r'', ⟨trivial, noFail⟩, le, le'⟩

end Solidity.Semantics.IntrinsicSession
