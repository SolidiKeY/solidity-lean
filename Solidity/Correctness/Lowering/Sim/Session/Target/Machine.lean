import Solidity.Correctness.IntrinsicSession.Run
import Solidity.Correctness.Sim.Observation

/-! The intrinsic session run as a small-step machine (plan step
`ls1n-intrinsic-machine`, definitions). A state is a transaction boundary:
the history, the typed world, the number of actions issued and what is pending
there (the deployment, an action, nothing more, or a stopped frame). One step
is the deployment or the one-action `step` of `IntrinsicSession/Step.lean`;
`observe` is the prefix so far, final only once no action follows.

The step reads the bound's failures (never its horizon), so the machine is
indexed by a bound whose horizon it ignores (`machine_congr`). -/
namespace Solidity.Correctness.Lowering.Sim.Session

open Solidity.Roadmap Solidity.Correctness.Sim Solidity.Semantics.IntrinsicSession
open Solidity.ContractWorld (World Entry Role)

/-- What is pending at a boundary. -/
inductive Pending where
  | deploy
  | action
  | idle
  | stopped
  deriving DecidableEq

/-- A machine state: the history, the typed world, the actions issued and what
is pending. -/
structure State (contracts : List Contract) where
  history : List Event
  world : World (catalog contracts)
  issued : Nat
  pending : Pending

/-- The prefix so far: final with the last outcome once the session is idle. -/
def State.observe {contracts : List Contract} (s : State contracts) : Prefix Event Outcome :=
  ⟨s.history, if s.pending = .idle then lastOutcome s.history else none⟩

/-- Where a session world starts. -/
def State.start {contracts : List Contract} (roles : Fin contracts.length → Role) (e : SessionEnv) :
    SessionWorld contracts → State contracts
  | .fresh => ⟨[], initial roles e, 0, .deploy⟩
  | .boundary w => ⟨[], w, 0, .action⟩

section Machine

variable {contracts : List Contract} (main : Nat) (roles : Fin contracts.length → Role)
  (ctor : (k : Fin contracts.length) → Bytes → Option (Prog contracts[k] [] []))
  (entry : (k : Fin contracts.length) → Bytes → Option (Entry contracts[k] Bytes))
  (F : Fixed) (wire : Wire)

/-- The successor of a state: the deployment, the next action, the end of the
session, or none once idle or stopped. -/
noncomputable def next (r : Bound) (e : SessionEnv) (s : State contracts) : Option (State contracts) :=
  match s with
  | ⟨h, w, n, .deploy⟩ =>
    let d := deploy main roles ctor F wire r e
    some (if d.stops then ⟨h, w, n, .stopped⟩ else ⟨d.events, d.world, 0, .action⟩)
  | ⟨h, w, n, .action⟩ =>
    match e.requests h n with
    | none => some ⟨h, w, n, .idle⟩
    | some a =>
      let t := step entry F wire r e h n w a
      some (if t.stops then ⟨h, w, n, .stopped⟩ else ⟨h ++ t.events, t.world, n + 1, .action⟩)
  | ⟨_, _, _, .idle⟩ => none
  | ⟨_, _, _, .stopped⟩ => none

/-- **The session machine** of the session world `w` in `e`, with the failures
of `r`. -/
noncomputable def machine (w : SessionWorld contracts) (e : SessionEnv) (r : Bound) : Machine where
  State := State contracts
  initial := State.start roles e w
  step s t := next main roles ctor entry F wire r e s = some t
  observe := State.observe

/-- Only the bound's failures matter. -/
theorem machine_congr (w : SessionWorld contracts) (e : SessionEnv) {r r' : Bound}
    (same : r.deployFails = r'.deployFails ∧ r.fails = r'.fails) :
    machine main roles ctor entry F wire w e r = machine main roles ctor entry F wire w e r' := by
  have : next main roles ctor entry F wire r e = next main roles ctor entry F wire r' e := by
    funext s
    rcases s with ⟨h, w, n, _ | _ | _ | _⟩ <;>
      simp only [next, deploy_bound (main := main) (roles := roles) (ctor := ctor) (F := F)
        (wire := wire) (e := e) same.1, step_bound (entry := entry) (F := F) (wire := wire)
        (e := e) same.2]
  simp only [machine, this]

end Machine

/-! ## Paths from the front

`Star` grows at the tail; the run is read from the front. -/

/-- Zero or more transitions, grown at the front. -/
inductive Path {S : Type} (step : S → S → Prop) : S → S → Prop where
  | refl (s) : Path step s s
  | head {s t u} : step s t → Path step t u → Path step s u

theorem Path.tail {S : Type} {step : S → S → Prop} {s t u : S}
    (p : Path step s t) (edge : step t u) : Path step s u := by
  induction p with
  | refl => exact .head edge (.refl _)
  | head e _ ih => exact .head e (ih edge)

theorem Path.ofStar {S : Type} {step : S → S → Prop} {s t : S} (p : Star step s t) :
    Path step s t := by
  induction p with
  | refl => exact .refl _
  | tail _ edge ih => exact ih.tail edge

/-- A state without successor ends every path from it. -/
theorem Path.stuck {S : Type} {step : S → S → Prop} {s t : S} (p : Path step s t)
    (stuck : ∀ u, ¬ step s u) : t = s := by
  cases p with
  | refl => rfl
  | head e _ => exact absurd e (stuck _)

end Solidity.Correctness.Lowering.Sim.Session
