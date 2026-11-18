import Solidity.Correctness.Lowering.Sim.Session.Backward.NoDiagram

/-! The session machine with a chosen horizon (v2 of the target machine, next
to the frozen `machine`; plan step `ls2s-session-diagrams`, lane backward).

`machine` runs without bound, and the Source session machine cannot follow it
(`NoDiagram.lean`). `boundedMachine` runs the same steps (`next`) from the same
start, but its first step chooses how many it will take, as `sourceMachine`'s
first step chooses its horizon. It reaches exactly the observations of
`machine` (`bounded_reaches`), so its coverage is `covers_noFail`
(`bounded_covers`). -/
namespace Solidity.Correctness.Lowering.Sim.Session

open Solidity.Roadmap (Event Outcome SessionEnv Fixed Bytes Prefix)
open Solidity.Semantics.IntrinsicSession
open Solidity.ContractWorld (Entry Role)
open Solidity.Correctness.Sim (Machine Star)

/-- A step of a machine with a chosen horizon: choose it, or take one step of
`nxt` and spend one unit. -/
inductive BoundedStep {S : Type} (nxt : S → Option S) (start : S) :
    Option (Nat × S) → Option (Nat × S) → Prop where
  | choose (k : Nat) : BoundedStep nxt start none (some (k, start))
  | step {k : Nat} {s t : S} : nxt s = some t → BoundedStep nxt start (some (k + 1, s)) (some (k, t))

/-- With enough budget, a bounded run takes every step of an unbounded one. -/
theorem BoundedStep.lift {S : Type} {nxt : S → Option S} {start s t : S}
    (path : Star (fun s t => nxt s = some t) s t) (k : Nat) :
    ∃ m, Star (BoundedStep nxt start) (some (m, s)) (some (k, t)) := by
  induction path generalizing k with
  | refl => exact ⟨k, .refl _⟩
  | tail _ edge ih =>
    obtain ⟨m, run⟩ := ih (k + 1)
    exact ⟨m, .tail run (.step edge)⟩

section Machine

variable {contracts : List Contract} (main : Nat) (roles : Fin contracts.length → Role)
  (ctor : (k : Fin contracts.length) → Bytes → Option (Prog contracts[k] [] []))
  (entry : (k : Fin contracts.length) → Bytes → Option (Entry contracts[k] Bytes))
  (F : Fixed) (wire : Wire) (w : SessionWorld contracts) (e : SessionEnv)

/-- **The session machine with a chosen horizon**, without resource failure:
no state before the horizon is chosen, then a boundary state of `machine` with
the steps left. -/
noncomputable def boundedMachine : Machine where
  State := Option (Nat × State contracts)
  initial := none
  step := BoundedStep (next main roles ctor entry F wire { horizon := 0 } e) (State.start roles e w)
  observe
    | none => ⟨[], none⟩
    | some (_, s) => s.observe

/-- Every reachable state of the frozen machine is reached, with any budget
left, by the machine with a chosen horizon. -/
theorem bounded_reaches {s : State contracts}
    (reach : (machine₀ main roles ctor entry F wire w e).Reachable s) (k : Nat) :
    (boundedMachine main roles ctor entry F wire w e).Reachable (some (k, s)) :=
  let ⟨m, run⟩ := BoundedStep.lift (start := State.start roles e w) reach k
  (Star.single (BoundedStep.choose m)).trans run

/-- **Coverage** of every bound without resource failure. -/
theorem bounded_covers {r : Bound} (good : r.NoFail) :
    ∃ s, (boundedMachine main roles ctor entry F wire w e).Reachable s ∧
      (boundedMachine main roles ctor entry F wire w e).observe s =
        (run main roles ctor entry F wire w e r).pfx :=
  let ⟨s, reach, obs⟩ := covers_noFail (main := main) (roles := roles) (ctor := ctor)
    (entry := entry) (F := F) (wire := wire) w e good
  ⟨some (0, s), bounded_reaches main roles ctor entry F wire w e reach 0, obs⟩

end Machine

end Solidity.Correctness.Lowering.Sim.Session
