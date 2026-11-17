import Solidity.Correctness.Lowering.Sim.Session.Target
import Solidity.Examples.IntrinsicSession.Run

/-! Checks of the session machine on the one-contract session of
`Examples/IntrinsicSession/Run.lean`: coverage reaches the deployment and the
request, and the final outcome once the session is idle; realization bounds the
state after the deployment by a run without resource failure. -/
namespace Solidity.Examples.Lowering.Sim.Session.Target

open Solidity.Roadmap Solidity.Correctness.Sim Solidity.Semantics.IntrinsicSession
open Solidity.Correctness.Lowering.Sim.Session
open Solidity.Examples.IntrinsicSession.Run
open Solidity.ContractWorld (World Entry Role)

variable {C : Contract} {roles : Fin [C].length → Role}
  {ctor : (k : Fin [C].length) → Bytes → Option (Prog [C][k] [] [])}
  {entry : (k : Fin [C].length) → Bytes → Option (Entry [C][k] Bytes)}
  {F : Fixed} {wire : Wire} {r : Bound} {e : SessionEnv}
  (s : TwoActions C roles ctor entry F wire r e)

/-- With room for the request, the machine reaches both events. -/
example (one : r.horizon = 1) :
    ∃ t, (machine 0 roles ctor entry F wire .fresh e r).Reachable t ∧
      t.observe = ⟨[s.deployed, s.transacted], none⟩ := by
  obtain ⟨t, reach, obs⟩ := covers (main := 0) (roles := roles) (ctor := ctor) (entry := entry)
    (F := F) (wire := wire) .fresh e r
  refine ⟨t, reach, obs.trans ?_⟩
  rw [run_fresh s.deploy_completes, s.deploy_eq, one]
  dsimp only
  rw [go_step s.next (by rw [s.step_eq]), s.step_eq]
  rfl

/-- When no action follows the request, the machine reaches the request's
outcome as the final observation. -/
example (two : r.horizon = 2) (idle : e.requests [s.deployed, s.transacted] 1 = none) :
    ∃ t, (machine 0 roles ctor entry F wire .fresh e r).Reachable t ∧
      t.observe = ⟨[s.deployed, s.transacted], some (.success s.d)⟩ := by
  obtain ⟨t, reach, obs⟩ := covers (main := 0) (roles := roles) (ctor := ctor) (entry := entry)
    (F := F) (wire := wire) .fresh e r
  refine ⟨t, reach, obs.trans ?_⟩
  rw [run_fresh s.deploy_completes, s.deploy_eq, two]
  dsimp only
  rw [go_step s.next (by rw [s.step_eq]), s.step_eq]
  dsimp only
  rw [show [s.deployed] ++ [s.transacted] = [s.deployed, s.transacted] from rfl, go_idle idle]
  rfl

/-- The state after the deployment is reachable in the machine without
failures, and realized below a run without resource failure. -/
example (noFail : r.NoFail) :
    ∃ r', (r'.Admissible ∧ r'.NoFail) ∧
      (State.observe (⟨[s.deployed], s.w1, 0, .action⟩ : Solidity.Correctness.Lowering.Sim.Session.State [C])).Le
        (run 0 roles ctor entry F wire .fresh e r').pfx := by
  apply realizes_noFail
  refine Star.single ?_
  show next 0 roles ctor entry F wire { horizon := 0 } e ⟨[], initial roles e, 0, .deploy⟩ = _
  simp only [next, deploy_bound (r := { horizon := 0 }) (r' := r) noFail.1.symm, s.deploy_eq,
    Bool.false_eq_true, if_false]

end Solidity.Examples.Lowering.Sim.Session.Target
