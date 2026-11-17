import Solidity.Correctness.IntrinsicSession.Run

/-! Checks of the session run on a one-contract world: a deployment, then one
determined request. The contract, its resolution, the environment and the two
frames' results stay arbitrary: the run is checked structurally, never by
evaluating a frame. -/
namespace Solidity.Examples.IntrinsicSession.Run

open Solidity.Roadmap Solidity.Semantics.IntrinsicSession
open Solidity.ContractWorld (World Handle Entry Role)
open Solidity.Lowering.V08.EnvironmentProjection (liftWord liftAddress requestContext)

/-- The only contract's index. -/
abbrev main (C : Contract) : Fin [C].length := ⟨0, Nat.zero_lt_succ 0⟩

/-- A two-action session: the main contract's constructor resolves to `body`
and its creation succeeds at `w1`; then the first action is the affordable
request `q` to an installed instance, whose resolved entry returns `d` at `w2`.
No frame of either fails for lack of resources. -/
structure TwoActions (C : Contract) (roles : Fin [C].length → Role)
    (ctor : (k : Fin [C].length) → Bytes → Option (Prog [C][k] [] []))
    (entry : (k : Fin [C].length) → Bytes → Option (Entry [C][k] Bytes))
    (F : Fixed) (wire : Wire) (r : Bound) (e : SessionEnv) where
  body : Prog [C][main C] [] []
  w1 : World (catalog [C])
  created : Handle (main C)
  q : Request
  k : Fin [C].length
  st : Storage [C][k]
  en : Entry [C][k] Bytes
  w2 : World (catalog [C])
  d : Bytes
  enough : r.deployFails = false ∧ r.fails 0 = false
  ctor_resolved : ctor (main C) e.deployArgs = some body
  creates : ((initial roles e).transact fun v => v.create (main C)
    (liftAddress (F.createAddress e.deployer e.deployNonce)) body (deployContext wire e)) =
    (w1, .ok created)
  next : e.requests [Event.deploy e.deployer e.deployValue e.deployArgs (.success [])
    (some (F.createAddress e.deployer e.deployNonce))] 0 = some (.request q)
  funded : Funded F e [Event.deploy e.deployer e.deployValue e.deployArgs (.success [])
    (some (F.createAddress e.deployer e.deployNonce))] q
  installed : w1.accounts (liftAddress q.target) = some ⟨k, st⟩
  entry_resolved : entry k q.input = some en
  returns : ((w1.atTime (liftWord q.timestamp)).transact fun v =>
    v.call (⟨liftAddress q.target⟩ : Handle k) en
      (requestContext q (responses wire e [Event.deploy e.deployer e.deployValue e.deployArgs
        (.success []) (some (F.createAddress e.deployer e.deployNonce))]))) = (w2, .ok d)

variable {C : Contract} {roles : Fin [C].length → Role}
  {ctor : (k : Fin [C].length) → Bytes → Option (Prog [C][k] [] [])}
  {entry : (k : Fin [C].length) → Bytes → Option (Entry [C][k] Bytes)}
  {F : Fixed} {wire : Wire} {r : Bound} {e : SessionEnv}
  (s : TwoActions C roles ctor entry F wire r e)

namespace TwoActions

/-- The deployment's event. -/
abbrev deployed (_ : TwoActions C roles ctor entry F wire r e) : Event :=
  .deploy e.deployer e.deployValue e.deployArgs (.success [])
    (some (F.createAddress e.deployer e.deployNonce))

/-- The request's event. -/
def transacted : Event := .tx s.q.sender s.q.target s.q.value s.q.timestamp s.q.input (.success s.d)

/-- The create frame: from the initial world, at `Fixed.createAddress`. -/
def createFrame : Frame (catalog [C]) :=
  ⟨(initial roles e).resetTransient,
    .create (main C) (liftAddress (F.createAddress e.deployer e.deployNonce)) s.body,
    deployContext wire e⟩

/-- The call frame: from the world the deployment reached, at the request's time. -/
def callFrame : Frame (catalog [C]) :=
  ⟨(s.w1.atTime (liftWord s.q.timestamp)).resetTransient, .call ⟨liftAddress s.q.target⟩ s.en,
    requestContext s.q (responses wire e [s.deployed])⟩

theorem deploy_eq : deploy 0 roles ctor F wire r e =
    { events := [s.deployed], world := s.w1, frames := [s.createFrame] } := by
  simp only [deploy, show 0 < [C].length from Nat.zero_lt_succ 0, dite_true]
  rw [s.ctor_resolved]
  simp only [s.enough.1, Bool.false_eq_true, if_false, s.creates]
  rfl

include s in
theorem deploy_completes : (deploy 0 roles ctor F wire r e).stops = false := by
  rw [s.deploy_eq]

theorem step_eq : step entry F wire r e [s.deployed] 0 s.w1 (.request s.q) =
    { events := [s.transacted], world := s.w2, frames := [s.callFrame] } := by
  dsimp only [step, request]
  rw [if_neg (not_not_intro s.funded)]
  split
  · rename_i none
    rw [s.installed] at none
    cases none
  · rename_i k' st' hk
    rw [s.installed] at hk
    cases hk
    rw [s.entry_resolved]
    simp only [s.enough.2, Bool.false_eq_true, if_false]
    rw [s.returns]
    rfl

/-- With room for the request, the prefix has the two events in order, the
boundary worlds list both, and the frames are the create frame then the call
frame. -/
example (one : r.horizon = 1) : run 0 roles ctor entry F wire .fresh e r =
    ⟨⟨[s.deployed, s.transacted], none⟩, [s.w1, s.w2], [s.createFrame, s.callFrame]⟩ := by
  rw [run_fresh s.deploy_completes, s.deploy_eq, one]
  dsimp only
  rw [go_step s.next (by rw [s.step_eq]), s.step_eq]
  rfl

/-- A bound too small for the request shows a strict prefix of each. -/
theorem one (zero : r.horizon = 0) : run 0 roles ctor entry F wire .fresh e r =
    ⟨⟨[s.deployed], none⟩, [s.w1], [s.createFrame]⟩ := by
  rw [run_fresh s.deploy_completes, s.deploy_eq, zero]
  rfl

/-- When no action follows the request, a larger bound completes the session
with the request's outcome. -/
example (two : r.horizon = 2)
    (idle : e.requests [s.deployed, s.transacted] 1 = none) :
    run 0 roles ctor entry F wire .fresh e r =
      ⟨⟨[s.deployed, s.transacted], some (.success s.d)⟩, [s.w1, s.w2],
        [s.createFrame, s.callFrame]⟩ := by
  rw [run_fresh s.deploy_completes, s.deploy_eq, two]
  dsimp only
  rw [go_step s.next (by rw [s.step_eq]), s.step_eq]
  dsimp only
  rw [show [s.deployed] ++ [s.transacted] = [s.deployed, s.transacted] from rfl, go_idle idle]
  rfl

/-- Every larger bound keeps that prefix of each in front (`run_consistent`,
`worlds_mono`, `frames_mono`). -/
example {r' : Bound} (zero : r.horizon = 0) (le : r ≤ r') :
    [s.deployed] <+: (run 0 roles ctor entry F wire .fresh e r').pfx.events ∧
      [s.w1] <+: (run 0 roles ctor entry F wire .fresh e r').worlds ∧
      [s.createFrame] <+: (run 0 roles ctor entry F wire .fresh e r').frames := by
  have events : (run 0 roles ctor entry F wire .fresh e r).pfx.Le
      (run 0 roles ctor entry F wire .fresh e r').pfx :=
    run_consistent 0 roles ctor entry F wire .fresh e r r' le
  have worlds := worlds_mono 0 roles ctor entry F wire .fresh e le
  have frames := frames_mono 0 roles ctor entry F wire .fresh e le
  rw [s.one zero] at events worlds frames
  exact ⟨events.1, worlds, frames⟩

end TwoActions

/-- Two bounds without resource failure have a common upper bound. -/
example {r r' : Bound} (noFail : r.NoFail) (noFail' : r'.NoFail) :
    ∃ r'' : Bound, (r''.Admissible ∧ r''.NoFail) ∧ r ≤ r'' ∧ r' ≤ r'' :=
  directed ⟨trivial, noFail⟩ ⟨trivial, noFail'⟩

end Solidity.Examples.IntrinsicSession.Run
