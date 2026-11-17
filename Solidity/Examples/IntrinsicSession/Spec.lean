import Solidity.Correctness.IntrinsicSession.View

/-! Checks of the session's hash accounting on a one-contract world: a session
resumed at a world, whose first action is one determined request. The
contract, its resolution, the world and the request stay arbitrary: the
accounting is checked structurally, never by evaluating a frame or the stored
keys. -/
namespace Solidity.Examples.IntrinsicSession.Spec

open Solidity.Roadmap Solidity.Semantics Solidity.Semantics.IntrinsicSession
open Solidity.Goals.IntrinsicSession (Code TypedWorld)
open Solidity.ContractWorld (World Handle Entry Role)
open Solidity.Lowering.V08.EnvironmentProjection (liftWord liftAddress requestContext)

/-- A resumed session whose first action is the affordable request `q` to an
installed instance with a resolved entry, at a bound with room for it whose
frame does not fail for lack of resources. -/
structure OneRequest (C : Contract) (code : Code) (w : World code.catalog) (F : Fixed)
    (r : Bound) (e : SessionEnv) where
  one : code.contracts = [C]
  q : Request
  k : Fin code.contracts.length
  st : Storage code.contracts[k]
  en : Entry code.contracts[k] Bytes
  room : 0 < r.horizon
  enough : r.fails 0 = false
  next : e.requests [] 0 = some (.request q)
  funded : Funded F e [] q
  installed : w.accounts (liftAddress q.target) = some ⟨k, st⟩
  resolved : code.entry k q.input = some en

variable {C : Contract} {code : Code} {w : World code.catalog} {F : Fixed} {r : Bound}
  {e : SessionEnv} (s : OneRequest C code w F r e)

namespace OneRequest

/-- The session start: the code, resumed at `w`. -/
abbrev start (_ : OneRequest C code w F r e) : Start := ⟨code, .boundary w⟩

/-- The world the frame runs from: `w` at the request's time, transaction-local
cells reset. -/
abbrev base (s : OneRequest C code w F r e) : World code.catalog :=
  (w.atTime (liftWord s.q.timestamp)).resetTransient

/-- The request's frame: the arguments of `Frame.call`, with no answers. -/
abbrev frame : Frame (catalog code.contracts) :=
  ⟨s.base, .call ⟨liftAddress s.q.target⟩ s.en, requestContext s.q []⟩

/-- The request's observer at the fuel `n`. -/
noncomputable abbrev observed (n : Nat) : IntrinsicStorage.Audit (World code.catalog × Bytes) :=
  IntrinsicStorage.Frame.call n s.base ⟨liftAddress s.q.target⟩ s.en (requestContext s.q [])

/-- The step runs exactly the request's frame. -/
theorem step_frames :
    (step code.entry F wire r e [] 0 w (.request s.q)).frames = [s.frame] := by
  dsimp only [step, request]
  rw [if_neg (not_not_intro s.funded)]
  split
  · rename_i none
    rw [s.installed] at none
    cases none
  · rename_i k' st' hk
    rw [s.installed] at hk
    cases hk
    rw [s.resolved]
    simp only [s.enough, Bool.false_eq_true, if_false]
    split <;> rfl

/-- The frame is among the run's executed frames, whether or not it completes. -/
theorem ran : s.frame ∈ (runOf F s.start e r).frames := by
  obtain ⟨k, hk⟩ : ∃ k, r.horizon = k + 1 := ⟨r.horizon - 1, by have := s.room; omega⟩
  have frames : s.frame ∈ (step code.entry F wire r e [] 0 w (.request s.q)).frames := by
    rw [s.step_frames]
    exact List.mem_singleton.2 rfl
  simp only [runOf, run, hk, go, s.next]
  split
  · exact frames
  · exact List.mem_append_left _ frames

/-- **`hashed` contains the inputs of the request's `Frame.call`**, at a fuel
whose result is the actual `World.call`, and `slotHashed` its slots. -/
theorem inputs_hashed (done : ∃ n, (s.observed n).result ≠ .error .diverge) :
    ∃ n, (s.observed n).result =
        s.base.call ⟨liftAddress s.q.target⟩ s.en (requestContext s.q []) ∧
      (∀ b ∈ (s.observed n).inputs.hashed, b ∈ hashed F s.start e r) ∧
      ∀ b ∈ (s.observed n).inputs.slots, b ∈ slotHashed F s.start e r := by
  obtain ⟨n, result, inputs⟩ := Frame.inputs_call done
  refine ⟨n, result, fun b mem => frame_hashed s.ran ?_, fun b mem => frame_slotHashed s.ran ?_⟩
  · rw [show s.frame.inputs = (s.observed n).inputs from inputs]
    exact mem
  · rw [show s.frame.inputs = (s.observed n).inputs from inputs]
    exact mem

/-- **A reverting transaction keeps its inputs**: when the frame reverts, the
actual call reverts and what the frame hashed before is accounted for. -/
example {n : Nat} (reverts : (s.observed n).result = .error .revert) :
    ∃ m, s.base.call ⟨liftAddress s.q.target⟩ s.en (requestContext s.q []) = .error .revert ∧
      (s.observed m).result = .error .revert ∧
      ∀ b ∈ (s.observed m).inputs.hashed, b ∈ hashed F s.start e r := by
  have actual := (IntrinsicStorage.Frame.call_approx n s.base ⟨liftAddress s.q.target⟩ s.en
    (requestContext s.q [])).eq (by rw [reverts]; exact fun h => nomatch h)
  obtain ⟨m, result, mem, _⟩ := s.inputs_hashed (F := F) ⟨n, by rw [reverts]; exact fun h => nomatch h⟩
  exact ⟨m, actual.symm.trans reverts, result.trans (actual.symm.trans reverts), mem⟩

/-- **`slotHashed` contains `stored` of the resumed world**, at every bound,
the empty one included, and so does `hashed`. -/
example (r' : Bound) (b : Bytes) (mem : b ∈ IntrinsicStorage.stored w) :
    b ∈ slotHashed F s.start e r' ∧ b ∈ hashed F s.start e r' :=
  ⟨stored_slotHashed mem, slotHashed_sub (stored_slotHashed mem)⟩

/-- The same through the spec and its view. -/
example (r' : Bound) (b : Bytes) (mem : b ∈ (view F).stored ⟨code, w⟩) :
    b ∈ (spec F).slotHashed ((spec F).ofWorld ((view F).resume ⟨code, w⟩)) e r' :=
  stored_resume F ⟨code, w⟩ e r' mem

/-- **The session is not event-free**: a frame that returns `d` shows the
transaction with `success d`. -/
example (d : Bytes) (returns : ((w.atTime (liftWord s.q.timestamp)).transact fun v =>
      v.call (⟨liftAddress s.q.target⟩ : Handle s.k) s.en (requestContext s.q [])).2 = .ok d) :
    [Event.tx s.q.sender s.q.target s.q.value s.q.timestamp s.q.input (.success d)] <+:
      ((spec F).lang.sem s.start e r).events := by
  obtain ⟨k, hk⟩ : ∃ k, r.horizon = k + 1 := ⟨r.horizon - 1, by have := s.room; omega⟩
  have events : (step code.entry F wire r e [] 0 w (.request s.q)).events =
      [Event.tx s.q.sender s.q.target s.q.value s.q.timestamp s.q.input (.success d)] := by
    dsimp only [step, request]
    rw [if_neg (not_not_intro s.funded)]
    split
    · rename_i none
      rw [s.installed] at none
      cases none
    · rename_i k' st' hk
      rw [s.installed] at hk
      cases hk
      rw [s.resolved]
      simp only [s.enough, Bool.false_eq_true, if_false, responses_wire, returns, outcomeOf]
  have stops : (step code.entry F wire r e [] 0 w (.request s.q)).stops = false := by
    dsimp only [step, request]
    rw [if_neg (not_not_intro s.funded)]
    split
    · rfl
    · rename_i k' st' hk
      rw [s.installed] at hk
      cases hk
      rw [s.resolved]
      simp only [s.enough, Bool.false_eq_true, if_false, responses_wire, returns, outcomeOf]
  show _ <+: (go code.entry F wire r e [] 0 w r.horizon).pfx.events
  rw [hk, go_step s.next stops]
  exact events ▸ go_extends k _ _ _

/-- The boundary the session starts at, and the fixed parameters of the spec. -/
example : (view F).Boundary s.start e [] 0 ⟨code, w⟩ ∧ (spec F).fixed = F :=
  ⟨Boundary.resume F ⟨code, w⟩ e, rfl⟩

end OneRequest

end Solidity.Examples.IntrinsicSession.Spec
