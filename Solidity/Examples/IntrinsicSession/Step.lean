import Solidity.Correctness.IntrinsicSession.Step

/-! Checks of the one-action step on a one-contract world. The contract, its
resolution, the world, the request and the frame's result stay arbitrary: the
step is checked structurally, never by evaluating a run. -/
namespace Solidity.Examples.IntrinsicSession.Step

open Solidity.Roadmap Solidity.Semantics.IntrinsicSession
open Solidity.ContractWorld (World Handle Entry Role)
open Solidity.Lowering.V08.EnvironmentProjection (liftWord liftAddress requestContext)

variable (C : Contract) (roles : Fin [C].length → Role)
  (ctor : (k : Fin [C].length) → Bytes → Option (Prog [C][k] [] []))
  (entry : (k : Fin [C].length) → Bytes → Option (Entry [C][k] Bytes))
  (F : Fixed) (wire : Wire) (r : Bound) (e : SessionEnv)

/-- An affordable request to an installed instance whose input resolves shows
exactly the outcome of `World.transact` of the actual `World.call` at the
request's time with `requestContext`, reaches its world when it completes, and
records one call frame with exactly those arguments. -/
theorem request_transacts (h : List Event) (n : Nat) (w : World (catalog [C])) (q : Request)
    (k : Fin [C].length) (st : Storage [C][k]) (en : Entry [C][k] Bytes)
    (funded : Funded F e h q) (installed : w.accounts (liftAddress q.target) = some ⟨k, st⟩)
    (resolved : entry k q.input = some en) (enough : r.fails n = false) :
    let w0 := w.atTime (liftWord q.timestamp)
    let target : Handle k := ⟨liftAddress q.target⟩
    let ctx := requestContext q (responses wire e h)
    let res := w0.transact fun v => v.call target en ctx
    let s := step entry F wire r e h n w (.request q)
    s.events = (outcomeOf res.2).toList.map
        (Event.tx q.sender q.target q.value q.timestamp q.input) ∧
      (∀ out, outcomeOf res.2 = some out → s.world = res.1 ∧ s.stops = false) ∧
      s.frames = [⟨w0.resetTransient, .call target en, ctx⟩] := by
  dsimp only [step, request]
  rw [if_neg (not_not_intro funded)]
  split
  · simp_all
  · rename_i k' st' hk
    rw [installed] at hk
    cases hk
    rw [resolved]
    dsimp only
    simp only [enough, Bool.false_eq_true, ↓reduceIte]
    split <;> simp_all

/-- A determined body that returns `d` shows `success d`, at its world. -/
theorem request_returns (h : List Event) (n : Nat) (w : World (catalog [C])) (q : Request)
    (k : Fin [C].length) (st : Storage [C][k]) (en : Entry [C][k] Bytes) (d : Bytes)
    (funded : Funded F e h q) (installed : w.accounts (liftAddress q.target) = some ⟨k, st⟩)
    (resolved : entry k q.input = some en) (enough : r.fails n = false)
    (returns : ((w.atTime (liftWord q.timestamp)).transact fun v =>
      v.call (⟨liftAddress q.target⟩ : Handle k) en
        (requestContext q (responses wire e h))).2 = .ok d) :
    (step entry F wire r e h n w (.request q)).events =
      [Event.tx q.sender q.target q.value q.timestamp q.input (.success d)] := by
  have := (request_transacts C entry F wire r e h n w q k st en funded installed resolved
    enough).1
  rw [this, returns]
  rfl

/-- An unaffordable request is dropped: no event, the same world, no frame. -/
theorem request_dropped (h : List Event) (n : Nat) (w : World (catalog [C])) (q : Request)
    (unfunded : ¬ Funded F e h q) :
    let s := step entry F wire r e h n w (.request q)
    s.events = [] ∧ s.world = w ∧ s.frames = [] := by
  dsimp only [step, request]
  rw [if_pos unfunded]
  exact ⟨rfl, rfl, rfl⟩

/-- The deployment of the main contract records one create frame: from the
initial world, at `Fixed.createAddress`, with the deployment context. -/
theorem deploy_creates (body : Prog [C][(⟨0, Nat.zero_lt_succ 0⟩ : Fin [C].length)] [] [])
    (resolved : ctor ⟨0, Nat.zero_lt_succ 0⟩ e.deployArgs = some body) :
    (deploy 0 roles ctor F wire r e).frames =
      [⟨(initial roles e).resetTransient,
        .create ⟨0, Nat.zero_lt_succ 0⟩ (liftAddress (F.createAddress e.deployer e.deployNonce)) body,
        deployContext wire e⟩] := by
  simp only [deploy, show 0 < [C].length from Nat.zero_lt_succ 0, dite_true]
  rw [resolved]
  dsimp only
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

/-- A credit appends exactly its event and runs no frame. -/
example (h : List Event) (n : Nat) (w : World (catalog [C])) (t : Address) (v : Roadmap.Word) :
    let s := step entry F wire r e h n w (.credit t v)
    s.events = [.credit t v] ∧ s.frames = [] := ⟨rfl, rfl⟩

end Solidity.Examples.IntrinsicSession.Step
