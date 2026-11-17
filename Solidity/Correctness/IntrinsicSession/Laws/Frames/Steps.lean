import Solidity.Correctness.IntrinsicSession.Laws.Common

/-!
# The intrinsic session: the determined steps, unfolded

Helpers of `Laws/Frames.lean` (step `is0p-session-laws`, lane frames): the step of a resolved,
affordable request and of a resolved deployment at any bound, as the actual frame with no
answers (`callOf`, `createOf`); what a session with an empty history shows first at a bound with
resource failures (`first_tx`, `fresh_events`).
-/

namespace Solidity.Semantics.IntrinsicSession

open Solidity.Roadmap
open Solidity.Goals.IntrinsicSession (Code Good Ends Matches)
open Solidity.ContractWorld (World Handle Entry)
open Solidity.Lowering.V08.EnvironmentProjection (liftWord liftAddress requestContext)

/-- Two one-event prefixes of a history are the same event. -/
theorem prefix_head {α : Type} {a b : α} {xs l : List α} (ha : xs <+: l) (hb : [b] <+: l)
    (one : xs = [a]) : a = b := by
  subst one
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨v, eq⟩ := hb
  exact (List.cons.inj eq).1.symm

/-- A completed frame result matches its outcome. -/
theorem matches_of {res : TRes Bytes} {out : Outcome} (eq : outcomeOf res = some out) :
    Matches res out := by
  cases res with
  | ok d => cases eq; rfl
  | error hlt =>
    simp only [outcomeOf] at eq
    split at eq
    · cases eq; exact ⟨‹_›, _, rfl, fun _ => rfl⟩
    · cases eq

/-- A frame result that ends has an outcome. -/
theorem ends_of {res : TRes Bytes} (ends : Ends res) : ∃ out, outcomeOf res = some out := by
  cases res with
  | ok d => exact ⟨_, rfl⟩
  | error hlt => exact ⟨_, if_pos ends⟩

/-! ## Silent steps -/

section Walk

variable {contracts : List Contract}
  {entry : (k : Fin contracts.length) → Bytes → Option (Entry contracts[k] Bytes)}
  {F : Fixed} {wire : Wire} {r : Bound} {e : SessionEnv} {h h' : List Event} {n : Nat}
  {w w' : World (catalog contracts)}

/-- A walk keeps the history it starts from. -/
theorem walk_extends {k : Nat} (reach : walk entry F wire r e h n w k = some (h', w')) :
    h <+: h' := by
  obtain ⟨_, _, _, _, eq⟩ := walk_go k reach
  have ext := go_extends (entry := entry) (F := F) (wire := wire) (r := r) (e := e) (k + 0) h n w
  rw [eq 0] at ext
  exact ext

/-- A completed step without events is a dropped request, at every bound. -/
theorem step_silent (r : Bound) {a : Action}
    (completes : (step entry F wire (Bound.upto 0) e h n w a).stops = false)
    (silent : (step entry F wire (Bound.upto 0) e h n w a).events = []) :
    step entry F wire r e h n w a = step entry F wire (Bound.upto 0) e h n w a := by
  cases a with
  | credit t v => rfl
  | request q =>
    by_cases funded : Funded F e h q
    · exfalso
      revert completes silent
      simp only [step, request, Bool.false_eq_true, if_false, if_neg (not_not_intro funded)]
      repeat' split
      all_goals first | (intro c; cases c; done) | (intro _ s; cases s)
    · simp only [step, request, if_pos funded]

/-- A walk that shows nothing is the same walk at every bound. -/
theorem walk_quiet (r : Bound) : ∀ (k : Nat) {i : Nat} {w0 w : World (catalog contracts)},
    walk entry F wire (Bound.upto 0) e [] i w0 k = some ([], w) →
    walk entry F wire r e [] i w0 k = some ([], w)
  | 0, _, _, _, reach => reach
  | k + 1, i, w0, w, reach => by
    cases req : e.requests [] i with
    | none => simp [walk, req] at reach
    | some a =>
      cases cont : (step entry F wire (Bound.upto 0) e [] i w0 a).stops
      · simp only [walk, req, cont, Bool.false_eq_true, if_false] at reach
        have silent := List.prefix_nil.1 (walk_extends reach)
        rw [List.nil_append] at silent
        rw [silent] at reach
        simp only [walk, req, step_silent r cont silent, cont, Bool.false_eq_true, if_false,
          silent]
        exact walk_quiet r k reach
      · simp [walk, req, cont] at reach

end Walk

/-! ## The request -/

section Request

variable {F : Fixed} {x : Start} {e : SessionEnv} {r : Bound} {h : List Event} {n : Nat}
  {w : World (catalog x.code.contracts)} {q : Request} {k : Fin x.code.contracts.length}
  {st : Storage (x.code.catalog k)} {entry : Entry (x.code.catalog k) Bytes}

/-- The frame of the request `q` to a resolved entry of `k`, with no answers. -/
noncomputable abbrev callOf (w : World (catalog x.code.contracts)) (q : Request)
    (k : Fin x.code.contracts.length) (entry : Entry (x.code.catalog k) Bytes) :=
  (w.atTime (liftWord q.timestamp)).transact fun v =>
    v.call (⟨liftAddress q.target⟩ : Handle k) entry (requestContext q [])

/-- **The step of a resolved, affordable request** at any bound. -/
theorem request_eq (funded : Funded F e h q)
    (installed : w.accounts (liftAddress q.target) = some ⟨k, st⟩)
    (resolved : x.code.entry k q.input = some entry) :
    step x.code.entry F wire r e h n w (.request q) =
      let done := Event.tx q.sender q.target q.value q.timestamp q.input
      let w0 := (w.atTime (liftWord q.timestamp)).resetTransient
      let frame : Frame (catalog x.code.contracts) :=
        ⟨w0, .call ⟨liftAddress q.target⟩ entry, requestContext q []⟩
      if r.fails n then { events := [done (.revert [])], world := w0, frames := [frame] }
      else match outcomeOf (callOf w q k entry).2 with
        | some out => { events := [done out], world := (callOf w q k entry).1, frames := [frame] }
        | none => { events := [], world := w, frames := [frame], stops := true } := by
  dsimp only [step, request]
  rw [if_neg (not_not_intro funded)]
  split
  · rename_i none
    rw [installed] at none
    cases none
  · rename_i k' st' hk
    rw [installed] at hk
    cases hk
    rw [resolved]
    rfl

/-- The frame completes: its transaction, its world. -/
theorem request_done (funded : Funded F e h q)
    (installed : w.accounts (liftAddress q.target) = some ⟨k, st⟩)
    (resolved : x.code.entry k q.input = some entry) (nofail : r.fails n = false) {out : Outcome}
    (eq : outcomeOf (callOf w q k entry).2 = some out) :
    (step x.code.entry F wire r e h n w (.request q)).events =
      [Event.tx q.sender q.target q.value q.timestamp q.input out] ∧
    (step x.code.entry F wire r e h n w (.request q)).world = (callOf w q k entry).1 ∧
    (step x.code.entry F wire r e h n w (.request q)).stops = false := by
  rw [request_eq funded installed resolved]
  simp only [nofail, eq, Bool.false_eq_true, if_false, and_self]

/-- The frame exhausts or diverges: the session stops. -/
theorem request_halts (funded : Funded F e h q)
    (installed : w.accounts (liftAddress q.target) = some ⟨k, st⟩)
    (resolved : x.code.entry k q.input = some entry) (nofail : r.fails n = false)
    (eq : outcomeOf (callOf w q k entry).2 = none) :
    (step x.code.entry F wire r e h n w (.request q)).stops = true := by
  rw [request_eq funded installed resolved]
  simp only [nofail, eq, Bool.false_eq_true, if_false]

/-- The bound fails the frame: a revert with empty data. -/
theorem request_fails (funded : Funded F e h q)
    (installed : w.accounts (liftAddress q.target) = some ⟨k, st⟩)
    (resolved : x.code.entry k q.input = some entry) (fails : r.fails n = true) :
    (step x.code.entry F wire r e h n w (.request q)).events =
      [Event.tx q.sender q.target q.value q.timestamp q.input (.revert [])] := by
  rw [request_eq funded installed resolved]
  simp only [fails, if_true]

/-- A completed deployment shows its event. -/
theorem deployed_events_ne {code : Code} (completes : (deployed F code e).stops = false) :
    (deployed F code e).events ≠ [] := by
  revert completes
  simp only [deployed, deploy]
  repeat' split
  all_goals first | (intro c; cases c; done) | (intro _ s; cases s)

/-- **The first transaction at any bound**: a session standing at a boundary with an empty
history, whose next action is a resolved affordable request, shows as its first transaction the
frame's outcome, or a revert with empty data where the bound fails the frame. -/
theorem first_tx (b : (view F).Boundary x e [] n ⟨x.code, w⟩)
    (next : e.requests [] n = some (.request q)) (funded : Funded F e [] q)
    (installed : w.accounts (liftAddress q.target) = some ⟨k, st⟩)
    (resolved : x.code.entry k q.input = some entry) (r : Bound) {out : Outcome}
    (pre : [Event.tx q.sender q.target q.value q.timestamp q.input out] <+:
      ((spec F).lang.sem x e r).events) :
    outcomeOf (callOf w q k entry).2 = some out ∨ out = .revert [] := by
  obtain ⟨h0, w0, o, wk⟩ := boundary_mk.1 b
  obtain rfl := List.prefix_nil.1 (walk_extends wk)
  obtain ⟨code, _ | wb⟩ := x
  · cases stop : (deployed F code e).stops
    · simp only [Start.origin, stop, Bool.false_eq_true, if_false, Option.some.injEq,
        Prod.mk.injEq] at o
      exact absurd o.1 (deployed_events_ne stop)
    · simp [Start.origin, stop] at o
  · simp only [Start.origin, Option.some.injEq, Prod.mk.injEq] at o
    obtain ⟨-, rfl⟩ := o
    obtain ⟨ws, fs, -, -, eq⟩ := walk_go n (walk_quiet r n wk)
    have sem : ((spec F).lang.sem ⟨code, .boundary wb⟩ e r).events =
        (go code.entry F wire r e [] 0 wb r.horizon).pfx.events := rfl
    rw [sem] at pre
    by_cases le : n ≤ r.horizon
    · obtain ⟨j, hj⟩ : ∃ j, r.horizon = n + j := ⟨r.horizon - n, by omega⟩
      rw [hj, eq j] at pre
      simp only [Nat.zero_add] at pre
      cases j with
      | zero => exact nomatch List.prefix_nil.1 pre
      | succ j =>
        cases stop : (step code.entry F wire r e [] n w (.request q)).stops with
        | true =>
          rw [go_stops next stop] at pre
          exact nomatch List.prefix_nil.1 pre
        | false =>
          rw [go_step next stop] at pre
          have ext := go_extends (entry := code.entry) (F := F) (wire := wire) (r := r) (e := e) j
            ([] ++ (step code.entry F wire r e [] n w (.request q)).events) (n + 1)
            (step code.entry F wire r e [] n w (.request q)).world
          cases fl : r.fails n with
          | true =>
            cases prefix_head ext pre (request_fails funded installed resolved fl)
            exact .inr rfl
          | false =>
            cases o : outcomeOf (callOf w q k entry).2 with
            | none => exact nomatch stop.symm.trans (request_halts funded installed resolved fl o)
            | some out' =>
              cases prefix_head ext pre (request_done funded installed resolved fl o).1
              exact .inl rfl
    · have short := (go_mono (entry := code.entry) (F := F) (wire := wire) (r := r) (e := e)
        r.horizon n [] 0 wb (by omega)).1.1
      have z := eq 0
      rw [Nat.add_zero] at z
      rw [z] at short
      exact nomatch List.prefix_nil.1 (pre.trans short)

end Request

/-! ## The deployment -/

section Deploy

variable {F : Fixed} {e : SessionEnv} {r : Bound} {code : Code}
  (hk : code.main < code.contracts.length) {body : Prog (code.catalog ⟨code.main, hk⟩) [] []}

/-- The creation frame of the main contract's resolved constructor, with no answers. -/
noncomputable abbrev createOf (F : Fixed) (e : SessionEnv) (code : Code)
    (hk : code.main < code.contracts.length) (body : Prog (code.catalog ⟨code.main, hk⟩) [] []) :=
  (initial code.roles e).transact fun v =>
    v.create ⟨code.main, hk⟩ (liftAddress (F.createAddress e.deployer e.deployNonce)) body
      (deployContext wire e)

/-- The creation returns: the deployment's event at its address, and its world. -/
theorem deploy_ok (resolved : code.ctor ⟨code.main, hk⟩ e.deployArgs = some body)
    (nofail : r.deployFails = false) {d : Handle (⟨code.main, hk⟩ : Fin code.contracts.length)} (eq : (createOf F e code hk body).2 = .ok d) :
    (deploy code.main code.roles code.ctor F wire r e).events =
      [Event.deploy e.deployer e.deployValue e.deployArgs (.success [])
        (some (F.createAddress e.deployer e.deployNonce))] ∧
    (deploy code.main code.roles code.ctor F wire r e).world = (createOf F e code hk body).1 ∧
    (deploy code.main code.roles code.ctor F wire r e).stops = false := by
  simp only [deploy, dif_pos hk, resolved, nofail, Bool.false_eq_true, if_false, eq, and_self]

/-- The creation fails observably: the deployment's revert with its data. -/
theorem deploy_error (resolved : code.ctor ⟨code.main, hk⟩ e.deployArgs = some body)
    (nofail : r.deployFails = false) {hlt : THalt}
    (eq : (createOf F e code hk body).2 = .error hlt) (caught : ContractWorld.catchable hlt = true) :
    (deploy code.main code.roles code.ctor F wire r e).events =
      [Event.deploy e.deployer e.deployValue e.deployArgs (.revert hlt.data) none] ∧
    (deploy code.main code.roles code.ctor F wire r e).stops = false := by
  simp only [deploy, dif_pos hk, resolved, nofail, Bool.false_eq_true, if_false, eq, caught,
    if_true, and_self]

/-- The creation exhausts or diverges: the session stops. -/
theorem deploy_halts (resolved : code.ctor ⟨code.main, hk⟩ e.deployArgs = some body)
    (nofail : r.deployFails = false) {hlt : THalt}
    (eq : (createOf F e code hk body).2 = .error hlt)
    (halts : ContractWorld.catchable hlt = false) :
    (deploy code.main code.roles code.ctor F wire r e).stops = true := by
  simp only [deploy, dif_pos hk, resolved, nofail, Bool.false_eq_true, if_false, eq, halts]

/-- The bound fails the creation: a revert with empty data and no address. -/
theorem deploy_fails (resolved : code.ctor ⟨code.main, hk⟩ e.deployArgs = some body)
    (fails : r.deployFails = true) :
    (deploy code.main code.roles code.ctor F wire r e).events =
      [Event.deploy e.deployer e.deployValue e.deployArgs (.revert []) none] ∧
    (deploy code.main code.roles code.ctor F wire r e).stops = false := by
  simp only [deploy, dif_pos hk, resolved, fails, if_true, and_self]

/-- **A fresh session at any bound** shows nothing when its deployment stops, and the
deployment's events first otherwise. -/
theorem fresh_events (r : Bound) (code : Code) :
    ((deploy code.main code.roles code.ctor F wire r e).stops = true →
      ((spec F).lang.sem (Start.initial code) e r).events = []) ∧
    ((deploy code.main code.roles code.ctor F wire r e).stops = false →
      (deploy code.main code.roles code.ctor F wire r e).events <+:
        ((spec F).lang.sem (Start.initial code) e r).events) := by
  have sem : (spec F).lang.sem (Start.initial code) e r =
      (run code.main code.roles code.ctor code.entry F wire .fresh e r).pfx := rfl
  rw [sem]
  exact ⟨fun stop => by rw [run_fresh_stops stop],
    fun completes => by rw [run_fresh completes]; exact go_extends _ _ _ _⟩

end Deploy

end Solidity.Semantics.IntrinsicSession
