import Solidity.Correctness.IntrinsicSession.Laws.Frames.Steps

/-!
# The intrinsic session laws: the determined frames

The fields `transacts`, `resumes` and `deploys` of `Solidity.Goals.IntrinsicSession.Laws` at
`spec F` and `view F` (step `is0p-session-laws`, lane frames), from the boundary lemmas of
`Laws/Common.lean` and the unfolded steps of `Frames/Steps.lean`. The response table of `spec`
is empty, so the frame of a law at `ext := []` is the step's own frame; the premises on
`callsBack`, on the response tables and on the sender's funds are not used.
-/

namespace Solidity.Semantics.IntrinsicSession

open Solidity.Roadmap
open Solidity.Goals.IntrinsicSession (Code Good Observed Ends Matches RevertMatches IsTx)
open Solidity.ContractWorld (World Handle)
open Solidity.Lowering.V08.EnvironmentProjection (liftWord liftAddress requestContext)

/-- **A transaction that never leaves its contract is the actual frame.** -/
theorem Laws.transacts (F : Fixed) : ∀ x en h n (code : Code)
      (cw : ContractWorld.World code.catalog)
      (q : Request) (k : Fin code.contracts.length) (st : Storage (code.catalog k))
      (entry : ContractWorld.Entry (code.catalog k) Bytes),
    (spec F).lang.Allowed en → (view F).Boundary x en h n ⟨code, cw⟩ →
    ((spec F).session en).requests h n = some (.request q) →
    Solidity.Goals.IntrinsicSession.Funded F ((spec F).session en) h q →
    cw.accounts (liftAddress q.target) = some ⟨k, st⟩ → code.entry k q.input = some entry →
    Prog.callsBack true entry.body = false →
    (liftWord q.value).1 ≤ (cw.funds (liftAddress q.sender)).1 →
    let p := (spec F).ofWorld x
    let frame := fun ext => (cw.atTime (liftWord q.timestamp)).transact fun w =>
      w.call (⟨liftAddress q.target⟩ : ContractWorld.Handle k) entry (requestContext q ext)
    let res := frame []
    (∀ ext, frame ext = res) →
    (Ends res.2 → ∃ out, Observed (spec F) p en
      (h ++ [Event.tx q.sender q.target q.value q.timestamp q.input out])) ∧
    (∀ r, Good (spec F) r → h <+: ((spec F).lang.sem p en r).events →
      ((spec F).lang.sem p en r).events = h ∨ ∃ out,
        let done := Event.tx q.sender q.target q.value q.timestamp q.input out
        h ++ [done] <+: ((spec F).lang.sem p en r).events ∧ Matches res.2 out ∧
        ∃ ω ∈ (spec F).worlds p en r, ((view F).typed ω).Shows code res.1 ∧
          (view F).Boundary x en (h ++ [done]) (n + 1) ((view F).typed ω)) ∧
    ∀ r, (spec F).lang.Admissible r → h = [] → ∀ out,
      [Event.tx q.sender q.target q.value q.timestamp q.input out] <+:
        ((spec F).lang.sem p en r).events →
      Matches res.2 out ∨ out = .revert [] := by
  intro x en h n code cw q k st entry _ b next funded installed resolved _ _
  obtain ⟨w, eq, -⟩ := id b
  cases eq
  intro p frame res _
  have below {r} (good : Good (spec F) r) (pre : h <+: ((spec F).lang.sem x en r).events)
      (ge : ¬ n < r.horizon) : ((spec F).lang.sem x en r).events = h :=
    have short := Boundary.below b good (by omega)
    short.eq_of_length (Nat.le_antisymm short.length_le pre.length_le)
  have first : ∀ r, (spec F).lang.Admissible r → h = [] → ∀ out,
      [Event.tx q.sender q.target q.value q.timestamp q.input out] <+:
        ((spec F).lang.sem x en r).events → Matches res.2 out ∨ out = .revert [] := by
    rintro r - rfl out pre
    exact (first_tx b next funded installed resolved r pre).imp_left matches_of
  cases o : outcomeOf res.2 with
  | none =>
    have stops : (act F x en h n w (.request q)).stops = true :=
      request_halts (e := en) (r := Bound.upto 0) (n := n) funded installed resolved rfl o
    refine ⟨fun ends => ?_, fun r good pre => .inl ?_, first⟩
    · obtain ⟨out, eq⟩ := ends_of ends
      exact nomatch o.symm.trans eq
    · by_cases lt : n < r.horizon
      · exact Boundary.stops b next stops good (Nat.le_of_lt lt)
      · exact below good pre lt
  | some out =>
    obtain ⟨evs, wd, completes⟩ := request_done (e := en) (r := Bound.upto 0) (n := n) funded installed resolved rfl o
    have nb := Boundary.next b next completes
    have shown := fun {r} => Boundary.next_events (r := r) b next completes
    dsimp only [act] at nb shown
    rw [evs] at nb shown
    rw [wd] at nb
    refine ⟨fun _ => ⟨out, Boundary.observed nb⟩, fun r good pre => ?_, first⟩
    by_cases lt : n < r.horizon
    · obtain ⟨ω, mem, ty⟩ := Boundary.listed nb good lt
      exact .inr ⟨out, shown good lt, matches_of o, ω, mem, ty ▸ ⟨_, rfl, rfl, rfl, rfl⟩, ty ▸ nb⟩
    · exact .inl (below good pre lt)

/-- **Every completed transaction of an affordable request is that request's.** -/
theorem Laws.resumes (F : Fixed) : ∀ x en h n t (q : Request), (spec F).lang.Allowed en →
    (view F).Boundary x en h n t →
    ((spec F).session en).requests h n = some (.request q) →
    Solidity.Goals.IntrinsicSession.Funded F ((spec F).session en) h q →
    let p := (spec F).ofWorld x
    ∀ r, Good (spec F) r → ∀ (seg : List Event) (ev : Event), IsTx ev →
      (∀ y ∈ seg, ¬ IsTx y) → h ++ seg ++ [ev] <+: ((spec F).lang.sem p en r).events →
      (∃ out, ev = Event.tx q.sender q.target q.value q.timestamp q.input out) ∧
      ∃ ω ∈ (spec F).worlds p en r,
        (view F).Boundary x en (h ++ seg ++ [ev]) (n + 1) ((view F).typed ω) := by
  intro x en h n t q _ b next funded p r good seg ev _ quiet pre
  have pre : h ++ seg ++ [ev] <+: ((spec F).lang.sem x en r).events := pre
  obtain ⟨w, rfl, st⟩ := b
  have b : (view F).Boundary x en h n ⟨x.code, w⟩ := ⟨w, rfl, st⟩
  have long : h.length < ((spec F).lang.sem x en r).events.length := by
    have := pre.length_le
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    omega
  have lt : n < r.horizon := Nat.lt_of_not_le fun le => by
    have := (Boundary.below b good le).length_le
    omega
  cases stop : (act F x en h n w (.request q)).stops with
  | true =>
    rw [Boundary.stops b next stop good (Nat.le_of_lt lt)] at long
    exact absurd long (Nat.lt_irrefl _)
  | false =>
    obtain ⟨out, evs⟩ := request_events (e := en) funded stop
    have shown := Boundary.next_events b next stop good lt
    have nb := Boundary.next b next stop
    rw [evs] at shown nb
    obtain ⟨u, hu⟩ := shown
    obtain ⟨v, hv⟩ := pre
    have same := hu.trans hv.symm
    simp only [List.append_assoc, List.append_cancel_left_eq, List.cons_append,
      List.nil_append] at same
    cases seg with
    | nil =>
      cases (List.cons.inj same).1
      obtain ⟨ω, mem, ty⟩ := Boundary.listed nb good lt
      rw [List.append_nil]
      exact ⟨⟨out, rfl⟩, ω, mem, ty ▸ nb⟩
    | cons y seg =>
      cases (List.cons.inj same).1
      exact absurd trivial (quiet _ List.mem_cons_self)

/-- **A deployment that never leaves its contract is the actual creation.** -/
theorem Laws.deploys (F : Fixed) : ∀ (code : Code) (en : (spec F).lang.Env)
      (k : Fin code.contracts.length) (body : Prog (code.catalog k) [] []),
    (spec F).lang.Allowed en → k.val = code.main →
    code.ctor k ((spec F).session en).deployArgs = some body → Prog.callsBack true body = false →
    let e := (spec F).session en
    let p := (spec F).ofWorld ((view F).initial code)
    let this := F.createAddress e.deployer e.deployNonce
    e.deployValue.val ≤ (e.balance e.deployer).val → this ≠ e.deployer →
    let frame := fun ext =>
      (ContractWorld.World.empty code.catalog
          (Solidity.Goals.IntrinsicSession.funds e.balance) code.roles).transact fun w =>
        w.create k (liftAddress this) body
          { sender := liftAddress e.deployer, mode := .ordinary (liftWord e.deployValue),
            ext := ext }
    let res := frame []
    (∀ ext, frame ext = res) →
    (Ends res.2 → ∃ out address, Observed (spec F) p en
      [Event.deploy e.deployer e.deployValue e.deployArgs out address]) ∧
    (∀ r, Good (spec F) r → ((spec F).lang.sem p en r).events ≠ [] → ∃ out address,
      let done := Event.deploy e.deployer e.deployValue e.deployArgs out address
      [done] <+: ((spec F).lang.sem p en r).events ∧
      match res.2 with
      | .ok _ => (∃ d, out = .success d) ∧ address = some this ∧
        ∃ t', t'.Shows code res.1 ∧ (view F).Boundary ((view F).initial code) en [done] 0 t'
      | .error h => RevertMatches h out ∧ address = none) ∧
    ∀ r, (spec F).lang.Admissible r → ∀ out address,
      [Event.deploy e.deployer e.deployValue e.deployArgs out address] <+:
        ((spec F).lang.sem p en r).events →
      (out = .revert [] ∧ address = none) ∨
      match res.2 with
      | .ok _ => (∃ d, out = .success d) ∧ address = some this
      | .error h => RevertMatches h out ∧ address = none := by
  intro code en k body _ main resolved _
  obtain ⟨kv, hk⟩ := k
  cases main
  intro e p this _ _ frame res _
  have shows := fun r => fresh_events (F := F) (e := en) r code
  -- A bound that fails the creation shows a revert with empty data and no address.
  have failing : ∀ (r : Bound) out address, r.deployFails = true →
      [Event.deploy e.deployer e.deployValue e.deployArgs out address] <+:
        ((spec F).lang.sem p en r).events → out = .revert [] ∧ address = none := by
    intro r out address fl pre
    obtain ⟨evs, completes⟩ := deploy_fails (F := F) (e := en) (r := r) hk resolved fl
    cases prefix_head ((shows r).2 completes) pre evs
    exact ⟨rfl, rfl⟩
  cases hres : res.2 with
  | ok d =>
    have ok := fun (r : Bound) (nf : r.deployFails = false) =>
      deploy_ok (F := F) (e := en) (r := r) hk resolved nf hres
    obtain ⟨evs, wd, completes⟩ := ok (Bound.upto 0) rfl
    have b0 := deploy_boundary (F := F) (e := en) (code := code) completes
    dsimp only [deployed] at b0
    rw [evs, wd] at b0
    refine ⟨fun _ => ⟨_, _, Boundary.observed b0⟩, fun r good _ => ⟨_, _,
      (Boundary.reached b0 good (Nat.zero_le _)).2, ⟨_, rfl⟩, rfl, _, ⟨_, rfl, rfl, rfl, rfl⟩, b0⟩,
      fun r _ out address pre => ?_⟩
    cases fl : r.deployFails with
    | true => exact .inl (failing r out address fl pre)
    | false =>
      obtain ⟨evs, -, completes⟩ := ok r fl
      cases prefix_head ((shows r).2 completes) pre evs
      exact .inr ⟨⟨_, rfl⟩, rfl⟩
  | error hlt =>
    cases c : ContractWorld.catchable hlt with
    | true =>
      have err := fun (r : Bound) (nf : r.deployFails = false) =>
        deploy_error (F := F) (e := en) (r := r) hk resolved nf hres c
      obtain ⟨evs, completes⟩ := err (Bound.upto 0) rfl
      have b0 := deploy_boundary (F := F) (e := en) (code := code) completes
      dsimp only [deployed] at b0
      rw [evs] at b0
      refine ⟨fun _ => ⟨_, _, Boundary.observed b0⟩, fun r good _ => ⟨_, _,
        (Boundary.reached b0 good (Nat.zero_le _)).2, ⟨c, _, rfl, fun _ => rfl⟩, rfl⟩,
        fun r _ out address pre => ?_⟩
      cases fl : r.deployFails with
      | true => exact .inl (failing r out address fl pre)
      | false =>
        obtain ⟨evs, completes⟩ := err r fl
        cases prefix_head ((shows r).2 completes) pre evs
        exact .inr ⟨⟨c, _, rfl, fun _ => rfl⟩, rfl⟩
    | false =>
      have halts := fun (r : Bound) (nf : r.deployFails = false) =>
        deploy_halts (F := F) (e := en) (r := r) hk resolved nf hres c
      refine ⟨fun ends => (nomatch c.symm.trans ends), fun r good ne =>
        absurd (deploy_stops (halts (Bound.upto 0) rfl) good).1 ne, fun r _ out address pre => ?_⟩
      cases fl : r.deployFails with
      | true => exact .inl (failing r out address fl pre)
      | false =>
        have short : [Event.deploy e.deployer e.deployValue e.deployArgs out address] <+: [] :=
          (shows r).1 (halts r fl) ▸ pre
        exact nomatch List.prefix_nil.1 short

end Solidity.Semantics.IntrinsicSession
