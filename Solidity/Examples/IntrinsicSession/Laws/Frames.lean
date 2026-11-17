import Solidity.Correctness.IntrinsicSession.Laws.Frames
import Solidity.Examples.IntrinsicSession.Spec

/-! The determined-frame laws (`transacts`, `resumes`, `deploys`) on the one-contract session of
`Spec.lean`: resumed at `w` for the request, fresh for the deployment of its code. -/
namespace Solidity.Examples.IntrinsicSession.Laws.Frames

open Solidity.Roadmap Solidity.Semantics.IntrinsicSession Solidity.Examples.IntrinsicSession.Spec
open Solidity.Goals.IntrinsicSession (Code Good IsTx)
open Solidity.ContractWorld (World Handle)
open Solidity.Lowering.V08.EnvironmentProjection (liftWord liftAddress requestContext)

variable {C : Contract} {code : Code} {w : World code.catalog} {F : Fixed} {r : Bound}
  {e : SessionEnv} (s : OneRequest C code w F r e)

/-- The three theorems are exactly the fields of the laws at `spec F`, `view F`. -/
example (L : Solidity.Goals.IntrinsicSession.Laws F (spec F) (view F)) :
    L.transacts = Laws.transacts F ∧ L.resumes = Laws.resumes F ∧ L.deploys = Laws.deploys F :=
  ⟨rfl, rfl, rfl⟩

/-- The request's frame under the response table `ext`. -/
noncomputable abbrev called (s : OneRequest C code w F r e)
    (ext : List (Semantics.ExtKey × Semantics.ExtResult)) : World code.catalog × TRes Bytes :=
  (w.atTime (liftWord s.q.timestamp)).transact fun v =>
    v.call (⟨liftAddress s.q.target⟩ : Handle s.k) s.en (requestContext s.q ext)

/-- **`transacts`**: when the request's frame returns `d`, a good bound shows nothing or the
transaction with `success d` first, and every bound that shows the transaction first shows
`success d` or a revert with empty data. -/
example (allowed : (spec F).lang.Allowed e) (inside : Prog.callsBack true s.en.body = false)
    (covered : (liftWord s.q.value).1 ≤ (w.funds (liftAddress s.q.sender)).1)
    (table : ∀ ext, called s ext = called s []) (d : Bytes) (returns : (called s []).2 = .ok d)
    (good : Good (spec F) r) :
    (((spec F).lang.sem s.start e r).events = [] ∨
      [Event.tx s.q.sender s.q.target s.q.value s.q.timestamp s.q.input (.success d)] <+:
        ((spec F).lang.sem s.start e r).events) ∧
    ∀ r' out, [Event.tx s.q.sender s.q.target s.q.value s.q.timestamp s.q.input out] <+:
        ((spec F).lang.sem s.start e r').events → out = .success d ∨ out = .revert [] := by
  obtain ⟨_, shown, first⟩ := Laws.transacts F s.start e [] 0 code w s.q s.k s.st s.en allowed
    (Boundary.resume F ⟨code, w⟩ e) s.next s.funded s.installed s.resolved inside covered table
  refine ⟨?_, fun r' out pre => ?_⟩
  · rcases shown r good List.nil_prefix with idle | ⟨out, pre, m, -⟩
    · exact .inl idle
    · rw [returns] at m
      cases m
      exact .inr pre
  · have m := first r' trivial rfl out pre
    rw [returns] at m
    exact m

/-- **`resumes`**: the first transaction a good bound shows is the request's. -/
example (allowed : (spec F).lang.Allowed e) (good : Good (spec F) r) {ev : Event} (isTx : IsTx ev)
    (pre : [ev] <+: ((spec F).lang.sem s.start e r).events) :
    ∃ out, ev = Event.tx s.q.sender s.q.target s.q.value s.q.timestamp s.q.input out :=
  (Laws.resumes F s.start e [] 0 _ s.q allowed (Boundary.resume F ⟨code, w⟩ e) s.next s.funded
    r good [] ev isTx (fun _ m => nomatch m) pre).1

/-- The creation of the session's code by its resolved constructor `body`, under `ext`. -/
noncomputable abbrev created (_ : OneRequest C code w F r e) (k : Fin code.contracts.length)
    (body : Prog (code.catalog k) [] []) (ext : List (Semantics.ExtKey × Semantics.ExtResult)) :
    World code.catalog × TRes (Handle k) :=
  (World.empty code.catalog (Solidity.Goals.IntrinsicSession.funds e.balance) code.roles).transact
    fun v => v.create k (liftAddress (F.createAddress e.deployer e.deployNonce)) body
      { sender := liftAddress e.deployer, mode := .ordinary (liftWord e.deployValue), ext := ext }

/-- **`deploys`**: when the creation of the session's code returns, a good bound that shows
anything of the fresh session shows the successful deployment at the created address first,
and every bound that shows a deployment first shows that one or a revert with empty data. -/
example (allowed : (spec F).lang.Allowed e) (k : Fin code.contracts.length)
    (body : Prog (code.catalog k) [] []) (main : k.val = code.main)
    (resolved : code.ctor k e.deployArgs = some body) (inside : Prog.callsBack true body = false)
    (covered : e.deployValue.val ≤ (e.balance e.deployer).val)
    (apart : F.createAddress e.deployer e.deployNonce ≠ e.deployer)
    (table : ∀ ext, created s k body ext = created s k body []) (v : Handle k)
    (returns : (created s k body []).2 = .ok v) (good : Good (spec F) r)
    (some : ((spec F).lang.sem (Start.initial code) e r).events ≠ []) :
    (∃ d, [Event.deploy e.deployer e.deployValue e.deployArgs (.success d)
        (.some (F.createAddress e.deployer e.deployNonce))] <+:
      ((spec F).lang.sem (Start.initial code) e r).events) ∧
    ∀ r' out address, [Event.deploy e.deployer e.deployValue e.deployArgs out address] <+:
        ((spec F).lang.sem (Start.initial code) e r').events →
      (out = .revert [] ∧ address = none) ∨
        ((∃ d, out = .success d) ∧ address = .some (F.createAddress e.deployer e.deployNonce)) := by
  obtain ⟨_, shown, first⟩ := Laws.deploys F code e k body allowed main resolved inside covered
    apart table
  refine ⟨?_, fun r' out address pre => ?_⟩
  · obtain ⟨out, address, pre, m⟩ := shown r good some
    erw [returns] at m
    obtain ⟨⟨d, rfl⟩, rfl, -⟩ := m
    exact ⟨d, pre⟩
  · have m := first r' trivial out address pre
    erw [returns] at m
    exact m

end Solidity.Examples.IntrinsicSession.Laws.Frames
