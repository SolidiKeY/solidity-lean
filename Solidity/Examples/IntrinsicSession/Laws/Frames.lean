import Solidity.Correctness.IntrinsicSession.Laws.Frames
import Solidity.Examples.IntrinsicSession.Spec

/-! The determined-frame laws `transacts` and `resumes` on the one-contract session of
`Spec.lean`, resumed at `w`. -/
namespace Solidity.Examples.IntrinsicSession.Laws.Frames

open Solidity.Roadmap Solidity.Semantics.IntrinsicSession Solidity.Examples.IntrinsicSession.Spec
open Solidity.Goals.IntrinsicSession (Code Good IsTx)
open Solidity.ContractWorld (World Handle)
open Solidity.Lowering.V08.EnvironmentProjection (liftWord liftAddress requestContext)

variable {C : Contract} {code : Code} {w : World code.catalog} {F : Fixed} {r : Bound}
  {e : SessionEnv} (s : OneRequest C code w F r e)

/-- The theorems are exactly the fields of the laws at `spec F`, `view F`. -/
example (L : Solidity.Goals.IntrinsicSession.Laws F (spec F) (view F)) :
    L.transacts = Laws.transacts F ∧ L.resumes = Laws.resumes F :=
  ⟨rfl, rfl⟩

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

end Solidity.Examples.IntrinsicSession.Laws.Frames
