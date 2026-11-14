import Solidity.Correctness.Sim.Steps
import Solidity.Roadmap.G49Final.PassCorrect

/-! Observation diagrams over the roadmap's unchanged prefix order.
Initial states and completed observations are explicit; silent steps alone
are not enough to establish observational refinement. -/
namespace Solidity.Correctness.Sim
open Solidity.Roadmap Solidity.Roadmap.G49Final

/-- A small-step presentation. Relating it to a language requires run coverage. -/
structure Machine where
  State : Type
  initial : State
  step : State → State → Prop
  observe : State → Prefix Event Outcome

def Machine.Reachable (M : Machine) (s : M.State) : Prop :=
  Star M.step M.initial s

/-- Events may extend until completion; a matched completed state must retain
both its final outcome and its entire event sequence. -/
structure Diagram (S T : Machine) where
  matchState : S.State → T.State → Prop
  initial : matchState S.initial T.initial
  step : ∀ s s' t, S.step s s' → matchState s t →
    ∃ t', Star T.step t t' ∧ matchState s' t'
  events : ∀ s t, matchState s t → (S.observe s).events <+: (T.observe t).events
  final : ∀ s t o, matchState s t → (S.observe s).final = some o →
    T.observe t = S.observe s

theorem Diagram.observations {S T : Machine} (D : Diagram S T)
    {s : S.State} {t : T.State} (related : D.matchState s t) :
    (S.observe s).Le (T.observe t) := by
  refine ⟨D.events s t related, ?_⟩
  cases h : (S.observe s).final with
  | none => exact .inl rfl
  | some o => exact .inr (D.final s t o related h)

theorem Diagram.run {S T : Machine} (D : Diagram S T)
    {s : S.State} (run : S.Reachable s) :
    ∃ t, T.Reachable t ∧ D.matchState s t ∧ (S.observe s).Le (T.observe t) := by
  obtain ⟨t, path, matched⟩ := star_simulation D.matchState D.step run D.initial
  exact ⟨t, path, matched, D.observations matched⟩

/-- Every prefix selected by the guard, including every completed run, has
an execution in the presentation. No source Forward premise is implicit. -/
def Covers (b : Behaviour) (M : b.Env → Machine)
    (selected : b.Env → b.Res → Prop) : Prop :=
  ∀ e r, b.Allowed e → selected e r →
    ∃ s, (M e).Reachable s ∧ (M e).observe s = b.observe e r

/-- The explicit completed-run consequence of coverage. This includes failure
outcomes whenever the supplied selection includes them. -/
theorem Covers.completed {b : Behaviour} {M : b.Env → Machine}
    {selected : b.Env → b.Res → Prop} (coverage : Covers b M selected)
    {e : b.Env} {r : b.Res} (allowed : b.Allowed e) (select : selected e r)
    {o : Outcome} (done : (b.observe e r).final = some o) :
    ∃ s, (M e).Reachable s ∧ (M e).observe s = b.observe e r ∧
      ((M e).observe s).final = some o := by
  obtain ⟨s, path, observes⟩ := coverage e r allowed select
  exact ⟨s, path, observes, by rw [observes]; exact done⟩

/-- Forward resource adequacy at a specified bound, for the states supplied
by the diagram. It preserves all three Ready components. -/
structure ForwardResources (a b : Behaviour) (S : a.Env → Machine)
    (T : b.Env → Machine) (envAbs : b.Env → a.Env)
    (D : ∀ e, Diagram (S (envAbs e)) (T e)) where
  need : b.Env → a.Res → b.Res
  coverage : Covers a S a.Ready
  ready : ∀ e r, b.Allowed e → a.Ready (envAbs e) r → b.Ready e (need e r)
  bound : ∀ e r s t, b.Allowed e → a.Ready (envAbs e) r →
    (S (envAbs e)).Reachable s → (S (envAbs e)).observe s = a.observe (envAbs e) r →
    (T e).Reachable t → (D e).matchState s t →
    ((T e).observe t).Le (b.observe e (need e r))

/-- Backward coverage uses a separately proved reverse diagram. Every target
admissible guarded prefix is covered, without requiring target Forward.
Realization of the reverse endpoint retains source admissibility and Guard. -/
structure BackwardResources (a b : Behaviour) (S : a.Env → Machine)
    (T : b.Env → Machine) (envAbs : b.Env → a.Env)
    (D : ∀ e, Diagram (T e) (S (envAbs e))) where
  coverage : Covers b T (fun e r => b.Admissible r ∧ b.Guard e r)
  bound : ∀ e r t s, b.Allowed e → b.Admissible r → b.Guard e r →
    (T e).Reachable t → (T e).observe t = b.observe e r →
    (S (envAbs e)).Reachable s → (D e).matchState t s →
    ∃ rs, a.Admissible rs ∧ a.Guard (envAbs e) rs ∧
      ((S (envAbs e)).observe s).Le (a.observe (envAbs e) rs)

/-- Sufficient assumptions for the frozen backward clause. Determinism is
neither a premise nor a substitute for coverage and resource realization. -/
theorem backward_of_simulation {a b : Behaviour} {S : a.Env → Machine}
    {T : b.Env → Machine} {envAbs : b.Env → a.Env}
    (D : ∀ e, Diagram (T e) (S (envAbs e))) (R : BackwardResources a b S T envAbs D)
    (e : b.Env) (r : b.Res) (allowed : b.Allowed e)
    (admissible : b.Admissible r) (guard : b.Guard e r) :
    ∃ rs, a.Admissible rs ∧ a.Guard (envAbs e) rs ∧
      (b.observe e r).Le (a.observe (envAbs e) rs) := by
  obtain ⟨t, path, observes⟩ := R.coverage e r allowed ⟨admissible, guard⟩
  obtain ⟨s, run, related, le⟩ := (D e).run path
  obtain ⟨rs, ha, hg, bound⟩ := R.bound e r t s allowed admissible guard path observes run related
  exact ⟨rs, ha, hg, observes ▸ le.trans bound⟩

/-- Construct both obligations, keeping the original environment and resource
contracts. This is a framework theorem, not a concrete compiler certificate. -/
def passCorrect_of_simulations {a b : Behaviour} {S : a.Env → Machine}
    {T : b.Env → Machine} (envAbs : b.Env → a.Env)
    (envSound : ∀ e, b.Allowed e → a.Allowed (envAbs e))
    (envOnto : ∀ e, a.Allowed e → ∃ e', b.Allowed e' ∧ envAbs e' = e)
    (forward : ∀ e, Diagram (S (envAbs e)) (T e))
    (reverse : ∀ e, Diagram (T e) (S (envAbs e)))
    (F : ForwardResources a b S T envAbs forward)
    (B : BackwardResources a b S T envAbs reverse) : PassCorrect a b where
  envAbs := envAbs
  envSound := envSound
  envOnto := envOnto
  need := F.need
  need_ok e r allowed ready := by
    obtain ⟨s, path, observes⟩ := F.coverage (envAbs e) r (envSound e allowed) ready
    obtain ⟨t, run, related, le⟩ := (forward e).run path
    have bound := F.bound e r s t allowed ready path observes run related
    exact ⟨F.ready e r allowed ready, observes ▸ le.trans bound⟩
  back := backward_of_simulation reverse B

end Solidity.Correctness.Sim
