import Solidity.Goals.GoalPinsSpec
/-! # `goalPinsCorrect` is false as stated

**Claim**: `goalPinsCorrect := ∃ ops, GoalPinSpecV2.Laws ops` asks for a pin checker that
refines the reference graphs exactly (goal "gp-goal-pins", still open).
**Culprit**: `Solidity/Goals/GoalPinsSpec.lean:387` (`Laws.check_exact`). `→` binds tighter
than `↔`, so the law reads `(ObservedSnapshot s → check … = out) ↔ CheckGraph … out`. For a
snapshot that no `readSnapshot` run returns the left side holds for every `out`, so
`CheckGraph` must relate it to every output, against `Laws.check_deterministic`.
**Witness**: `laws_force_observed` (any `Laws ops` makes every `Snapshot` observed), `not_observed`
(`⟨env, []⟩` never is: `GoalPinSpec.required` returns a nonempty list), so `¬ goalPinsCorrect`.
**Suggested fix**: parenthesize, `ObservedSnapshot snapshot → (ops.check … = output ↔ CheckGraph …)`.
Second witness, a documented boundary (`GoalPinsSpec.lean:96`): `folded_ignores_body`, the pin
graph of a folded (data or non-`Solidity`) definition never reads its body. -/
namespace Solidity.Examples.RedTeam.Statements.GoalPinsUnsat
open Lean Solidity.Goals GoalPinSpec GoalPinSpecV2

theorem laws_force_observed {ops : Operations} (h : Laws ops) (s : Snapshot) :
    ObservedSnapshot s := Classical.byContradiction fun hn => by
  have g := fun out => (h.check_exact s 0 ⟨"", []⟩ [] out).mp (fun o => absurd o hn)
  exact nomatch h.check_deterministic s _ _ 0 _ _ (g (.ok ())) (g (.error .resource))
/-- Some run of `x` returns `a`. -/
def Ret {α} (x : MetaM α) (a : α) : Prop := ∃ mc ms cc cs w w', x mc ms cc cs w = .ok a w'
theorem ok_bind {ε σ α β} (x : EStateM ε σ α) (f : α → EStateM ε σ β) (s b s') :
    EStateM.bind x f s = .ok b s' ↔ ∃ a s1, x s = .ok a s1 ∧ f a s1 = .ok b s' := by
  unfold EStateM.bind; cases x s with
  | ok a s1 => exact ⟨fun h => ⟨a, s1, rfl, h⟩, fun ⟨_, _, e, h⟩ => by cases e; exact h⟩
  | error => exact ⟨nofun, fun ⟨_, _, e, _⟩ => nomatch e⟩
theorem ok_map {ε σ α β} (x : EStateM ε σ α) (f : α → β) (s b s') :
    EStateM.map f x s = .ok b s' ↔ ∃ a, x s = .ok a s' ∧ f a = b := by
  unfold EStateM.map; cases x s with
  | ok a s1 => exact ⟨fun h => by cases h; exact ⟨a, rfl, rfl⟩, fun ⟨_, e, h⟩ => by cases e; cases h; rfl⟩
  | error => exact ⟨nofun, fun ⟨_, e, _⟩ => nomatch e⟩
theorem ret_bind {α β} (x : MetaM α) (f : α → MetaM β) (b) (h : Ret (x >>= f) b) :
    ∃ a, Ret x a ∧ Ret (f a) b := by
  obtain ⟨mc, ms, cc, cs, w, w', h⟩ := h
  simp only [bind, ReaderT.bind, ok_bind] at h
  obtain ⟨_, _, hx, h⟩ := h
  exact ⟨_, ⟨_, _, _, _, _, _, hx⟩, _, _, _, _, _, _, h⟩
theorem ret_finally {α} (y : MetaM α) (fin : MetaM Unit) (a) (h : Ret (tryFinally y fin) a) : Ret y a := by
  obtain ⟨mc, ms, cc, cs, w, w', h⟩ := h
  simp only [tryFinally, tryFinally', ok_map, Functor.map] at h
  obtain ⟨_, h, rfl⟩ := h
  split at h <;> split at h <;> cases h
  exact ⟨_, _, _, _, _, _, by assumption⟩
theorem ret_meta {α} (x : MetaM α) (mc ms cc cs w w' a)
    (h : x.run' mc ms cc cs w = .ok a w') : Ret x a := by
  simp only [Meta.MetaM.run', Meta.MetaM.run, StateRefT'.run, bind, ReaderT.bind, ok_bind, ok_map, Functor.map] at h
  obtain ⟨_, ⟨_, _, _, _, _, hx, _, _, _, hp⟩, rfl⟩ := h
  cases hp; exact ⟨_, _, _, _, _, _, hx⟩
open Elab Tactic in
/-- Unfold the private wrapper `Core.withConsistentCtx` in `h`. -/
elab "expose_run" : tactic => liftMetaTactic fun g => g.withContext do
  let some d := (← getLCtx).findFromUserName? `h | failure
  let t ← Meta.deltaExpand d.type (· == mkPrivateNameCore `Lean.CoreM `Lean.Core.withConsistentCtx)
  return [← g.replaceLocalDeclDefEq d.fvarId t]
theorem ret_core {α} (y : CoreM α) (cc cs w w' a post)
    (h : y.run cc cs w = .ok (a, post) w') : ∃ cc cs w w', y cc cs w = .ok a w' := by
  simp only [Core.CoreM.run, StateRefT'.run, bind, ok_bind] at h
  expose_run
  simp only [withReader, withTheReader, MonadWithReaderOf.withReader, withOptions, MonadWithOptions.withOptions, read, MonadReader.read, readThe, MonadReaderOf.read, ReaderT.read,
     bind, ReaderT.bind, ok_bind] at h
  obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, _, _, _, _, hi⟩, _, _, _, hp⟩ := h
  cases hp
  split at hi <;> simp only [bind, ReaderT.bind, ok_bind] at hi <;> obtain ⟨_, _, _, hi⟩ := hi <;> exact ⟨_, _, _, _, hi⟩
abbrev R := Except CoverageError (List Lean.Name)
theorem catch_ok (x : CoreM R) (hd : Exception → CoreM R) (cc cs w w') (ns : List Lean.Name)
    (hh : ∀ ex w w', hd ex cc cs w ≠ .ok (.ok ns) w')
    (h : Core.tryCatchRuntimeEx x hd cc cs w = .ok (.ok ns) w') : x cc cs w = .ok (.ok ns) w' := by
  unfold Core.tryCatchRuntimeEx at h
  simp only [tryCatch, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, bind] at h
  generalize x cc cs w = r at h ⊢
  cases r with
  | ok => exact h
  | error =>
    dsimp only at h; split at h
    · cases h
    · exact absurd h (hh _ _ _)
def Out (x : MetaM R) : Prop := ∀ ns, Ret x (.ok ns) → ns ≠ []
theorem out_err (e) : Out (pure (.error e)) := fun _ ⟨_, _, _, _, _, _, h⟩ => nomatch h
theorem out_bind {α} (x : MetaM α) (f : α → MetaM R) (hf : ∀ a, Out (f a)) : Out (x >>= f) :=
  fun ns h => let ⟨a, _, h⟩ := ret_bind _ _ _ h; hf a ns h
theorem required_nonempty : Out required := by
  intro ns ⟨mc, ms, cc, cs, w, w', h⟩
  unfold required at h
  refine out_bind _ _ (fun env => ?_) ns ⟨mc, ms, cc, cs, w, w', catch_ok _ _ _ _ _ _ _ (fun _ _ _ h => by cases h) h⟩
  dsimp only
  split
  · exact out_err _
  · refine out_bind _ _ fun _ => ?_
    repeat' split
    all_goals first | exact out_err _ | skip
    refine out_bind _ _ fun _ => out_bind _ _ fun rs => ?_
    intro ns ⟨_, _, _, _, _, _, h⟩
    cases h
    simp [List.eraseDups_cons]
theorem not_observed (env : Environment) : ¬ ObservedSnapshot ⟨env, []⟩ := by
  intro ⟨mc, ms, cc, cs, post, w, w', _, h⟩
  obtain ⟨_, _, _, _, h⟩ := ret_core _ _ _ _ _ _ _ h
  obtain ⟨_, _, h⟩ := ret_bind _ _ _ (ret_meta _ _ _ _ _ _ _ _ h)
  obtain ⟨r, hr, _, _, _, _, _, _, h⟩ := ret_bind _ _ _ h
  cases r <;> cases h
  obtain ⟨_, _, hr⟩ := ret_bind _ _ _ hr
  obtain ⟨_, _, hr⟩ := ret_bind _ _ _ (ret_finally _ _ _ hr)
  exact required_nonempty _ hr rfl
theorem goalPinsCorrect_false : ¬ goalPinsCorrect := fun ⟨_, h⟩ =>
  let ⟨env⟩ := (inferInstance : Nonempty Environment); not_observed env (laws_force_observed h _)

/--
info: 'Solidity.Examples.RedTeam.Statements.GoalPinsUnsat.goalPinsCorrect_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms goalPinsCorrect_false
theorem folded_ignores_body (t : Task) (d d' : DefinitionVal) (args : List Task)
    (h : d.toConstantVal = d'.toConstantVal) : folded t (.defnInfo d) args = folded t (.defnInfo d') args := by
  simp [folded, template, ConstantInfo.type, ConstantInfo.name, ConstantInfo.levelParams, ConstantInfo.toConstantVal, h]
/-- info: 'Solidity.Examples.RedTeam.Statements.GoalPinsUnsat.folded_ignores_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms folded_ignores_body
end Solidity.Examples.RedTeam.Statements.GoalPinsUnsat
