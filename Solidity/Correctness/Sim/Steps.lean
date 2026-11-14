/-! Finite transition closures and reusable simulation diagrams.
These lemmas do not assert resource adequacy or coverage of a language's runs.
Those obligations belong to the observation interface. -/
namespace Solidity.Correctness.Sim

/-- Zero or more transitions, retaining the endpoints. -/
inductive Star {S : Type} (step : S → S → Prop) : S → S → Prop where
  | refl (s) : Star step s s
  | tail {s t u} : Star step s t → step t u → Star step s u

/-- One or more transitions. -/
def Plus {S : Type} (step : S → S → Prop) (s u : S) : Prop :=
  ∃ t, step s t ∧ Star step t u

/-- At most one transition. -/
def OptionStep {S : Type} (step : S → S → Prop) (s t : S) : Prop :=
  s = t ∨ step s t

theorem Star.single {S : Type} {step : S → S → Prop} {s t : S}
    (h : step s t) : Star step s t := .tail (.refl s) h

theorem Star.trans {S : Type} {step : S → S → Prop} {s t u : S}
    (h : Star step s t) (k : Star step t u) : Star step s u := by
  induction k with
  | refl => exact h
  | tail _ edge ih => exact .tail ih edge

theorem Plus.star {S : Type} {step : S → S → Prop} {s t : S}
    (h : Plus step s t) : Star step s t := by
  obtain ⟨u, edge, rest⟩ := h
  exact (Star.single edge).trans rest

theorem OptionStep.star {S : Type} {step : S → S → Prop} {s t : S}
    (h : OptionStep step s t) : Star step s t := by
  rcases h with eq | edge
  · subst t; exact .refl s
  · exact .single edge

/-- A local diagram extends to every finite source path. -/
theorem star_simulation {S T : Type} {source : S → S → Prop}
    {target : T → T → Prop} (matchState : S → T → Prop)
    (diagram : ∀ s s' t, source s s' → matchState s t →
      ∃ t', Star target t t' ∧ matchState s' t')
    {s s' : S} (run : Star source s s') {t : T} (related : matchState s t) :
    ∃ t', Star target t t' ∧ matchState s' t' := by
  induction run with
  | refl => exact ⟨t, .refl t, related⟩
  | tail _ edge ih =>
    obtain ⟨u, path, matched⟩ := ih
    obtain ⟨v, next, final⟩ := diagram _ _ u edge matched
    exact ⟨v, path.trans next, final⟩

theorem lockStep_simulation {S T : Type} {source : S → S → Prop}
    {target : T → T → Prop} (matchState : S → T → Prop)
    (diagram : ∀ s s' t, source s s' → matchState s t →
      ∃ t', target t t' ∧ matchState s' t')
    {s s' : S} (run : Star source s s') {t : T} (related : matchState s t) :
    ∃ t', Star target t t' ∧ matchState s' t' :=
  star_simulation matchState (fun s s' t edge matched => by
    obtain ⟨t', next, final⟩ := diagram s s' t edge matched
    exact ⟨t', .single next, final⟩) run related

theorem plus_simulation {S T : Type} {source : S → S → Prop}
    {target : T → T → Prop} (matchState : S → T → Prop)
    (diagram : ∀ s s' t, source s s' → matchState s t →
      ∃ t', Plus target t t' ∧ matchState s' t')
    {s s' : S} (run : Star source s s') {t : T} (related : matchState s t) :
    ∃ t', Star target t t' ∧ matchState s' t' :=
  star_simulation matchState (fun s s' t edge matched => by
    obtain ⟨t', next, final⟩ := diagram s s' t edge matched
    exact ⟨t', next.star, final⟩) run related

theorem option_simulation {S T : Type} {source : S → S → Prop}
    {target : T → T → Prop} (matchState : S → T → Prop)
    (diagram : ∀ s s' t, source s s' → matchState s t →
      ∃ t', OptionStep target t t' ∧ matchState s' t')
    {s s' : S} (run : Star source s s') {t : T} (related : matchState s t) :
    ∃ t', Star target t t' ∧ matchState s' t' :=
  star_simulation matchState (fun s s' t edge matched => by
    obtain ⟨t', next, final⟩ := diagram s s' t edge matched
    exact ⟨t', next.star, final⟩) run related

/-- Existential progress for active related states. This does not assert
progress along every nondeterministic source execution. The decrease is on
the source states chosen while the target waits. -/
theorem wellFounded_progress {S T : Type} {source : S → S → Prop}
    {target : T → T → Prop} (matchState : S → T → Prop)
    (decreases : S → S → Prop) (wf : WellFounded decreases)
    (progress : ∀ s t, matchState s t →
      (∃ s' t', Star source s s' ∧ Plus target t t' ∧ matchState s' t') ∨
      (∃ s', source s s' ∧ decreases s' s ∧ matchState s' t)) :
    ∀ s t, matchState s t →
      ∃ s' t', Star source s s' ∧ Plus target t t' ∧ matchState s' t' := by
  intro s
  induction s using wf.induction with
  | h s ih =>
    intro t related
    rcases progress s t related with done | silent
    · exact done
    · obtain ⟨s', edge, smaller, matched⟩ := silent
      obtain ⟨u, v, path, next, final⟩ := ih s' smaller t matched
      exact ⟨u, v, (Star.single edge).trans path, next, final⟩

/-- A nonempty source path produces a nonempty target path. -/
theorem plus_simulation_nonempty {S T : Type} {source : S → S → Prop}
    {target : T → T → Prop} (matchState : S → T → Prop)
    (diagram : ∀ s s' t, source s s' → matchState s t →
      ∃ t', Plus target t t' ∧ matchState s' t')
    {s s' : S} (run : Plus source s s') {t : T} (related : matchState s t) :
    ∃ t', Plus target t t' ∧ matchState s' t' := by
  obtain ⟨u, edge, rest⟩ := run
  obtain ⟨v, first, matched⟩ := diagram s u t edge related
  obtain ⟨w, path, final⟩ := plus_simulation matchState diagram rest matched
  obtain ⟨v', next, suffix⟩ := first
  exact ⟨w, ⟨v', next, suffix.trans path⟩, final⟩

/-- Terminal-aware existential progress: finite silent source steps either
reach matching final states or allow a positive target path. -/
theorem wellFounded_final_or_progress {S T : Type} {source : S → S → Prop}
    {target : T → T → Prop} (matchState : S → T → Prop)
    (sourceFinal : S → Prop) (targetFinal : T → Prop)
    (decreases : S → S → Prop) (wf : WellFounded decreases)
    (progress : ∀ s t, matchState s t →
      (sourceFinal s ∧ targetFinal t) ∨
      (∃ s' t', Star source s s' ∧ Plus target t t' ∧ matchState s' t') ∨
      (∃ s', source s s' ∧ decreases s' s ∧ matchState s' t)) :
    ∀ s t, matchState s t → ∃ s', Star source s s' ∧
      ((matchState s' t ∧ sourceFinal s' ∧ targetFinal t) ∨
       ∃ t', Plus target t t' ∧ matchState s' t') := by
  intro s
  induction s using wf.induction with
  | h s ih =>
    intro t related
    rcases progress s t related with final | advance | silent
    · exact ⟨s, .refl s, .inl ⟨related, final⟩⟩
    · obtain ⟨s', t', path, next, matched⟩ := advance
      exact ⟨s', path, .inr ⟨t', next, matched⟩⟩
    · obtain ⟨s', edge, smaller, matched⟩ := silent
      obtain ⟨u, path, result⟩ := ih s' smaller t matched
      exact ⟨u, (Star.single edge).trans path, result⟩

end Solidity.Correctness.Sim
