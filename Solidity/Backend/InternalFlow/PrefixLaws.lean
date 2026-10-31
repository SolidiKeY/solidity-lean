import Solidity.Semantics.Run
import Solidity.Roadmap.Contracts

/-! Independent prefix algebra over the published loop and observation types.
No call evaluator, new loop semantics or termination cutoff is defined here. -/
namespace Solidity.Backend.InternalFlow

/-- Split any finite number of actual loop steps at an arbitrary horizon. -/
theorem loop_prefix_add {α : Type} (body : α → TRes α) (condition : α → TRes Bool)
    (n m : Nat) (initial : α) :
    TLoop.iterN body condition (n + m) initial =
      match TLoop.iterN body condition n initial with
      | .inl intermediate => TLoop.iterN body condition m intermediate
      | .inr result => .inr result := by
  induction n generalizing initial with
  | zero => rw [Nat.zero_add]; rfl
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [TLoop.iterN]
    cases h : TLoop.step body condition initial with
    | inl intermediate => exact ih intermediate
    | inr result => rfl

/-- Finite prefixes concatenate even when a body changes its state type's
heap/storage content; no invariance of those fields is assumed. -/
theorem loop_prefix_continue {α : Type} (body : α → TRes α) (condition : α → TRes Bool)
    (n m : Nat) (initial intermediate : α)
    (h : TLoop.iterN body condition n initial = .inl intermediate) :
    TLoop.iterN body condition (n + m) initial = TLoop.iterN body condition m intermediate := by
  rw [loop_prefix_add, h]

/-- A finite successful observed prefix determines the observation of the
actual unbounded loop run. The premise is checked on iterN, not on run. -/
theorem loop_observed_of_prefix {α β : Type} (body : α → TRes α)
    (condition : α → TRes Bool) (initial : α) (observe : α → β) (n : Nat) (value : β)
    (hprefix : (TLoop.iterN body condition n initial).map observe (Except.map observe) =
      .inr (.ok value)) :
    (TLoop.run body condition initial).map observe = .ok value := by
  cases hi : TLoop.iterN body condition n initial with
  | inl next => rw [hi] at hprefix; cases hprefix
  | inr result =>
    rw [TLoop.run_of_iterN hi]
    rw [hi] at hprefix
    exact Sum.inr.inj hprefix

/-- Prefixes that remain running at every horizon have the existing divergence
outcome. This is not a recursive-call correspondence theorem. -/
theorem loop_all_prefixes_running {α : Type} (body : α → TRes α)
    (condition : α → TRes Bool) (initial : α)
    (running : ∀ n, ∃ next, TLoop.iterN body condition n initial = .inl next) :
    TLoop.run body condition initial = .error .diverge := by
  have hn : ¬ ∃ r n, TLoop.iterN body condition n initial = .inr r := by
    rintro ⟨r, n, h⟩
    obtain ⟨next, hp⟩ := running n
    rw [hp] at h
    cases h
  simp only [TLoop.run, hn, dite_false]

/-- Prepend already observed caller events to a callee prefix. This is only
an observation adapter; it neither runs a callee nor validates a compiler. -/
def prefixContext {E O : Type} (events : List E) (p : Roadmap.Prefix E O) :
    Roadmap.Prefix E O := ⟨events ++ p.events, p.final⟩

theorem prefix_context_assoc {E O : Type} (a b : List E) (p : Roadmap.Prefix E O) :
    prefixContext a (prefixContext b p) = prefixContext (a ++ b) p := by
  simp only [prefixContext, List.append_assoc]

theorem prefix_context_le {E O : Type} (events : List E)
    {a b : Roadmap.Prefix E O} (h : a.Le b) :
    (prefixContext events a).Le (prefixContext events b) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨suffix, hs⟩ := h.1
    exact ⟨suffix, by simp only [prefixContext, List.append_assoc, hs]⟩
  · rcases h.2 with unfinished | finished
    · exact .inl unfinished
    · exact .inr (congrArg (prefixContext events) finished)

/-- Adding a fixed caller history preserves consistency of an existing family. -/
theorem prefix_context_consistent {R E O : Type} [LE R] (events : List E)
    (p : Roadmap.Prefixes R E O) (h : Roadmap.Prefixes.Consistent p) :
    Roadmap.Prefixes.Consistent (fun r => prefixContext events (p r)) :=
  fun r s hrs => prefix_context_le events (h r s hrs)

/-- Completion is exactly unchanged by caller-history transport. -/
theorem prefix_context_completes {R E O : Type} (events : List E)
    (p : Roadmap.Prefixes R E O) (o : O) :
    Roadmap.Prefixes.Completes (fun r => prefixContext events (p r)) o ↔
      Roadmap.Prefixes.Completes p o := Iff.rfl

/-- Divergence is exactly unchanged by caller-history transport. -/
theorem prefix_context_diverges {R E O : Type} (events : List E)
    (p : Roadmap.Prefixes R E O) (allowed : R → Prop) :
    Roadmap.Prefixes.Diverges allowed (fun r => prefixContext events (p r)) ↔
      Roadmap.Prefixes.Diverges allowed p := Iff.rfl

end Solidity.Backend.InternalFlow
