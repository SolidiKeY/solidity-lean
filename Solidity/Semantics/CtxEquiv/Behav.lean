import Solidity.Roadmap.Contracts

/-!
# Observable behaviours and their simulation order (S1.1)

The observation of one execution is G01's `Prefix E O`
(`Solidity/Roadmap/Contracts.lean`): the events so far and, if it completed,
the final observation.  A **behaviour** is a set of such prefixes: what one
deployed program can show one adversary, across every resource choice the
semantics allows (horizons, failure points, gas schedules).  Different
resource choices are the nondeterminism of a side.

`Behav.Below X Y` reads "everything `X` shows, `Y` can show at least as
far": each prefix of `X` is a prefix of one of `Y`'s.  A completed prefix is
below only itself (`Prefix.Le.final_eq`), so completed observations of `X`
are completed observations of `Y` (`Below.completes`), and any property of
prefixes closed under taking prefixes transfers from `Y` to `X`
(`Below.safety`).  `Below` is a preorder; G01's two-sided `Refines` is
`Below` in both directions (`Solidity/Semantics/CtxEquiv/Unify.lean`).

**Sequencing.**  `Behav.seq X K` runs `X` and, when it completes with
events `h` and outcome `o`, continues with `K h o` (the continuation reads
the whole history, as the G50 adversary does), the events concatenated; a
completed `X` prefix is also shown as the boundary prefix with no
continuation events yet.  `Below` is a congruence for it (`Below.seq`).
This is sequencing of *behaviours* (a bind on prefix sets): G01's `Lang`
has no composition operator on programs, and the transactions after a
deployment are already the adversary's (`SessionEnv.requests`), so the
congruence is stated for whatever continuation a context runs after a
completed part.

The definitions are generic in the event and observation types.  G01's
`Event` has no log constructor (logs are an excluded observation, G00), so
logs are **not** observed today; when X07 adds them to `Event`, these
definitions observe them unchanged.
-/

namespace Solidity.CtxEquiv

open Solidity.Roadmap (Prefix Prefixes)

/-- A behaviour: the prefixes one program can show one adversary. -/
abbrev Behav (E O : Type) := Prefix E O → Prop

variable {E O : Type}

/-- `X` is simulated by `Y`: every prefix `X` shows is a prefix of one `Y`
shows. -/
def Behav.Below (X Y : Behav E O) : Prop :=
  ∀ a, X a → ∃ b, Y b ∧ a.Le b

theorem Behav.Below.refl (X : Behav E O) : X.Below X :=
  fun a ha => ⟨a, ha, Prefix.Le.refl a⟩

theorem Behav.Below.trans {X Y Z : Behav E O} (h₁ : X.Below Y) (h₂ : Y.Below Z) :
    X.Below Z := by
  intro a ha
  obtain ⟨b, hb, hab⟩ := h₁ a ha
  obtain ⟨c, hc, hbc⟩ := h₂ b hb
  exact ⟨c, hc, hab.trans hbc⟩

/-- A smaller behaviour is below. -/
theorem Behav.Below.of_sub {X Y : Behav E O} (h : ∀ a, X a → Y a) : X.Below Y :=
  fun a ha => ⟨a, h a ha, Prefix.Le.refl a⟩

/-- **Completions transfer**: a completed prefix of `X` is a prefix `Y`
shows, with the same events and final observation. -/
theorem Behav.Below.completes {X Y : Behav E O} (h : X.Below Y) {a : Prefix E O} (ha : X a)
    {o : O} (ho : a.final = some o) : Y a := by
  obtain ⟨b, hb, hab⟩ := h a ha
  have heq : b = a := hab.final_eq ho
  exact heq ▸ hb

/-- **Safety transfers**: a property closed under taking prefixes that holds
of everything `Y` shows holds of everything `X` shows. -/
theorem Behav.Below.safety {X Y : Behav E O} (h : X.Below Y) (Φ : Prefix E O → Prop)
    (down : ∀ a b, a.Le b → Φ b → Φ a) (hY : ∀ b, Y b → Φ b) : ∀ a, X a → Φ a := by
  intro a ha
  obtain ⟨b, hb, hab⟩ := h a ha
  exact down a b hab (hY b hb)

/-- The completed observations of a behaviour, with their events. -/
def Behav.Done (X : Behav E O) (evs : List E) (o : O) : Prop := X ⟨evs, some o⟩

theorem Behav.Below.done {X Y : Behav E O} (h : X.Below Y) {evs : List E} {o : O}
    (hx : X.Done evs o) : Y.Done evs o :=
  h.completes hx rfl

/-! ## Sequencing -/

/-- Run `X`, then on a completion with events `h` and outcome `o` continue
with `K h o`.  Shown: `X`'s unfinished prefixes, each completed prefix as a
boundary (no continuation events yet), and each completed prefix followed by
a prefix of its continuation. -/
def Behav.seq (X : Behav E O) (K : List E → O → Behav E O) : Behav E O := fun p =>
  (X p ∧ p.final = none) ∨
  (∃ a o, X a ∧ a.final = some o ∧ p = ⟨a.events, none⟩) ∨
  (∃ a o k, X a ∧ a.final = some o ∧ K a.events o k ∧ p = ⟨a.events ++ k.events, k.final⟩)

/-- **Sequencing congruence**: refinement of the first part and of every
continuation gives refinement of the sequence. -/
theorem Behav.Below.seq {X X' : Behav E O} {K K' : List E → O → Behav E O} (hX : X.Below X')
    (hK : ∀ h o, (K h o).Below (K' h o)) : (X.seq K).Below (X'.seq K') := by
  intro p hp
  rcases hp with ⟨ha, hn⟩ | ⟨a, o, ha, hf, rfl⟩ | ⟨a, o, k, ha, hf, hk, rfl⟩
  · obtain ⟨b, hb, hab⟩ := hX p ha
    cases hbf : b.final with
    | none => exact ⟨b, .inl ⟨hb, hbf⟩, hab⟩
    | some o => exact ⟨⟨b.events, none⟩, .inr (.inl ⟨b, o, hb, hbf, rfl⟩), hab.1, .inl hn⟩
  · have hb : X' a := hX.completes ha hf
    exact ⟨⟨a.events, none⟩, .inr (.inl ⟨a, o, hb, hf, rfl⟩), Prefix.Le.refl _⟩
  · have hb : X' a := hX.completes ha hf
    obtain ⟨k', hk', hkk⟩ := hK a.events o k hk
    refine ⟨⟨a.events ++ k'.events, k'.final⟩, .inr (.inr ⟨a, o, k', hb, hf, hk', rfl⟩), ?_, ?_⟩
    · exact (List.prefix_append_right_inj a.events).2 hkk.1
    · rcases hkk.2 with hn | he
      · exact .inl hn
      · exact .inr (by rw [he])

/-- Sequencing is monotone in the first part alone. -/
theorem Behav.Below.seq_left {X X' : Behav E O} (K : List E → O → Behav E O) (hX : X.Below X') :
    (X.seq K).Below (X'.seq K) :=
  hX.seq fun h o => Behav.Below.refl (K h o)

/-- Sequencing is monotone in the continuations alone. -/
theorem Behav.Below.seq_right (X : Behav E O) {K K' : List E → O → Behav E O}
    (hK : ∀ h o, (K h o).Below (K' h o)) : (X.seq K).Below (X.seq K') :=
  (Behav.Below.refl X).seq hK

/-- The behaviour of one execution (a consistent family of prefixes) at the
resource bounds `A` admits. -/
def Behav.ofPrefixes {R : Type} (A : R → Prop) (p : Prefixes R E O) : Behav E O :=
  fun a => ∃ r, A r ∧ p r = a

theorem Behav.ofPrefixes_mono {R : Type} {A B : R → Prop} (h : ∀ r, A r → B r)
    (p : Prefixes R E O) : (Behav.ofPrefixes A p).Below (Behav.ofPrefixes B p) :=
  Behav.Below.of_sub fun _ ⟨r, hr, he⟩ => ⟨r, h r hr, he⟩

end Solidity.CtxEquiv
