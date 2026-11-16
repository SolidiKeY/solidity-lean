import Solidity.Roadmap.V16.Transport

/-!
# Relational finite-prefix, observation and resource composition

These laws consume the existing G01 relations/certificates. Forward/Guard are
carried across the middle language only by an actual certificate; no transitivity
of arbitrary guarded relations (which would be false) is asserted.
-/
namespace Solidity.Roadmap.V16

/-- A language execution refines itself on precisely the same resource set. -/
theorem refinement_refl {R E O : Type} (A : R → Prop) (p : Prefixes R E O) :
    Refines A A p p :=
  ⟨fun r hr => ⟨r, hr, Prefix.Le.refl _⟩, fun r hr => ⟨r, hr, Prefix.Le.refl _⟩⟩

/-- Relational prefix composition preserves the entire ordered event list
and final observation of a completed source, not merely event membership. -/
theorem composed_observation {R₁ R₂ R₃ E O : Type}
    {A₁ : R₁ → Prop} {A₂ : R₂ → Prop} {A₃ : R₃ → Prop}
    {p₁ : Prefixes R₁ E O} {p₂ : Prefixes R₂ E O} {p₃ : Prefixes R₃ E O}
    (h₁₂ : Refines A₁ A₂ p₁ p₂) (h₂₃ : Refines A₂ A₃ p₂ p₃)
    {r : R₁} (ha : A₁ r) {o : O} (ho : (p₁ r).final = some o) :
    ∃ t, A₃ t ∧ p₃ t = p₁ r := by
  obtain ⟨t, ht, hp⟩ := (h₁₂.trans h₂₃).1 r ha
  exact ⟨t, ht, hp.final_eq ho⟩

/-- A bad prefix property transports only when it is downward closed.
The intermediate admissibility predicate is identical in both premises. -/
theorem composed_safety {R₁ R₂ R₃ E O : Type}
    {A₁ : R₁ → Prop} {A₂ : R₂ → Prop} {A₃ : R₃ → Prop}
    {p₁ : Prefixes R₁ E O} {p₂ : Prefixes R₂ E O} {p₃ : Prefixes R₃ E O}
    (h₁₂ : Refines A₁ A₂ p₁ p₂) (h₂₃ : Refines A₂ A₃ p₂ p₃)
    (P : Prefix E O → Prop) (down : ∀ a b, a.Le b → P b → P a)
    (hs : ∀ r, A₁ r → P (p₁ r)) : ∀ r, A₃ r → P (p₃ r) :=
  (h₁₂.trans h₂₃).safety P down hs

section Certificate
variable {E O : Type} {L₁ L₂ L₃ : Lang E O}
    {π₁ : Pass L₁ L₂} {π₂ : Pass L₂ L₃}

/-- Certificate composition names the nested bound exactly. This equation
introduces no choice, but neither certifies computability of arbitrary inputs. -/
theorem composed_need (c₁ : Cert π₁) (c₂ : Cert π₂)
    (closed : ∀ p h, π₂.Dom (π₁.run p h))
    (p : L₁.Prog) (hd : π₁.Dom p) (e : L₃.Env) (r : L₁.Res) :
    (c₁.comp c₂ closed).need p hd e r =
      c₂.need (π₁.run p hd) (closed p hd) e (c₁.need p hd (π₂.envAbs e) r) := rfl

/-- At that very nested bound, completion has the exact same ordered events
and outcome. Source Forward/Guard and both actual pass certificates are owed. -/
theorem composed_completion (c₁ : Cert π₁) (c₂ : Cert π₂)
    (closed : ∀ p h, π₂.Dom (π₁.run p h))
    (p : L₁.Prog) (hd : π₁.Dom p) (e : L₃.Env) (he : L₃.Allowed e)
    (r : L₁.Res) (ha : L₁.Admissible r)
    (hf : L₁.Forward p (π₁.envAbs (π₂.envAbs e)) r)
    (hg : L₁.Guard p (π₁.envAbs (π₂.envAbs e)) r)
    {o : O} (ho : (L₁.sem p (π₁.envAbs (π₂.envAbs e)) r).final = some o) :
    L₃.Admissible ((c₁.comp c₂ closed).need p hd e r) ∧
      L₃.sem ((π₁.comp π₂ closed).run p hd) e ((c₁.comp c₂ closed).need p hd e r) =
        L₁.sem p (π₁.envAbs (π₂.envAbs e)) r :=
  completion_at_need (c₁.comp c₂ closed) p hd e he r ha hf hg ho
end Certificate
end Solidity.Roadmap.V16
