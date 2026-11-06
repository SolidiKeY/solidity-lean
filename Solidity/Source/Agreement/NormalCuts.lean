import Solidity.Source.Agreement.NormalStep

/-! Checked normal-result cuts of the existing Source monad. These lemmas
observe actual runs; they neither select intermediate states nor change the
Source evaluator or resource model. -/
namespace Solidity.Source.Agreement

variable {E : Env}

private theorem bind_ok {α β : Type} (m : EM E [] α) (f : α → EM E [] β)
    (initial final : Locals E.layout [] × St E) (v : β)
    (h : (m >>= f).run initial = (.ok v, final)) :
    ∃ a middle, m.run initial = (.ok a, middle) ∧
      (f a).run middle = (.ok v, final) := by
  change (ExceptT.bindCont f (m.run initial).1) (m.run initial).2 = _ at h
  cases hm : m.run initial with
  | mk result middle =>
    cases result with
    | error err => rw [hm] at h; cases h
    | ok a => exact ⟨a, middle, rfl, by simpa only [hm, ExceptT.bindCont] using h⟩

private theorem lift_run {α : Type} (r : R α) (j : Locals E.layout [] × St E) :
    (EM.lift r : EM E [] α).run j = (r, j) := by
  cases r <;> rfl

private theorem up_normal {D : Layout} {Γ₀ Γ₁ Γ₂ : RCtx}
    (out : Source.Out D Γ₁ Γ₂) (ls : Locals D Γ₂)
    (h : out.up Γ₀ = .ok (.normal ls)) : out = .normal ls := by
  cases out with
  | normal l => cases h; rfl
  | brk l => cases hr : l.restore Γ₀ <;> simp only [Source.Out.up, hr] at h <;> cases h
  | cont l => cases hr : l.restore Γ₀ <;> simp only [Source.Out.up, hr] at h <;> cases h
  | ret l => cases hr : l.restore Γ₀ <;> simp only [Source.Out.up, hr] at h <;> cases h

theorem source_cons_cut {R : List STy} {M : Bool} {k : SCtx}
    {Γ₀ Γ₁ Γ₂ : RCtx} (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E))
    (s : RStmt E R M k Γ₀ Γ₁) (rest : RItems E R M k Γ₁ Γ₂)
    (ls : Locals E.layout Γ₀) (st : St E) (ls' : Locals E.layout Γ₂)
    (journal : Locals E.layout [] × St E)
    (h : (execItems G F (n+1) nps ph (.stmt s rest) ls).run (.nil, st) =
      (.ok (.normal ls'), journal)) :
    ∃ middle middleState,
      (execS G F n nps ph s ls).run (.nil, st) = (.ok (.normal middle), (.nil, middleState)) ∧
      (execItems G F n nps ph rest middle).run (.nil, middleState) =
        (.ok (.normal ls'), journal) := by
  change ((execS G F n nps ph s ls >>= fun out => match out with
    | .normal mid => do EM.lift ((← execItems G F n nps ph rest mid).up Γ₀)
    | .brk mid => pure (.brk mid)
    | .cont mid => pure (.cont mid)
    | .ret mid => pure (.ret mid)) : EM E [] (Source.Out E.layout Γ₀ Γ₂)).run (.nil, st) = _ at h
  obtain ⟨out, ⟨jlocals, middleState⟩, first, next⟩ := bind_ok _ _ _ _ _ h
  cases jlocals
  cases out with
  | normal middle =>
    obtain ⟨last, lastJournal, tail, lifted⟩ := bind_ok _ _ _ _ _ next
    rw [lift_run] at lifted
    have he : last.up Γ₀ = .ok (.normal ls') := (Prod.mk.inj lifted).1
    have hj : lastJournal = journal := (Prod.mk.inj lifted).2
    have hn : last = .normal ls' := up_normal last ls' he
    subst last
    subst lastJournal
    exact ⟨middle, middleState, first, tail⟩
  | brk mid => cases next
  | cont mid => cases next
  | ret mid => cases next

end Solidity.Source.Agreement
