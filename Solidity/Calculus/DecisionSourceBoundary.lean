import Solidity.Calculus.Decision

/-! # Computed source-family allocation boundary
Recognition proves absence of fresh-allocation binders. Neither target
membership nor hash freedom follows from this source grammar; the existing
hash-free premise remains explicit on public verdicts.
-/
namespace Solidity.Decide

private theorem substU_equation_noAlloc {C : Contract} {Γ Δ : Ctx}
    (U : Upd C Γ Δ) (φ : Fml C Δ) {p : PrimTy}
    {a b : Tm C Γ (.val p)} (h : Fml.substU U φ = some (.eq a b)) :
    φ.hasAllocAll = false := by
  cases φ <;> simp only [Fml.substU] at h
  case eq => rfl
  case wellFormed =>
    obtain ⟨term, ht, he⟩ := Option.map_eq_some_iff.mp h
    cases he
  case not =>
    obtain ⟨body, hb, he⟩ := Option.map_eq_some_iff.mp h
    cases he
  case and =>
    obtain ⟨left, hl, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨right, hr, he⟩ := Option.bind_eq_some_iff.mp h
    cases he
  case imp =>
    obtain ⟨left, hl, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨right, hr, he⟩ := Option.bind_eq_some_iff.mp h
    cases he
  all_goals cases h

/-- An actual substituted equation cannot hide an allocation formula. -/
theorem SourceUIntLiteralInstance.noAlloc {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    {bound value : PrimTy.uint.Denote} (w : SourceUIntLiteralInstance φ bound value) :
    φ.hasAllocAll = false := by
  have hb : w.body.hasAllocAll = false :=
    substU_equation_noAlloc _ w.body w.instanceEq
  rw [w.equation]
  change ((false || w.body.hasAllocAll) || false) = false
  rw [hb]
  rfl

/-- Universal prefixes preserve the syntactically proved allocation boundary. -/
theorem SourceUIntLiteralChain.noAlloc {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    {bound value : PrimTy.uint.Denote} (w : SourceUIntLiteralChain bound value φ) :
    φ.hasAllocAll = false := by
  induction w with
  | leaf atom => exact atom.noAlloc
  | all name prim chain ih => exact ih

theorem sourceUIntLiteralDiscovery_noAlloc {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (h : (sourceUIntLiteralDiscovery? φ).isSome = true) : φ.hasAllocAll = false := by
  obtain ⟨candidate⟩ := sourceUIntLiteralDiscovery_witness h
  exact candidate.witness.noAlloc

/-- Actual source syntax suffices; absence of allocation is no longer supplied. -/
theorem sourceUIntLiteralDiscovery_covered {C : Contract} {φ : Fml C []}
    (h : (sourceUIntLiteralDiscovery? φ).isSome = true) : φ.Covered = true :=
  sourceUIntLiteral_covered (sourceUIntLiteralDiscovery_noAlloc h) h

/-- The old hash premise remains explicit, independent of source recognition. -/
theorem sourceUIntLiteralDiscovery_proved {C : Contract} {φ : Fml C []}
    (h : (sourceUIntLiteralDiscovery? φ).isSome = true) (hh : φ.hasHash = false) :
    decideGoal φ = .proved :=
  sourceUIntLiteral_proved (sourceUIntLiteralDiscovery_noAlloc h) h hh

end Solidity.Decide
