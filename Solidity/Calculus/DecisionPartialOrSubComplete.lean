import Solidity.Calculus.DecisionPartialOrSub

/-!
# Recognition of the subtraction-literal partial-OR family is complete

Every source formula `PartialOrRoots.subClaim sp i j c v k r` with a halting
subtraction literal `c` is found by `partialOrSub?`: its roots are among the
declared ones and `c`, `v`, `k`, `r` among the skeleton's literals. So
`Fml.partialOrSub` classifies the stated family exactly (`partialOrSub_iff`).
-/
namespace Solidity.Decide.ResidueReason
variable {C : Contract}

/-- The literals of a member's source skeleton include all four parameters. -/
theorem subClaim_literals (sp : PartialOrRoots C) (i j : Var)
    (c value key result : PrimTy.uint.Denote) :
    c ∈ sourceUIntChainLiterals (sp.subClaim i j c value key result) ∧
    value ∈ sourceUIntChainLiterals (sp.subClaim i j c value key result) ∧
    key ∈ sourceUIntChainLiterals (sp.subClaim i j c value key result) ∧
    result ∈ sourceUIntChainLiterals (sp.subClaim i j c value key result) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change c ∈ ((((_ ++ (_ ++ (_ ++ [c]))) ++ _) ++ _) ++ _) ++ _
    simp only [List.mem_append, List.mem_singleton, true_or, or_true]
  · change value ∈ (_ ++ (_ ++ [value])) ++ _
    simp only [List.mem_append, List.mem_singleton, true_or, or_true]
  · change key ∈ _ ++ ((_ ++ (_ ++ [key])) ++ _)
    simp only [List.mem_append, List.mem_singleton, true_or, or_true]
  · change result ∈ _ ++ (_ ++ [result])
    simp only [List.mem_append, List.mem_singleton, true_or, or_true]

/-- **Completeness of recognition**: every member with a halting literal is found. -/
theorem partialOrSub_complete {sp : PartialOrRoots C} {c value key result : PrimTy.uint.Denote}
    {i j : Var} {φ : Fml C []} (hc : binopT (p := .uint) .sub rfl (uintOfNat 0) (some c) = none)
    (he : φ = sp.subClaim i j c value key result) : φ.partialOrSub = true := by
  subst he
  have hl := subClaim_literals sp i j c value key result
  have hs : partialOrShape (sp.subClaim i j c value key result) = true := rfl
  unfold Fml.partialOrSub partialOrSub?
  simp only [hs, Bool.not_true, Bool.false_eq_true, if_false, List.findSome?_isSome_iff]
  refine ⟨sp, partialOrRootsOf_mem sp, c, hl.1, value, hl.2.1, key, hl.2.2.1, result, hl.2.2.2, ?_⟩
  unfold partialOrSubAt?
  simp only [dif_pos hc, sourceImpView?, sourceUIntAllView?, dif_pos True.intro,
    sourceEquationSame_self, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.isSome_some, PartialOrRoots.subClaim, PartialOrRoots.subBlock]

/-- Exact classification of the stated family. -/
theorem partialOrSub_iff {φ : Fml C []} :
    φ.partialOrSub = true ↔ Nonempty (PartialOrSub φ) := by
  constructor
  · intro h
    unfold Fml.partialOrSub at h
    cases hw : partialOrSub? φ with
    | none => rw [hw] at h; cases h
    | some w => exact ⟨w⟩
  · intro ⟨w⟩
    exact partialOrSub_complete w.halts w.equation

end Solidity.Decide.ResidueReason
