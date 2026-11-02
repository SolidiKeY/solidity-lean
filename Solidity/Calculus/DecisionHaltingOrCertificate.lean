import Solidity.Calculus.DecisionHaltingOrReason

/-! # Positive-key partial-OR certificates
These source certificates leave guard reconstruction and decision dispatch unchanged.
-/
namespace Solidity.Decide.ResidueReason
namespace PartialOrRoots
variable {C : Contract}

/-- A positive first key and zero second key bypass the partial subtraction. -/
theorem sourceGuard_positive (sp : PartialOrRoots C) (σ : State C [])
    (key : PrimTy.uint.Denote) (hk : 0 < key.1) :
    holds ((σ.push (t := .val .uint) key).push
      (t := .val .uint) (uintOfNat 0))
      (.eq sp.sourceGuard (.app0 (.lit true))) := by
  have hz : decide (key.1 ≤ 0) = false := decide_eq_false (by omega)
  change ((some (decide (key.1 ≤ 0))).bind
    (fun x => binopT (p := .bool) .and rfl x _)).bind
    (fun x => binopT (p := .bool) .or rfl x (some (decide (key.1 ≤ key.1)))) = some true
  rw [hz]
  change some (decide (key.1 ≤ key.1)) = some true
  simp only [Int.le_refl, decide_true]

/-- Instantiate the actual two-binder antecedent; no scalar definedness premise. -/
theorem sourceClaim_positive_valid (sp : PartialOrRoots C) (first second : Var)
    (value key : PrimTy.uint.Denote) (hk : 0 < key.1) :
    Fml.Valid (sp.sourceClaim first second value key value) := by
  intro σ h
  exact h key (uintOfNat 0) (sp.sourceGuard_positive σ key hk)

end PartialOrRoots

/-- Transport the exact source equation; the result literal must match the block. -/
theorem PartialOrBlockAt.valid_positive {C : Contract} {sp : PartialOrRoots C}
    {value key : PrimTy.uint.Denote} {φ : Fml C []}
    (w : PartialOrBlockAt sp value key value φ) (hk : 0 < key.1) : Fml.Valid φ := by
  rw [w.equation]
  exact sp.sourceClaim_positive_valid w.first w.second value key hk

/-- The hash-free source family needs no hash-model assumption. -/
theorem PartialOrBlockAt.validH_positive {C : Contract} {sp : PartialOrRoots C}
    {value key : PrimTy.uint.Denote} {φ : Fml C []}
    (w : PartialOrBlockAt sp value key value φ) (hk : 0 < key.1) : Fml.ValidH φ :=
  fun σ => (Fml.holdsH_iff σ φ w.hashFree).mpr (w.valid_positive hk σ)

end Solidity.Decide.ResidueReason
