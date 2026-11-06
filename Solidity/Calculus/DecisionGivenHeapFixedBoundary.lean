import Solidity.Calculus.DecisionGivenHeapFixedReason
import Solidity.Calculus.DecisionUIntGrammar

/-! # Frozen target admission for the fixed-array given-heap source family
Admission is derived from source syntax. The independently checked fixed-array
source extension now supplies actual coverage and a globally certified verdict.
-/
namespace Solidity.Decide.ResidueReason

/-- Existing numeric admission lifts through the actual direct memory read. -/
theorem fixedHeapUIntRead_admitted {C : Contract} {Γ : Ctx}
    (n : Nat)
    (key : Tm C (.mem (.fixed (.prim .uint) n) :: Γ) (.val .uint))
    (linear : key.UIntLinear) (waivers : Waivers) :
    (fixedHeapUIntRead n key).inTarget waivers false = true := by
  change ((key.inTarget waivers false && true) && true) = true
  rw [uintLinear_admitted linear waivers]
  rfl

theorem GivenHeapFixedReadReflexive.noAlloc {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : GivenHeapFixedReadReflexive φ) : φ.hasAllocAll = false :=
  (congrArg (fun ψ : Fml C Γ => ψ.hasAllocAll) w.equation).trans rfl

/-- Every closed member belongs to the actual unchanged target, for every waiver setting. -/
theorem GivenHeapFixedReadReflexive.target {C : Contract} {φ : Fml C []}
    (w : GivenHeapFixedReadReflexive φ) (waivers : Waivers) : φ.inTarget waivers = true := by
  rcases w with ⟨name, n, key, linear, heq⟩
  subst φ
  let body : Fml C [.mem (.fixed (.prim .uint) n)] :=
    .eq (fixedHeapUIntRead n key) (fixedHeapUIntRead n key)
  have hh : body.hasHash = false := by
    change (key.hasHash || key.hasHash) = false
    rw [uintLinear_hashFree linear]
    rfl
  have ht : body.target waivers true false = true := by
    change ((fixedHeapUIntRead n key).inTarget waivers false &&
      (fixedHeapUIntRead n key).inTarget waivers false) = true
    rw [fixedHeapUIntRead_admitted n key linear waivers]
    rfl
  have hk : body.mapKeys = [] := by
    change key.mapKeys ++ key.mapKeys = []
    rw [uintLinear_mapKeys linear]
    rfl
  have htarget : (Fml.bind .box name (.mem (.fixed (.prim .uint) n)) body).target
      waivers true false = true := by
    change (!body.hasHash && body.target waivers true false) = true
    rw [hh, ht]
    rfl
  have hkeys : (Fml.bind .box name (.mem (.fixed (.prim .uint) n)) body).mapKeys = [] := hk
  have hneg : (Fml.bind .box name (.mem (.fixed (.prim .uint) n)) body).negPairUnread
      (Fml.bind .box name (.mem (.fixed (.prim .uint) n)) body).scopeHashes true = false := by
    rfl
  unfold Fml.inTarget
  rw [htarget, hkeys, hneg]
  rfl

/-- Actual source recognition supplies the new memory coverage branch. -/
theorem GivenHeapFixedReadReflexive.memCovered {C : Contract} {φ : Fml C []}
    (w : GivenHeapFixedReadReflexive φ) : φ.memCovered = true := by
  simp only [Fml.memCovered, givenHeapFixedRead_complete w, Bool.or_true]

/-- The frozen Covered body receives the certified family through its helper. -/
theorem GivenHeapFixedReadReflexive.covered {C : Contract} {φ : Fml C []}
    (w : GivenHeapFixedReadReflexive φ) : φ.Covered = true := by
  simp only [Fml.Covered, w.memCovered, Bool.or_true, Bool.true_or]

/-- The returned global positive verdict has an all-heap source certificate. -/
theorem GivenHeapFixedReadReflexive.proved {C : Contract} {φ : Fml C []}
    (w : GivenHeapFixedReadReflexive φ) : decideGoal φ = .proved := by
  have hd : decideGoal φ ≠ .unknown := decideGoal_complete w.covered w.hashFree
  cases he : decideGoal φ with
  | proved => rfl
  | refuted σ => exact False.elim ((decideGoal_refutes he) (w.validH σ))
  | unknown => exact False.elim (hd he)

end Solidity.Decide.ResidueReason
