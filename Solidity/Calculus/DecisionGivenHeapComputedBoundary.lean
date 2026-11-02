import Solidity.Calculus.DecisionGivenHeapComputedReason
import Solidity.Calculus.DecisionUIntGrammar

/-! # Frozen target admission for the nonliteral given-heap source family
These are source facts, not global coverage or decision registration. The
existing computed-index unknown observation remains unchanged.
-/
namespace Solidity.Decide.ResidueReason

/-- Existing numeric admission lifts through the actual direct memory read. -/
theorem computedHeapUIntRead_admitted {C : Contract} {Γ : Ctx}
    (key : Tm C (.mem (.array (.prim .uint)) :: Γ) (.val .uint))
    (linear : key.UIntLinear) (waivers : Waivers) :
    (computedHeapUIntRead key).inTarget waivers false = true := by
  change ((key.inTarget waivers false && true) && true) = true
  rw [uintLinear_admitted linear waivers]
  rfl

theorem GivenHeapLinearReadReflexive.noAlloc {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (w : GivenHeapLinearReadReflexive φ) : φ.hasAllocAll = false :=
  (congrArg (fun ψ : Fml C Γ => ψ.hasAllocAll) w.equation).trans rfl

/-- Every closed member belongs to the actual unchanged target, for every waiver setting. -/
theorem GivenHeapLinearReadReflexive.target {C : Contract} {φ : Fml C []}
    (w : GivenHeapLinearReadReflexive φ) (waivers : Waivers) : φ.inTarget waivers = true := by
  rcases w with ⟨name, key, linear, nonliteral, heq⟩
  subst φ
  let body : Fml C [.mem (.array (.prim .uint))] :=
    .eq (computedHeapUIntRead key) (computedHeapUIntRead key)
  have hh : body.hasHash = false := by
    change (key.hasHash || key.hasHash) = false
    rw [uintLinear_hashFree linear]
    rfl
  have ht : body.target waivers true false = true := by
    change ((computedHeapUIntRead key).inTarget waivers false &&
      (computedHeapUIntRead key).inTarget waivers false) = true
    rw [computedHeapUIntRead_admitted key linear waivers]
    rfl
  have hk : body.mapKeys = [] := by
    change key.mapKeys ++ key.mapKeys = []
    rw [uintLinear_mapKeys linear]
    rfl
  have htarget : (Fml.bind .box name (.mem (.array (.prim .uint))) body).target
      waivers true false = true := by
    change (!body.hasHash && body.target waivers true false) = true
    rw [hh, ht]
    rfl
  have hkeys : (Fml.bind .box name (.mem (.array (.prim .uint))) body).mapKeys = [] := hk
  have hneg : (Fml.bind .box name (.mem (.array (.prim .uint))) body).negPairUnread
      (Fml.bind .box name (.mem (.array (.prim .uint))) body).scopeHashes true = false := by
    rfl
  unfold Fml.inTarget
  rw [htarget, hkeys, hneg]
  rfl

end Solidity.Decide.ResidueReason
