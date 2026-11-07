import Solidity.Examples.Decision

/-! Exact three-kind coverage certificate for the original decision gap pin. -/
namespace Solidity.Examples.Decision
open Solidity.Decide
set_option Elab.async false

/-! The exact transformation outputs and coverage conjuncts are certified separately
to keep kernel checking bounded. The `getD` defaults are unreachable by the
`*_some` certificates; no decision default or coverage condition changes. -/

private theorem some_getD {α : Type} (o : Option α) (d : α) (h : o.isSome = true) :
    o = some (o.getD d) := by
  cases o with
  | none => cases h
  | some a => rfl
private def routeFirst : Fml Solidity.Examples.Tactics.Hashing.Names [] :=
  (gapThreeKinds.tk3 .ripemd160 .keccak .sha256 (famN gapThreeKinds.allocCount) false false).getD .tt
private theorem first_some :
    gapThreeKinds.tk3 .ripemd160 .keccak .sha256 (famN gapThreeKinds.allocCount) false false = some routeFirst :=
  some_getD _ .tt (by decide +kernel)
private def routePrefix : Fml Solidity.Examples.Tactics.Hashing.Names [] :=
  (routeFirst.swPrefix .ripemd160).getD .tt
private theorem prefix_some : routeFirst.swPrefix .ripemd160 = some routePrefix :=
  some_getD _ .tt (by decide +kernel)
private def routeFull : Fml Solidity.Examples.Tactics.Hashing.Names [] :=
  (gapThreeKinds.tk3 .ripemd160 .keccak .sha256 (famN gapThreeKinds.allocCount) true true).getD .tt
private theorem full_some :
    gapThreeKinds.tk3 .ripemd160 .keccak .sha256 (famN gapThreeKinds.allocCount) true true = some routeFull :=
  some_getD _ .tt (by decide +kernel)
private theorem prefix_covered : routePrefix.Covered = true := by decide +kernel
private theorem family_covered : famCovered gapThreeKinds.allocCount = true := by decide +kernel
private theorem instances_covered :
    (rgs routeFirst.allocCount).all (fun cs => (routeFull.swInst .ripemd160 cs).any Fml.Covered) = true := by
  decide +kernel
private theorem regions_linked :
    routeFirst.swRL .ripemd160 routeFirst.allocLevels (routePrefix.vRoots routeFirst.allocLevels) = true := by
  decide +kernel
private theorem prefix_ok : routeFirst.prefixOK routeFirst.allocLevels = true := by decide +kernel
private theorem roots_typed :
    kTypedB Solidity.Examples.Tactics.Hashing.Names (routePrefix.vRoots routeFirst.allocLevels) = true := by
  decide +kernel
private theorem layers_linked :
    gapThreeKinds.tk3RL .ripemd160 .keccak .sha256 (famN gapThreeKinds.allocCount) = true := by decide +kernel
private theorem positive_prefix : routeFirst.posAll = true := by decide +kernel
private theorem route_covered : gapThreeKinds.coveredK3 .ripemd160 .keccak .sha256 = true := by
  simp only [Fml.coveredK3, first_some, prefix_some, full_some, prefix_covered,
    family_covered, instances_covered, regions_linked, prefix_ok, roots_typed,
    layers_linked, positive_prefix, Bool.true_and]
theorem gapThreeKinds_covered : gapThreeKinds.hashCovered = true := by
  let T : HashTry Solidity.Examples.Tactics.Hashing.Names :=
    tryK3 .ripemd160 .keccak .sha256 (by decide) (by decide) (by decide)
  have hc : T.covers = Fml.coveredK3 .ripemd160 .keccak .sha256 := rfl
  have ht : T.covers gapThreeKinds = true := by
    rw [hc]
    exact route_covered
  have hm : T ∈ hashTries (C := Solidity.Examples.Tactics.Hashing.Names) := by
    unfold hashTries
    iterate 13 apply List.mem_cons_of_mem
    exact List.mem_cons_self
  unfold Fml.hashCovered
  simp only [Bool.and_eq_true]
  exact ⟨by decide +kernel, List.any_eq_true.mpr ⟨T, hm, ht⟩⟩


end Solidity.Examples.Decision
