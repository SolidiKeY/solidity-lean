import Solidity.Backend.MemoryCopies.DefaultDemand
import Solidity.Backend.MemoryCopies.InterfaceV2Laws

/-! Actual finite plans, intrinsic nested defaults and negative cost controls.
Generic demand does not imply finite-plan selection or runtime capacity. -/
namespace Solidity.Backend.MemoryCopies.DefaultDemandControls
open Evm Evm.Memory

private def basket : DefaultPlan (.struct "Basket") :=
  (defaultPlan? (.struct "Basket")).get (by decide +kernel)
private def person : DefaultPlan (.struct "Person") :=
  (defaultPlan? (.struct "Person")).get (by decide +kernel)
private def seed := (Heap.empty.allocDefault (.struct "Basket") rfl)
private def after := seed.heap.allocDefault (.struct "Person") rfl

theorem certificate_inhabited : DefaultDemandCertificate := defaultDemand

theorem actual_plans : defaultPlan? (.struct "Basket") = some basket ∧
    defaultPlan? (.struct "Person") = some person ∧ basket.cost = 2 ∧ person.cost = 5 := by
  refine ⟨(Option.some_get _).symm, (Option.some_get _).symm, ?_, ?_⟩
  · decide +kernel
  · decide +kernel

theorem plan_heap_growth : heapWords seed.heap = 2 ∧ heapWords after.heap = 7 := by
  decide +kernel

theorem arbitrary_heap_plan {H : HTy} (heap : Heap H) :
    heapWords (heap.allocDefault (.struct "Person") rfl).heap = heapWords heap + 5 := by
  have cost : person.cost = 5 := actual_plans.2.2.2
  simpa only [cost] using default_plan_words person heap rfl

/-- The narrower compiler refuses this reference-member struct; its estimate
is not used as an accepted finite-plan cost. -/
theorem primitive_cost_boundary : ReferenceDefaults.defaultCells (.ref (.struct "Basket")) = 1 ∧
    ReferenceDefaults.compileDefault (.struct "Basket") rfl = none ∧
    finiteDefaultCells (.ref (.struct "Basket")) = some 2 ∧
    liveWordCount (SVal.dflt (.ref (.struct "Basket"))) ≠ 1 := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simpa only [actual_plans.2.2.1] using basket.cells
  · rw [finite_default_words (.ref (.struct "Basket")) basket.cost basket.cells, actual_plans.2.2.1]
    decide

theorem empty_fixed (element : Ty) :
    liveWordCount (SVal.dflt (.ref (.fixed element 0))) = 1 := by
  rw [fixed_default_words]
  simp only [Nat.zero_mul, Nat.add_zero, Nat.max_eq_left (Nat.zero_le _)]

theorem dynamic_reference_default (element : Ty) :
    liveWordCount (SVal.dflt (.ref (.array (.ref (.array element))))) = 1 :=
  dynamic_default_words _

theorem nested_fixed_default :
    liveWordCount (SVal.dflt (.ref (.fixed (.ref (.fixed (.ref (.array (.prim .uint))) 2)) 3))) = 15 := by
  rw [fixed_default_words, fixed_default_words, dynamic_default_words]
  decide

theorem long_reference_default :
    liveWordCount (SVal.dflt (.ref (.fixed (.ref (.array (.prim .uint))) 64))) = 128 := by
  rw [fixed_default_words, dynamic_default_words]
  decide

/-- No element of an empty fixed parent is constructed, even when its child's
intrinsic standalone demand would be too large for a word allocator. -/
theorem unused_huge_child :
    liveWordCount (SVal.dflt (.ref (.fixed (.ref (.fixed (.prim .uint) W)) 0))) = 1 :=
  empty_fixed _

theorem finite_selector_boundary : finiteDefaultCells (.ref (.fixed (.prim .uint) 2)) = none ∧
    liveWordCount (SVal.dflt (.ref (.fixed (.prim .uint) 2))) = 2 := by
  constructor
  · rw [finiteDefaultCells]
  · rw [fixed_default_words, SVal.dflt_prim, liveWordCount]
    decide

/-- Word-size exhaustion is a capacity obstruction; no Source panic or gas
outcome follows from this intrinsic demand equation. -/
theorem no_word_capacity :
    liveWordCount (SVal.dflt (.ref (.fixed (.prim .uint) W))) = W ∧
    ¬ Nonempty (V2.AllocatorWitness W) := by
  constructor
  · rw [fixed_default_words, SVal.dflt_prim, liveWordCount]
    have positive : 1 ≤ W := Nat.succ_le_of_lt W_pos
    simp only [Nat.mul_zero, Nat.add_zero, Nat.max_eq_right positive]
  · intro witness
    obtain ⟨witness⟩ := witness
    have impossible : W < W := witness.cost_lt
    omega

#print axioms certificate_inhabited
#print axioms actual_plans
#print axioms plan_heap_growth
#print axioms arbitrary_heap_plan
#print axioms primitive_cost_boundary
#print axioms empty_fixed
#print axioms dynamic_reference_default
#print axioms nested_fixed_default
#print axioms long_reference_default
#print axioms unused_huge_child
#print axioms finite_selector_boundary
#print axioms no_word_capacity
end Solidity.Backend.MemoryCopies.DefaultDemandControls
