import Solidity.Semantics.RecursiveStorage.Arrays

/-! Operation-side commutation over the published intrinsic slot update.
These laws neither define a new store nor prove an EVM representation. -/

namespace Solidity.Backend.StorageOps

open TypeGraph

/-- Two writes at distinct keys commute, with no assumption on stored values
or on whether the slots were previously absent, live, or retained. -/
theorem writes_commute {K : Type} [DecidableEq K] {n : Nat}
    {G : Schema n} {E : TypeGraph.Ty n} (slots : K → Slot G E)
    (a b : K) (different : a ≠ b) (x y : Value G E) :
    Slots.write (Slots.write slots a x) b y =
      Slots.write (Slots.write slots b y) a x := by
  funext k
  by_cases ka : k = a
  · subst k
    simp only [Slots.write, if_neg different]
  · by_cases kb : k = b
    · subst k
      simp only [Slots.write, if_neg ka]
    · simp only [Slots.write, if_neg ka, if_neg kb]

/-- Commutation lifted to the actual indexed array path operation. The
indices must be distinct, but need not lie in the live prefix: retained
aliases address the same slots across shrink/regrow operations. -/
theorem array_puts_commute {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (extent : Extent) (length : Index) (live : length.val ≤ extent.val)
    (slots : Fin extent.val → Slot G E) (a b : Index)
    (ha : a.val < extent.val) (hb : b.val < extent.val)
    (different : a.val ≠ b.val) (x y : Value G E) :
    ((TypeGraph.Step.index a).put (.array extent length live slots) x).bind
      (fun v => (TypeGraph.Step.index b).put v y) =
    ((TypeGraph.Step.index b).put (.array extent length live slots) y).bind
      (fun v => (TypeGraph.Step.index a).put v x) := by
  simp only [TypeGraph.Step.put, dif_pos ha, dif_pos hb, Option.bind_some]
  have separate : (⟨a.val, ha⟩ : Fin extent.val) ≠ ⟨b.val, hb⟩ :=
    fun equal => different (congrArg (fun k : Fin extent.val => k.val) equal)
  rw [writes_commute slots _ _ separate x y]

end Solidity.Backend.StorageOps
