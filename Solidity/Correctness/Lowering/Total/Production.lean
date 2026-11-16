import Solidity.Correctness.Lowering.Total.Contract

/-! E2D: the production loop lowering implements the frozen relation `LowersTo`.

The totalized production family `lowerList`/`lowerStmt`/`lowerLoop` is the unique
fixpoint of the kernel step (`LowerKernel.fixed`, `LowerKernel.contractive`), and
`derive` iterates that same step from the refusing triple. So below its depth a
derivation is the production family, as whole `LowerM` computations: for every
return-slot list, every admitted or refused constructor, every loop-flag state,
reader scope, locals, fresh counter and callee memo. No premise on the input,
the name supply or the outcome is used, and nothing here is about the meaning of
the lowered program. -/
namespace Solidity.Correctness.Lowering.Total

open Solidity.LowerKernel

section Production
variable [FreshNames]

/-- A derivation of depth `d` is the production family at every argument of
measure below `d`. -/
theorem derive_eq_production (d : Nat) :
    (∀ rs ss, listMeasure ss < d → (derive d).list rs ss = lowerList rs ss) ∧
    (∀ rs s, stmtMeasure s < d → (derive d).stmt rs s = lowerStmt rs s) ∧
    (∀ rs s, loopMeasure s < d → (derive d).loop rs s = lowerLoop rs s) := by
  induction d with
  | zero => exact ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ d ih =>
    have below (n : Nat) (hn : n ≤ d) :=
      contractive n (derive d).list lowerList (derive d).stmt lowerStmt (derive d).loop lowerLoop
        (fun rs ss h => ih.1 rs ss (Nat.lt_of_lt_of_le h hn))
        (fun rs s h => ih.2.1 rs s (Nat.lt_of_lt_of_le h hn))
        (fun rs s h => ih.2.2 rs s (Nat.lt_of_lt_of_le h hn))
    exact ⟨fun rs ss h => ((below _ (Nat.le_of_lt_succ h)).1 rs ss rfl).trans (fixed.1 rs ss).symm,
      fun rs s h => ((below _ (Nat.le_of_lt_succ h)).2.1 rs s rfl).trans (fixed.2.1 rs s).symm,
      fun rs s h => ((below _ (Nat.le_of_lt_succ h)).2.2 rs s rfl).trans (fixed.2.2 rs s).symm⟩

/-- The block derivation one above the measure of its input is `lowerList`. -/
theorem derive_list_eq (rs : Option (List String)) (ss : List RawStmt) :
    (derive (listMeasure ss + 1)).list rs ss = lowerList rs ss :=
  (derive_eq_production _).1 rs ss (Nat.lt_succ_self _)

/-- Every production run, successful or refused, is a derivation run from the
same complete state: the depth is read off the input's syntax alone. -/
theorem lowerLoops_eq_derive (rs : Option (List String)) (ss : List RawStmt) :
    lowerLoops rs ss =
      (do pure (← ((derive (listMeasure ss + 1)).list rs ss).run' {}).1 : ElabM (List RawStmt)) := by
  rw [derive_list_eq]; rfl

end Production

/-- **Production lowering implements `LowersTo`** (e2d-loops-production): every
successful `lowerLoops` run, at every spelling of fresh names, return-slot list,
raw input, reader scope and complete incoming state, is in the frozen relation,
with its exact output and complete outgoing state. -/
theorem universalProducerCorrect : UniversalProducerCorrect := by
  intro input output run
  letI : FreshNames := input.names
  refine ⟨listMeasure input.raw + 1, ?_⟩
  rw [← lowerLoops_eq_derive]
  exact run

end Solidity.Correctness.Lowering.Total
