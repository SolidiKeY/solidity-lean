import Solidity.Correctness.Lowering.Sim.State.Storage

/-! Successful finite lowering derivations give actual standalone lowering
receipts. This does not assert successful elaboration of the lowered output. -/
namespace Solidity.Correctness.Lowering.Sim.Coverage

open Solidity.Goals.Shrink.Lowering
open Total Total.Coverage

variable [FreshNames]

/-- Every successful finite rule derivation refines the actual producer. -/
theorem derivation_refines_production (n : Nat) :
    (∀ rs ss, Le ((derive n).list rs ss) (lowerList rs ss)) ∧
    (∀ rs s, Le ((derive n).stmt rs s) (lowerStmt rs s)) ∧
    (∀ rs s, Le ((derive n).loop rs s) (lowerLoop rs s)) := by
  induction n with
  | zero =>
    exact ⟨fun _ _ => ⟨fun _ _ _ _ _ h => nomatch h⟩,
      fun _ _ => ⟨fun _ _ _ _ _ h => nomatch h⟩,
      fun _ _ => ⟨fun _ _ _ _ _ h => nomatch h⟩⟩
  | succ n ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro rs ss
      change Le (LowerKernel.listStep (derive n).list (derive n).stmt rs ss) _
      rw [LowerKernel.fixed.1 rs ss]
      exact listStep_mono ih.1 ih.2.1 rs ss
    · intro rs s
      change Le (LowerKernel.stmtStep (derive n).list (derive n).loop rs s) _
      rw [LowerKernel.fixed.2.1 rs s]
      exact stmtStep_mono ih.1 ih.2.2 rs s
    · intro rs s
      change Le (LowerKernel.loopStep (derive n).list (derive n).loop rs s) _
      rw [LowerKernel.fixed.2.2 rs s]
      exact loopStep_mono ih.1 ih.2.2 rs s

/-- Reuse a finite derivation as the actual loop-site lowering receipt. -/
theorem lowerAt_of_lowersTo {raw out : List RawStmt} {sc : ElabScope}
    {before after : Checker.Snapshot} (h : LowersTo none raw out sc before after) :
    (((lowerAt none raw).run sc).run before.locals).run before.memo =
      .ok ((out, after.locals), after.memo) := by
  obtain ⟨depth, h⟩ := h
  change runAt depth none raw sc before = _ at h
  rw [runAt_eq] at h
  rw [lowerAt_run]
  cases hr : (derive depth).list none raw {} sc before.locals before.memo with
  | error e => simp only [hr] at h; contradiction
  | ok v =>
    rw [(derivation_refines_production depth).1 none raw |>.run _ _ _ _ _ hr]
    simpa only [hr] using h

end Solidity.Correctness.Lowering.Sim.Coverage
