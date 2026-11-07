import Solidity.Yul.Views.MultiRootByteWrites

/-! Exact chronological composition of actual coupled source writes. A failed
prefix skips the suffix in both source and raw memory; a successful prefix
feeds its reached state and raw map directly into the next plan. -/
namespace Solidity.Yul.Views.MultiRootByteAppend
open MultiRootByteWrites

theorem coupled_append {E Γ} (F : Source.Fr) (horizon : Nat) (addresses : Nat → Nat)
    (first second : List Request) (s : Source.EMState E Γ) (memory : ByteView) :
    coupled F horizon addresses (first++second) s memory=
      let reached := coupled F horizon addresses first s memory
      match reached.1.1 with
      | .error _ => reached
      | .ok _ => coupled F horizon addresses second reached.1.2 reached.2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  induction first generalizing s memory with
  | nil => rfl
  | cons request rest ih =>
    rw [List.cons_append,coupled]
    rcases executed : (action F horizon request).run s with ⟨outcome,after⟩
    cases outcome with
    | error reason => simp only [executed,coupled]
    | ok value =>
      cases value
      simp only [executed,coupled]
      exact ih after _
end Solidity.Yul.Views.MultiRootByteAppend
