import Solidity.Lowering.V08.HelperPackets.ConstructorTransport.Controls

/-! H57 overlap controls for the actual constructor fixture and a representable
wide Source datum outside the legacy Word domain; no reachability claim. -/
namespace Solidity.Lowering.V08.HelperPackets.ConstructorTransport
open Solidity
open Solidity.Lowering.V07

theorem initial_legacy_related (bytes : Roadmap.Bytes) :
    MachineRelV1 bytes (initial bytes) entered
      (Source.Monetary.wordView ((initial bytes).ex.world.accounts frame.this).balance) :=
  (relations_iff_of_fits bytes (initial bytes) entered (initial_balance_fits bytes)).mpr
    (initial_related bytes)

theorem reached_legacy_related (bytes : Roadmap.Bytes) (n : Int) (h : range n) :
    MachineRelV1 bytes (reached bytes n h) (targetReached n h)
      (Source.Monetary.wordView ((reached bytes n h).ex.world.accounts frame.this).balance) :=
  (relations_iff_of_fits bytes (reached bytes n h) (targetReached n h)
    (reached_balance_fits bytes n h)).mpr (reached_related bytes n h)

/-- A wide datum is representable in Source; it is not claimed reachable. -/
def wideInitial (bytes : Roadmap.Bytes) : Source.St E :=
  {initial bytes with ex := (initial bytes).ex.apply (.account frame.this
    (fun a => {a with balance := Source.Monetary.wordLimit + 5}))}

theorem wide_initial_not_fits (bytes : Roadmap.Bytes) :
    ¬ Source.Monetary.Fits ((wideInitial bytes).ex.world.accounts frame.this).balance := by
  change ¬ Source.Monetary.wordLimit + 5 < Source.Monetary.wordLimit
  decide

theorem wide_has_no_exact_word (bytes : Roadmap.Bytes) :
    ¬ ∃ w : Roadmap.Word, w.val = ((wideInitial bytes).ex.world.accounts frame.this).balance := by
  intro h
  obtain ⟨w, balance_eq⟩ := h
  have small : Source.Monetary.Fits w.val := w.isLt
  exact wide_initial_not_fits bytes (balance_eq ▸ small)

theorem wide_legacy_view_related (bytes : Roadmap.Bytes) :
    MachineRelV1 bytes (wideInitial bytes) entered
      (Source.Monetary.wordView ((wideInitial bytes).ex.world.accounts frame.this).balance) := by
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, HEq.rfl, ?_, rfl, rfl⟩
  · exact ⟨0, by decide +kernel, rfl, rfl⟩
  · exact ⟨0, by decide +kernel, rfl, rfl⟩
  · change (Source.Monetary.wordView (Source.Monetary.wordLimit + 5)).val = 5
    decide

theorem wide_nat_relation_refused (bytes : Roadmap.Bytes) :
    ¬ MachineRelNat bytes (wideInitial bytes) entered := by
  intro h
  have impossible : Source.Monetary.wordLimit + 5 = 5 := h.balance
  exact (by decide : Source.Monetary.wordLimit + 5 ≠ 5) impossible

/-- The explicit match/Fits premise cannot be omitted from the bridge. -/
theorem legacy_view_not_unconditional_nat (bytes : Roadmap.Bytes) :
    MachineRelV1 bytes (wideInitial bytes) entered
      (Source.Monetary.wordView ((wideInitial bytes).ex.world.accounts frame.this).balance) ∧
      ¬ MachineRelNat bytes (wideInitial bytes) entered :=
  ⟨wide_legacy_view_related bytes, wide_nat_relation_refused bytes⟩

end Solidity.Lowering.V08.HelperPackets.ConstructorTransport
