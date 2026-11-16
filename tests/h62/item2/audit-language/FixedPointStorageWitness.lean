import tests.h62.item2.«audit-language».FullTelescopeWitness
import Solidity.Language.FixedPoint.Storage

/-!
Guarded regression: packed-storage feasibility must jointly retain word bounds,
field bounds and nonoverlap; empty layouts cannot witness a neighbour-frame law.
Use nonzero offsets, a signed value and nonempty layouts with same-slot packing
and slot rollover. Imported telescope reflection checks all actual parameters
and premises. Mapping-key words are not a hash-injectivity claim, and these are
reference-storage witnesses, not source compiler or EVM storage correctness.
-/
set_option autoImplicit false

namespace Solidity.H62.AuditLanguage.FixedPointStorageWitness
open Solidity.Language.FixedPoint

def smallTy : FxTy := ⟨false, 8, 1, by decide⟩
def signedTy : FxTy := ⟨true, 16, 1, by decide⟩
def wideTy : FxTy := ⟨false, 256, 0, by decide⟩
def seven : Fx smallTy := ⟨7, by decide⟩
def negativeSeven : Fx signedTy := ⟨-7, by decide⟩
def word : Slot := ⟨1193046, by decide⟩
def state : Store := fun slot => ⟨slot % 2 ^ 256, Nat.mod_lt _ (Nat.two_pow_pos 256)⟩
def sizes : List Nat := [1, 2, 32]
def types : List FxTy := [smallTy, signedTy, wideTy]

theorem sizes_fit : ∀ size ∈ sizes, size ≤ 32 := by
  intro size h
  simp only [sizes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> decide

theorem offset_power_full : hypotheses_of% pow_off_len := by
  exact ⟨1, 2, True.intro⟩
#verify_hypotheses offset_power_full for Solidity.Language.FixedPoint.pow_off_len
#print axioms offset_power_full

theorem parts_identity_full : hypotheses_of% parts_eq := by
  exact ⟨18, 7, 9, 256, 65536, True.intro⟩
#verify_hypotheses parts_identity_full for Solidity.Language.FixedPoint.parts_eq
#print axioms parts_identity_full

theorem parts_low_full : hypotheses_of% parts_mod := by
  exact ⟨18, 7, 9, 256, 65536, by decide, True.intro⟩
#verify_hypotheses parts_low_full for Solidity.Language.FixedPoint.parts_mod
#print axioms parts_low_full

theorem parts_shift_full : hypotheses_of% parts_div := by
  exact ⟨18, 7, 9, 256, 65536, by decide, True.intro⟩
#verify_hypotheses parts_shift_full for Solidity.Language.FixedPoint.parts_div
#print axioms parts_shift_full

theorem parts_high_full : hypotheses_of% parts_hi := by
  exact ⟨18, 7, 9, 256, 65536, by decide, by decide, True.intro⟩
#verify_hypotheses parts_high_full for Solidity.Language.FixedPoint.parts_hi
#print axioms parts_high_full

theorem write_parts_full : hypotheses_of% setField_parts := by
  exact ⟨1193046, 1, 1, 7, True.intro⟩
#verify_hypotheses write_parts_full for Solidity.Language.FixedPoint.setField_parts
#print axioms write_parts_full

theorem low_bound_full : hypotheses_of% low_lt := by
  exact ⟨1193046, 1, True.intro⟩
#verify_hypotheses low_bound_full for Solidity.Language.FixedPoint.low_lt
#print axioms low_bound_full

theorem value_bound_full : hypotheses_of% val_lt := by
  exact ⟨513, 1, True.intro⟩
#verify_hypotheses value_bound_full for Solidity.Language.FixedPoint.val_lt
#print axioms value_bound_full

theorem write_low_full : hypotheses_of% setField_low := by
  exact ⟨1193046, 1, 1, 7, True.intro⟩
#verify_hypotheses write_low_full for Solidity.Language.FixedPoint.setField_low
#print axioms write_low_full

theorem write_shift_full : hypotheses_of% setField_div := by
  exact ⟨1193046, 1, 1, 7, True.intro⟩
#verify_hypotheses write_shift_full for Solidity.Language.FixedPoint.setField_div
#print axioms write_shift_full

theorem write_high_full : hypotheses_of% setField_hi := by
  exact ⟨1193046, 1, 1, 7, True.intro⟩
#verify_hypotheses write_high_full for Solidity.Language.FixedPoint.setField_hi
#print axioms write_high_full

theorem read_write_full : hypotheses_of% field_setField := by
  exact ⟨1193046, 1, 1, 7, True.intro⟩
#verify_hypotheses read_write_full for Solidity.Language.FixedPoint.field_setField
#print axioms read_write_full

theorem field_modulo_full : hypotheses_of% field_eq_mod := by
  exact ⟨1193046, 1, 1, True.intro⟩
#verify_hypotheses field_modulo_full for Solidity.Language.FixedPoint.field_eq_mod
#print axioms field_modulo_full

theorem below_frame_full : hypotheses_of% field_setField_below := by
  exact ⟨1193046, 1, 1, 7, 0, 1, by decide, True.intro⟩
#verify_hypotheses below_frame_full for Solidity.Language.FixedPoint.field_setField_below
#print axioms below_frame_full

theorem above_frame_full : hypotheses_of% field_setField_above := by
  exact ⟨1193046, 1, 1, 7, 2, 1, by decide, True.intro⟩
#verify_hypotheses above_frame_full for Solidity.Language.FixedPoint.field_setField_above
#print axioms above_frame_full

theorem write_existing_full : hypotheses_of% setField_field := by
  exact ⟨1193046, 1, 1, True.intro⟩
#verify_hypotheses write_existing_full for Solidity.Language.FixedPoint.setField_field
#print axioms write_existing_full

theorem overwrite_full : hypotheses_of% setField_setField := by
  exact ⟨1193046, 1, 1, 7, 9, True.intro⟩
#verify_hypotheses overwrite_full for Solidity.Language.FixedPoint.setField_setField
#print axioms overwrite_full

theorem word_bound_full : hypotheses_of% setField_lt := by
  exact ⟨1193046, 1, 1, 7, by decide, by decide, True.intro⟩
#verify_hypotheses word_bound_full for Solidity.Language.FixedPoint.setField_lt
#print axioms word_bound_full

theorem storage_width_full : hypotheses_of% FxTy.storageBytes_bits := by
  exact ⟨signedTy, True.intro⟩
#verify_hypotheses storage_width_full for Solidity.Language.FixedPoint.FxTy.storageBytes_bits
#print axioms storage_width_full

theorem storage_bound_full : hypotheses_of% FxTy.storageBytes_le := by
  exact ⟨signedTy, True.intro⟩
#verify_hypotheses storage_bound_full for Solidity.Language.FixedPoint.FxTy.storageBytes_le
#print axioms storage_bound_full

theorem storage_positive_full : hypotheses_of% FxTy.storageBytes_pos := by
  exact ⟨signedTy, True.intro⟩
#verify_hypotheses storage_positive_full for Solidity.Language.FixedPoint.FxTy.storageBytes_pos
#print axioms storage_positive_full

theorem bits_nonnegative_full : hypotheses_of% Fx.toBits_nonneg := by
  exact ⟨signedTy, negativeSeven, True.intro⟩
#verify_hypotheses bits_nonnegative_full for Solidity.Language.FixedPoint.Fx.toBits_nonneg
#print axioms bits_nonnegative_full

theorem load_after_store_full : hypotheses_of% Fx.load_store := by
  exact ⟨signedTy, word, 3, by decide, negativeSeven, True.intro⟩
#verify_hypotheses load_after_store_full for Solidity.Language.FixedPoint.Fx.load_store
#print axioms load_after_store_full

theorem packed_frame_full : hypotheses_of% Fx.load_store_disjoint := by
  exact ⟨signedTy, smallTy, word, 2, 0, by decide, negativeSeven, (by decide), True.intro⟩
#verify_hypotheses packed_frame_full for Solidity.Language.FixedPoint.Fx.load_store_disjoint
#print axioms packed_frame_full

theorem byte_frame_full : hypotheses_of% Fx.field_store_disjoint := by
  exact ⟨signedTy, word, 2, 0, 1, by decide, negativeSeven, (by decide), True.intro⟩
#verify_hypotheses byte_frame_full for Solidity.Language.FixedPoint.Fx.field_store_disjoint
#print axioms byte_frame_full

theorem store_existing_full : hypotheses_of% Fx.store_load := by
  exact ⟨signedTy, word, 1, by decide, True.intro⟩
#verify_hypotheses store_existing_full for Solidity.Language.FixedPoint.Fx.store_load
#print axioms store_existing_full

theorem last_write_full : hypotheses_of% Fx.store_store := by
  exact ⟨signedTy, word, 1, by decide, negativeSeven, ⟨7, by decide⟩, True.intro⟩
#verify_hypotheses last_write_full for Solidity.Language.FixedPoint.Fx.store_store
#print axioms last_write_full

theorem zero_load_full : hypotheses_of% Fx.load_zero := by
  exact ⟨signedTy, 3, True.intro⟩
#verify_hypotheses zero_load_full for Solidity.Language.FixedPoint.Fx.load_zero
#print axioms zero_load_full

theorem key_injection_full : hypotheses_of% Fx.keyWord_injective := by
  exact ⟨signedTy, negativeSeven, negativeSeven, rfl, True.intro⟩
#verify_hypotheses key_injection_full for Solidity.Language.FixedPoint.Fx.keyWord_injective
#print axioms key_injection_full

theorem placement_after_full : hypotheses_of% place_after := by
  exact ⟨sizes, 2, 3, (2, 4, 2), by decide, True.intro⟩
#verify_hypotheses placement_after_full for Solidity.Language.FixedPoint.place_after
#print axioms placement_after_full

theorem placement_fit_full : hypotheses_of% place_fits := by
  exact ⟨sizes, 2, 3, sizes_fit, (2, 4, 2), by decide, True.intro⟩
#verify_hypotheses placement_fit_full for Solidity.Language.FixedPoint.place_fits
#print axioms placement_fit_full

theorem placement_pairwise_full : hypotheses_of% place_pairwise := by
  exact ⟨sizes, 2, 3, True.intro⟩
#verify_hypotheses placement_pairwise_full for Solidity.Language.FixedPoint.place_pairwise
#print axioms placement_pairwise_full

theorem apart_symmetry_full : hypotheses_of% Apart.symm := by
  exact ⟨(2, 3, 1), (2, 4, 2), (Or.inr (Or.inl (by decide))), True.intro⟩
#verify_hypotheses apart_symmetry_full for Solidity.Language.FixedPoint.Apart.symm
#print axioms apart_symmetry_full

theorem placement_sizes_full : hypotheses_of% place_sizes := by
  exact ⟨sizes, 2, 3, True.intro⟩
#verify_hypotheses placement_sizes_full for Solidity.Language.FixedPoint.place_sizes
#print axioms placement_sizes_full

theorem placement_length_full : hypotheses_of% place_length := by
  exact ⟨sizes, 2, 3, True.intro⟩
#verify_hypotheses placement_length_full for Solidity.Language.FixedPoint.place_length
#print axioms placement_length_full

theorem placement_apart_full : hypotheses_of% place_apart := by
  exact ⟨sizes, 2, 3, 0, 2, by decide, by decide, by decide, True.intro⟩
#verify_hypotheses placement_apart_full for Solidity.Language.FixedPoint.place_apart
#print axioms placement_apart_full

theorem layout_length_full : hypotheses_of% layout_length := by
  exact ⟨types, True.intro⟩
#verify_hypotheses layout_length_full for Solidity.Language.FixedPoint.layout_length
#print axioms layout_length_full

theorem layout_size_full : hypotheses_of% layout_size := by
  exact ⟨types, 1, by decide, True.intro⟩
#verify_hypotheses layout_size_full for Solidity.Language.FixedPoint.layout_size
#print axioms layout_size_full

theorem layout_fit_full : hypotheses_of% layout_fits := by
  exact ⟨types, 1, by decide, True.intro⟩
#verify_hypotheses layout_fit_full for Solidity.Language.FixedPoint.layout_fits
#print axioms layout_fit_full

theorem store_location_full : hypotheses_of% Fx.loadAt_storeAt := by
  exact ⟨signedTy, state, 2, 3, by decide, negativeSeven, True.intro⟩
#verify_hypotheses store_location_full for Solidity.Language.FixedPoint.Fx.loadAt_storeAt
#print axioms store_location_full

theorem store_apart_full : hypotheses_of% Fx.loadAt_storeAt_apart := by
  exact ⟨signedTy, smallTy, state, 2, 3, 2, 0, by decide, negativeSeven, (Or.inr (Or.inr (by decide))), True.intro⟩
#verify_hypotheses store_apart_full for Solidity.Language.FixedPoint.Fx.loadAt_storeAt_apart
#print axioms store_apart_full

theorem layout_frame_full : hypotheses_of% Fx.layout_frame := by
  exact ⟨types, state, 0, 1, by decide, by decide, by decide, seven, True.intro⟩
#verify_hypotheses layout_frame_full for Solidity.Language.FixedPoint.Fx.layout_frame
#print axioms layout_frame_full

theorem layout_read_write_full : hypotheses_of% Fx.layout_load_store := by
  exact ⟨types, state, 0, by decide, seven, True.intro⟩
#verify_hypotheses layout_read_write_full for Solidity.Language.FixedPoint.Fx.layout_load_store
#print axioms layout_read_write_full

/-- The witness layout contains neighbours in slot zero and a full-width rollover. -/
theorem layout_branches : layout types = [(0, 0, 1), (0, 1, 2), (1, 0, 32)] := by
  decide
#print axioms layout_branches
end Solidity.H62.AuditLanguage.FixedPointStorageWitness
