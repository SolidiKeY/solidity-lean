import SolidityBridge.RoadmapV15.WordByteTransport
import SolidityBridge.RoadmapV15.CumulativeTransport

/-! Inhabited boundary and negative consumer controls, not external EVM tests. -/
namespace SolidityBridge.RoadmapV15.ConsumerControls
open Solidity Solidity.Backend Solidity.Roadmap Backend.Failure.Local

example : (toBytesBE 0 99).toList = [] := rfl
example : (Scalar.immediate []).toNat = 0 := rfl
example : Failure.digits 2 258 = (toBytesBE 2 258).toList := digits_toBytesBE 2 258
example : (toBytesBE 2 258).toList = [1, 2] := by decide +kernel
example : (toBytesBE 2 258).toList ≠ [2, 1] := by decide +kernel
example : (Scalar.immediate [1, 2]).toNat = 258 := by decide +kernel
example : Keccak.ofBytes ([1, 2].map UInt8.toNat) = ofBytesBE [1, 2] := keccak_ofBytesBE _
example : (Scalar.immediate (toBytesBE 1 255).toList).toNat = 255 :=
  bounded_immediate 1 255 (by decide) (by decide)
example : (Scalar.immediate (toBytesBE 1 256).toList).toNat = 0 := by decide +kernel
example : (Scalar.immediate (toBytesBE 1 256).toList).toNat ≠ 256 := by decide +kernel
-- Truncated-PUSH right padding is a different byte string, not this reader's job.
example : ofBytesBE [1] ≠ ofBytesBE [1, 0] := by decide +kernel
example : (toBytesBE 32 (2 ^ 256 - 1)).toList.length = 32 := Vector.length_toList
private def maximumWord : Scalar.Word := BitVec.ofNat 256 (2 ^ 256 - 1)
example : maximumWord.toNat = 2 ^ 256 - 1 := by decide +kernel
example : Failure.Slice.pushed (toBytesBE 32 maximumWord.toNat).toList =
    maximumWord.toFin := word32_pushed maximumWord

private def negativeOne : PrimTy.int.Denote := ⟨-1, by decide⟩
private def minimumSigned : PrimTy.int.Denote := ⟨-((2 ^ 255 : Nat) : Int), by decide +kernel⟩
private def maximumSigned : PrimTy.int.Denote := ⟨((2 ^ 255 : Nat) : Int) - 1, by decide +kernel⟩
example : (Scalar.immediate
    (toBytesBE 32 (Scalar.encodeValue .int negativeOne).toNat).toList).toInt = -1 :=
  signed_word_bytes negativeOne
example : (Scalar.immediate
    (toBytesBE 32 (Scalar.encodeValue .int minimumSigned).toNat).toList).toInt = -((2 ^ 255 : Nat) : Int) :=
  signed_word_bytes minimumSigned
example : (Scalar.immediate
    (toBytesBE 32 (Scalar.encodeValue .int maximumSigned).toNat).toList).toInt = ((2 ^ 255 : Nat) : Int) - 1 :=
  signed_word_bytes maximumSigned
example : (Scalar.encodeValue .int negativeOne).toNat ≠ 0 := by decide +kernel

example : Scalar.run (Scalar.unsignedCode ⟨0, by decide⟩)
    (Scalar.immediate (toBytesBE 32 (257 : Scalar.Word).toNat).toList :: [77]) = some [1, 77] := by
  have h := unsigned_cleanup_bytes ⟨0, by decide⟩ 257 [77]
  rw [word32_immediate, word32_immediate] at h
  have hc : Scalar.unsignedClean ⟨0, by decide⟩ 257 = 1 := by decide +kernel
  rw [hc] at h
  simpa only [word32_immediate] using h
example : Scalar.run (Scalar.signedCode ⟨0, by decide⟩)
    (Scalar.immediate (toBytesBE 32 (128 : Scalar.Word).toNat).toList :: [77]) =
      some [BitVec.ofInt 256 (-128), 77] := by
  have h := signed_cleanup_bytes ⟨0, by decide⟩ 128 [77]
  rw [word32_immediate, word32_immediate] at h
  have hc : Scalar.signedClean ⟨0, by decide⟩ 128 = BitVec.ofInt 256 (-128) := by decide +kernel
  rw [hc] at h
  simpa only [word32_immediate] using h
example : (Scalar.signedClean ⟨0, by decide⟩ 127).toInt = 127 := by decide +kernel
example : (Scalar.signedClean ⟨0, by decide⟩ 128).toInt = -128 := by decide +kernel
example : (Scalar.signedClean ⟨0, by decide⟩ 255).toInt = -1 := by decide +kernel
example : Scalar.signedClean ⟨0, by decide⟩ 128 ≠ Scalar.unsignedClean ⟨0, by decide⟩ 128 := by decide +kernel

example : Failure.Slice.getBytes
    (Failure.Slice.putBytes (Failure.Slice.putBytes (fun _ => 77) 5 (Failure.digits 2 258)) 7 [99])
      5 2 = [1, 2] := written_immediate_suffix _ 5 2 258 [99]
example : Failure.Slice.getBytes
    (Failure.Slice.putBytes (fun _ => 77) 5 [1, 2]) 6 2 ≠ [1, 2] := by decide +kernel

private def fixed : Fixed where
  evm := Evm.withKeccak
  ledger := fun bal _ a => bal a
  regionLen := 1
  rootSlots := 0
example : fixed.Sane := ⟨by decide, by decide, by decide⟩
private theorem singleton_guard : HashPremise fixed [[1, 255]] [[1, 255]] := by
  constructor
  · exact Hash.CollisionFree.singleton _
  · constructor
    · intro x hx y hy hne
      exact False.elim (hne ((List.mem_singleton.mp hx).trans (List.mem_singleton.mp hy).symm))
    · intro x hx r hr
      change r ∈ ([] : List Nat) at hr
      cases hr

-- Both sides are inhabited and nonempty; repeated preimages require no cross
-- injectivity hypothesis and distinct-region clauses are vacuous only for repeats.
example : HashPremise fixed ([[1, 255]] ++ [[1, 255]]) ([[1, 255]] ++ [[1, 255]]) := by
  apply (hashPremise_append_iff fixed _ _ _ _).mpr
  refine ⟨singleton_guard, singleton_guard, ?_, ?_⟩
  · intro x hx y hy _
    exact (List.mem_singleton.mp hx).trans (List.mem_singleton.mp hy).symm
  · intro x hx y hy hne
    exact False.elim (hne ((List.mem_singleton.mp hx).trans (List.mem_singleton.mp hy).symm))

-- Collision-free hashes alone do not imply disjoint regions of positive length.
example : Hash.CollisionFree (fun x : Nat => x) [4, 5] := by
  intro x _ y _ h; exact h
example : Hash.RegionsDisjoint 16 2 (fun x : Nat => x) [0] [4] := by decide
example : Hash.RegionsDisjoint 16 2 (fun x : Nat => x) [0] [5] := by decide
example : ¬ Hash.RegionsDisjoint 16 2 (fun x : Nat => x) [0] ([4] ++ [5]) := by decide
example : ¬ Hash.CollisionFree (fun _ : Nat => 0) ([4] ++ [5]) := by
  intro h
  have bad : (4 : Nat) = 5 := h 4 (by decide) 5 (by decide) rfl
  cases bad

private def journal (p t : Nat) : Journal Nat Nat := ⟨p, t, ⟨[], fun _ => 0⟩⟩
private def pairedJournal (p hidden t : Nat) : Journal (Nat × Nat) Nat :=
  ⟨(p, hidden), t, ⟨[], fun _ => 255⟩⟩
example (innerOutcome outerOutcome : Outcome) :
    (finish (save (journal 7 3)) outerOutcome
      (finish (save (journal 9 4)) innerOutcome (journal 99 8))).persistent =
    (finish (save (pairedJournal 7 100 3)) outerOutcome
      (finish (save (pairedJournal 9 200 4)) innerOutcome (pairedJournal 99 300 8))).persistent.1 :=
  checkpoint_relation_nested (fun a b => a.persistent = b.persistent.1)
    (save (journal 7 3)) (save (pairedJournal 7 100 3))
    (save (journal 9 4)) (save (pairedJournal 9 200 4))
    (journal 99 8) (pairedJournal 99 300 8) innerOutcome outerOutcome rfl rfl rfl
example : (finish (save (journal 7 3)) (.revert [1, 255]) (journal 99 8)).persistent ≠
    (finish (save (journal 6 3)) (.revert [1, 255]) (journal 99 8)).persistent := by decide

example : (toBytesBE 32 (Scalar.encodeValue .int negativeOne).toNat).toList =
    (toBytesBE 32 (PrimTy.toWord negativeOne).val.toNat).toList :=
  typed_bytes_toWord .int negativeOne
example (a b : Scalar.Word)
    (h : (toBytesBE 32 a.toNat).toList = (toBytesBE 32 b.toNat).toList) : a = b :=
  word32_bytes_injective a b h
example : HashPremise fixed ([[1, 255]] ++ []) ([[1, 255]] ++ []) ↔
    HashPremise fixed ([] ++ [[1, 255]]) ([] ++ [[1, 255]]) :=
  hashPremise_append_comm fixed _ _ _ _

private def maximumUint : PrimTy.uint.Denote :=
  ⟨((2 ^ 256 - 1 : Nat) : Int), by decide +kernel⟩
example : (Scalar.immediate
    (toBytesBE 32 (Scalar.encodeValue .uint maximumUint).toNat).toList).toNat =
      maximumUint.val.toNat := unsigned_word_bytes maximumUint
example : maximumUint.val ≠ 0 := by decide +kernel

-- Test-only Fixed family, NOT asserted equal to the approved Keccak instance.
-- It inhabits the precise generic HashPremise shape without cryptographic work.
private def regionFixture (second : Nat) (hsecond : second < 2 ^ 256) : Fixed where
  evm := { Evm.withKeccak with
    keccak := fun bs => if bs = [1] then 4 else second
    keccak_lt := fun _ => by split <;> first | decide | exact hsecond }
  ledger := fun bal _ a => bal a
  regionLen := 2
  rootSlots := 1
private def separated : Fixed := regionFixture 8 (by decide)
private def overlapping : Fixed := regionFixture 5 (by decide)
example : separated.Sane := ⟨by decide, by decide, by decide⟩

private theorem separated_guard :
    HashPremise separated ([[1]] ++ [[2]]) ([[1]] ++ [[2]]) := by
  apply (hashPremise_append_iff separated [[1]] [[2]] [[1]] [[2]]).mpr
  constructor
  · unfold HashPremise Hash.CollisionFree Hash.RegionsDisjoint
    decide +kernel
  · constructor
    · unfold HashPremise Hash.CollisionFree Hash.RegionsDisjoint
      decide +kernel
    · constructor <;> decide +kernel

-- Both segments and their distinct preimages are nonempty; byte order changes.
example : HashPremise separated ([[2]] ++ [[1]]) ([[2]] ++ [[1]]) :=
  (hashPremise_append_comm separated [[1]] [[2]] [[1]] [[2]]).mp separated_guard

example : HashPremise overlapping [[1]] [[1]] := by
  unfold HashPremise Hash.CollisionFree Hash.RegionsDisjoint
  decide +kernel
example : HashPremise overlapping [[2]] [[2]] := by
  unfold HashPremise Hash.CollisionFree Hash.RegionsDisjoint
  decide +kernel
-- Local component premises hold and hashes differ, but the exact cross-region
-- obligation from append_iff fails. This cannot be repaired by rollback.
example : ¬ HashPremise overlapping ([[1]] ++ [[2]]) ([[1]] ++ [[2]]) := by
  intro h
  have cross := (hashPremise_append_iff overlapping [[1]] [[2]] [[1]] [[2]]).mp h
  have noOverlap := cross.2.2.2 [1] (by decide) [2] (by decide) (by decide)
  exact noOverlap (by decide)

#print axioms typed_bytes_toWord
#print axioms word32_bytes_injective
#print axioms digits_toBytesBE
#print axioms readImmediate_ofBytesBE
#print axioms keccak_ofBytesBE
#print axioms encoded_bytes_injective
#print axioms pushed_immediate_toNat
#print axioms word32_immediate
#print axioms word32_pushed
#print axioms bounded_immediate
#print axioms signed_word_bytes
#print axioms unsigned_word_bytes
#print axioms unsigned_cleanup_bytes
#print axioms signed_cleanup_bytes
#print axioms written_immediate_bytes
#print axioms written_immediate_suffix
#print axioms hashPremise_append_iff
#print axioms hashPremise_append_comm
#print axioms checkpoint_relation_nested
end SolidityBridge.RoadmapV15.ConsumerControls
