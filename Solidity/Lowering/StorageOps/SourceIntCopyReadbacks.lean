import Solidity.Lowering.StorageOps.SourceCopyReadbacks
import Solidity.Backend.Scalar.Typed

/-! Integer Source copy readbacks and a typed signed-value observation adapter.
PUBLIC Scalar encodings/ranges are reused read-only; no arithmetic, codec,
value/state layer or compiler implementation is introduced. -/
namespace Solidity.Backend.StorageOps.SourceIntCopyReadbacks
open SourceStorageCopy SourceCopyReadbacks SourceArrayDeleteTarget

def int256 : Source.IntTy := ⟨true,256,by decide⟩

theorem signed_bounds (v : PrimTy.int.Denote) : int256.lo≤v.val ∧ v.val≤int256.hi := by
 have bounds := Scalar.int_range v
 change -((2^255:Nat):Int)≤v.val ∧ v.val≤((2^255-1:Nat):Int)
 omega

def sourceValue {D : Source.Layout} (v : PrimTy.int.Denote) : Source.Val D (.int int256) := .int v.val (signed_bounds v)

/-- Existing independent Source and existing PUBLIC scalar ABI observations
agree on EVERY intrinsically bounded signed value, including negatives. -/
theorem word_agrees {D : Source.Layout} (v : PrimTy.int.Denote) :
 (sourceValue (D:=D) v).word.map Fin.val=some (TargetOperations.encodeWord (PrimTy.toWord v)).val := by
 have bit : (Scalar.encodeValue .int v).toNat=(v.val % ((2^256:Nat):Int)).toNat := by
  simp only [Scalar.encodeValue,BitVec.toNat_ofInt,Int.natCast_pow]
 have abi := congrArg BitVec.toNat (Scalar.encodeValue_toWord .int v)
 change (Scalar.encodeValue .int v).toNat=(Scalar.encodeValue .uint (PrimTy.toWord v)).toNat at abi
 have equal := abi.trans (Scalar.encode_uint_toNat (PrimTy.toWord v))
 change some (((v.val % ((2^256:Nat):Int)).toNat) % 2^256)=some _
 rw [← bit,Nat.mod_eq_of_lt (Scalar.encodeValue .int v).isLt,equal]
 rfl

/-- ACTUAL declared integer default remains zero at every supported IntTy. -/
theorem clear_word_zero {E : Source.Env} (frame : Source.Fr) (t : Source.IntTy)
 (state : Source.ExecState E.layout E.lay E.lay) (query : Source.SPath)
 (ordinary : E.transientRoot query=false) (typed : E.cellTy query=.int t) :
 wordAt frame (state.apply (SourceScalarDeleteLog.clearOp E frame query)) query=some 0 := by
 unfold wordAt SourceScalarDeleteLog.clearOp
 simp only [ordinary,Bool.false_eq_true,if_false,Source.ExecState.apply,Source.World.set_get,Source.Storage.read,Source.Storage.set,dif_pos]
 change ((Source.Val.default E.layout (E.cellTy query)).bind Source.Val.word).map Fin.val=some 0
 rw [typed]
 rfl

theorem clear_words_index {E : Source.Env} (frame : Source.Fr) (t : Source.IntTy)
 (state : Source.ExecState E.layout E.lay E.lay) (path : Source.SPath) (indices : List Nat) (j : Nat)
 (ordinary : E.transientRoot (path.go (.index j))=false) (typed : E.cellTy (path.go (.index j))=.int t) :
 wordAt frame (state.run (indices.map (fun i => SourceScalarDeleteLog.clearOp E frame (path.go (.index i))))) (path.go (.index j))=
 if j ∈ indices then some 0 else wordAt frame state (path.go (.index j)) := by
 induction indices generalizing state with
 | nil => rfl
 | cons i indices ih =>
  simp only [List.map_cons,Source.ExecState.run]
  rw [ih]
  by_cases same : j=i
  · subst i
    rw [clear_word_zero frame t state _ ordinary typed]
    simp only [List.mem_cons,true_or,if_true,ite_self]
  · rw [SourceArrayDeleteTarget.clear_word_other frame state _ _ (index_ne_index path same)]
    simp only [List.mem_cons,same,false_or]

/-- Exact copied/stale-live/older-shadow Source outcomes. The default scalar
clear remains the published Source default, with ordinary storage explicit. -/
theorem copy_data {E : Source.Env} (frame : Source.Fr) (t : Source.IntTy) (dst : Source.SPath)
 (count oldLength j : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (typed : E.pathTy dst=some (.array .storage (.int t) none))
 (state : Source.ExecState E.layout E.lay E.lay) (ordinary : E.transientRoot dst=false) :
 wordAt frame (state.run (copyLog frame t dst count oldLength payload typed)) (dst.go (.index j))=
 if j<count then (payload j).word.map Fin.val else if j<oldLength then some 0 else wordAt frame state (dst.go (.index j)) := by
 have childOrdinary : E.transientRoot (dst.go (.index j))=false := ordinary
 unfold copyLog
 rw [Source.run_append,Source.run_append]
 change wordAt frame ((state.run _).run _ |>.apply _) (dst.go (.index j))=_
 rw [cell_word_other frame _ dst _ _ (index_ne_header dst j)]
 rw [clear_words_index frame t _ dst _ j childOrdinary (element_type t dst typed j)]
 rw [writes_word frame t dst payload _ 0 count j state childOrdinary]
 have membership : j ∈ List.range' count (oldLength-count) ↔ count≤j ∧ j<oldLength := by
  rw [List.mem_range']
  constructor
  · rintro ⟨i,inside,same⟩
    simp only [Nat.one_mul] at same
    omega
  · rintro ⟨lower,upper⟩
    refine ⟨j-count,by omega,?_⟩
    simp only [Nat.one_mul]
    omega
 by_cases copied : j<count
 · rw [if_pos copied,if_neg (by intro yes; have bound:count≤j := (membership.mp yes).1; omega),if_pos (by omega : 0≤j ∧ j<0+count)]
 · rw [if_neg copied,if_neg (by omega : ¬ (0≤j ∧ j<0+count))]
   by_cases stale : j<oldLength
   · rw [if_pos stale,if_pos (membership.mpr ⟨by omega,stale⟩)]
   · rw [if_neg stale,if_neg (by intro yes; exact stale (membership.mp yes).2)]

/-- info: 'Solidity.Backend.StorageOps.SourceIntCopyReadbacks.signed_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms signed_bounds
/-- info: 'Solidity.Backend.StorageOps.SourceIntCopyReadbacks.word_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms word_agrees
/-- info: 'Solidity.Backend.StorageOps.SourceIntCopyReadbacks.clear_word_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms clear_word_zero
/-- info: 'Solidity.Backend.StorageOps.SourceIntCopyReadbacks.clear_words_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms clear_words_index
/-- info: 'Solidity.Backend.StorageOps.SourceIntCopyReadbacks.copy_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms copy_data
end Solidity.Backend.StorageOps.SourceIntCopyReadbacks
