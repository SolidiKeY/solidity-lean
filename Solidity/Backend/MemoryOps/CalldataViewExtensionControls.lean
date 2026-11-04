import Solidity.Backend.MemoryOps.CalldataViewExtension
import Solidity.Backend.MemoryOps.CalldataTransfer
import Solidity.Backend.MemoryOps.CalldataUintTransfer
import Solidity.Evm.Memory

/-! Clients with genuinely noncanonical prior keys; structural view packing
only. No raw decoder or Source/native execution is claimed. -/
namespace Solidity.Backend.MemoryOps.ViewExtensionControls
open Solidity.Backend.AbiEntry.Premises
private def D : Source.Layout := ⟨fun _ => [],fun _ => 1,fun _ => .bool⟩
private def bv (off : Nat) (xs : List Bool) : CalldataView D :=
  ⟨.array .calldata .bool none,rfl,off,xs.length,
    .array xs.length (fun _ h => nomatch h) (fun i => .val (.bool xs[i]))⟩
private def uv (off : Nat) (xs : List PrimTy.uint.Denote) : CalldataView D :=
  ⟨.array .calldata (.int .u256) none,rfl,off,xs.length,
    .array xs.length (fun _ h => nomatch h) (fun i => .val (sourceUint xs[i]))⟩
private def u0 : PrimTy.uint.Denote := ⟨0,by decide⟩
private def u1 : PrimTy.uint.Denote := ⟨1,by decide⟩
private def umax : PrimTy.uint.Denote := Evm.Memory.indexValue Evm.wMax
private def oldViews : List (CalldataView D) :=
  [bv 0 [true,false,true],uv 0 [u1,u0,u1],bv 0 [true,false,true]]
private def added : List (CalldataView D) :=
  [bv 0 [true,false,true],bv 32 [false,true],uv 96 [umax,u0],bv 0 [true]]
private def bytes : List UInt8 := [1,0,1,255]

theorem full_coherent : V11G34_ViewCoherence (oldViews++added) := by
  constructor
  change ∀ i : Fin 7,∀ j : Fin 7,_
  simp only [Fin.forall_fin_succ]
  repeat' apply And.intro
  all_goals first
    | (intro i;exact Fin.elim0 i)
    | (intro ht ho hl
       simp only [oldViews,added,List.cons_append,List.nil_append,List.getElem_cons_zero,
         List.getElem_cons_succ,Fin.val_zero,Fin.val_succ,List.length_cons,List.length_nil,bv,uv]
         at ht ho hl ⊢
       first | rfl | omega | cases ht)

private theorem old_coherent : V11G34_ViewCoherence oldViews := by
  constructor
  change ∀ i : Fin 3,∀ j : Fin 3,_
  simp only [Fin.forall_fin_succ]
  repeat' apply And.intro
  all_goals first
    | (intro i;exact Fin.elim0 i)
    | (intro ht ho hl
       simp only [oldViews,List.getElem_cons_zero,List.getElem_cons_succ,
         Fin.val_zero,Fin.val_succ,bv,uv] at ht ho hl ⊢
       first | rfl | cases ht)

private theorem shifted_aliases (offset : Nat) (i j : Fin oldViews.length) :
    offset+calldataViewKey oldViews i=offset+calldataViewKey oldViews j ↔
    calldataViewIdentity oldViews[i.val]=calldataViewIdentity oldViews[j.val] := by
  rw [Nat.add_left_cancel_iff]
  exact (calldataViewKey_aliases oldViews i j).trans (calldataViewIdentity_eq _ _).symm

private def prior (offset : Nat) : V11G34_PackedViews bytes oldViews :=
  { calldata := keyedCalldataViews bytes oldViews (fun i => offset+calldataViewKey oldViews i)
    key := fun i => offset+calldataViewKey oldViews i
    rawReference := fun i => .cdRef oldViews[i.val].location oldViews[i.val].rawOffset oldViews[i.val].rawLength
    input_exact := rfl
    raw_exact := fun _ => rfl
    lookup := keyedCalldataViews_lookup bytes oldViews _ (shifted_aliases offset) old_coherent
    aliases := fun i j => (shifted_aliases offset i j).trans (calldataViewIdentity_eq _ _) }
private def extension (offset : Nat) :=
  (overlappingCalldataViewsV2 D).extend bytes oldViews added (prior offset) full_coherent

/-- Runtime-sized sparse prior keys retain their identities after real packing. -/
theorem runtime_prefix (offset : Nat) (i : Fin oldViews.length)
    (j : Fin (oldViews++added).length) (same : i.val=j.val) :
    (prior offset).key i=(extension offset).grown.key j := by
  exact (extension offset).prefix_keys i j same

/-- Full ordered old/new keys discriminate canonical repacking from extension. -/
theorem sparse_keys : List.ofFn (prior 100).key=[100,101,100] ∧
    List.ofFn (extension 100).grown.key=[100,101,100,100,106,107,108] := by
  exact ⟨rfl,rfl⟩

/-- All captured typed objects and bytes remain actual lookups, including the
old repeated alias and the newly materialized heterogeneous overlapping views. -/
theorem sparse_observations :
    (prior 100).calldata.input=bytes ∧ (extension 100).grown.calldata.input=bytes ∧
    (∀ i : Fin (oldViews++added).length,
      (extension 100).grown.calldata.objects ((extension 100).grown.key i)=
        some ⟨(oldViews++added)[i.val].type,(oldViews++added)[i.val].contents⟩) ∧
    calldataBools (prior 100).calldata 100=some [true,false,true] ∧
    calldataUints (prior 100).calldata 101=some [u1,u0,u1] ∧
    calldataBools (extension 100).grown.calldata 100=some [true,false,true] ∧
    calldataUints (extension 100).grown.calldata 101=some [u1,u0,u1] ∧
    calldataBools (extension 100).grown.calldata 106=some [false,true] ∧
    calldataUints (extension 100).grown.calldata 107=some [umax,u0] ∧
    calldataBools (extension 100).grown.calldata 108=some [true] ∧
    (extension 100).grown.rawReference ⟨4,by decide⟩=.cdRef rfl 32 2 ∧
    (extension 100).grown.rawReference ⟨5,by decide⟩=.cdRef rfl 96 2 := by
  refine ⟨rfl,rfl,(extension 100).grown.lookup,?_,?_,?_,?_,?_,?_,?_,rfl,rfl⟩
  all_goals rfl

/-- A canonical repack is valid V1 but violates the required existing key. -/
theorem repack_not_prefix :
    (prior 100).key ⟨0,by decide⟩≠calldataViewKey (oldViews++added) ⟨0,by decide⟩ := by
  decide

/-- Empty append is an actual extension retaining all captured payloads/keys. -/
theorem empty_extension :
    let e := extendCalldataViews bytes oldViews [] (prior 100)
      (by simpa only [List.append_nil] using old_coherent)
    List.ofFn e.grown.key=[100,101,100] ∧
    calldataBools e.grown.calldata 100=some [true,false,true] ∧
    calldataUints e.grown.calldata 101=some [u1,u0,u1] := by
  exact ⟨rfl,rfl,rfl⟩

/-- An actually empty prior table extends to nonempty repeated typed views;
its unused key zero remains absent while new identities are materialized. -/
theorem empty_prior :
    let p := packCalldataViews bytes [] (by constructor;intro i;exact Fin.elim0 i)
    let e := extendCalldataViews bytes [] oldViews p old_coherent
    List.ofFn e.grown.key=[1,2,1] ∧
    calldataBools e.grown.calldata 1=some [true,false,true] ∧
    calldataUints e.grown.calldata 2=some [u1,u0,u1] ∧
    e.grown.calldata.objects 0=none := by
  first | rfl | exact ⟨rfl,rfl,rfl,rfl⟩ | decide

/-- info: 'Solidity.Backend.MemoryOps.ViewExtensionControls.full_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms full_coherent
/-- info: 'Solidity.Backend.MemoryOps.ViewExtensionControls.runtime_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms runtime_prefix
/-- info: 'Solidity.Backend.MemoryOps.ViewExtensionControls.sparse_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sparse_keys
/-- info: 'Solidity.Backend.MemoryOps.ViewExtensionControls.sparse_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sparse_observations
/-- info: 'Solidity.Backend.MemoryOps.ViewExtensionControls.repack_not_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms repack_not_prefix
/-- info: 'Solidity.Backend.MemoryOps.ViewExtensionControls.empty_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms empty_extension
/-- info: 'Solidity.Backend.MemoryOps.ViewExtensionControls.empty_prior' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms empty_prior
end Solidity.Backend.MemoryOps.ViewExtensionControls
