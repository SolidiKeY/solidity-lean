import Solidity.Backend.MemoryOps.CalldataViewPacking
import Solidity.Backend.MemoryOps.CalldataTransfer
import Solidity.Backend.MemoryOps.CalldataUintTransfer
import Solidity.Evm.Memory

/-! Inhabited structural packing clients. Payloads are typed supplied views;
these tests do not certify ABI decoding, entry admission or emitted code. -/
namespace Solidity.Backend.MemoryOps.ViewPackingControls
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
private def fixedView : CalldataView D :=
  ⟨.array .calldata .bool (some 3),rfl,0,3,
    .array 3 (fun _ h => by cases h;rfl) (fun i => .val (.bool ([true,false,true][i])))⟩
private def views : List (CalldataView D) :=
  [bv 0 [true,false,true],uv 0 [u1,u0,u1],bv 0 [true,false,true],
    bv 32 [false,true],uv 96 [umax,u0],bv 0 [true],fixedView]
private def input : List UInt8 :=
  (List.replicate 31 0++[1])++List.replicate 32 0++(List.replicate 31 0++[1])++
    List.replicate 32 255++List.replicate 32 0
theorem fixture_coherent : V11G34_ViewCoherence views := by
  constructor
  change ∀ i : Fin 7,∀ j : Fin 7,_
  simp only [Fin.forall_fin_succ]
  repeat' apply And.intro
  all_goals first
    | (intro i;exact Fin.elim0 i)
    | (intro ht ho hl
       simp only [views,List.getElem_cons_zero,List.getElem_cons_succ,Fin.val_zero,Fin.val_succ,List.length_cons,List.length_nil,bv,uv,fixedView] at ht ho hl ⊢
       first | rfl | omega | cases ht)
private def packed := (overlappingCalldataViews D).pack input views fixture_coherent

/-- Complete captured key order: heterogeneous same-address views and a
same-type shorter view remain distinct; an exact duplicate shares key0. -/
theorem packed_keys : List.ofFn packed.key=[0,1,0,3,4,5,6] := by
  rfl

/-- All seven supplied typed objects, actual raw references and bytes are
retained, including the high uint word, partial overlap and fixed view. -/
theorem packed_observations :
    packed.calldata.input=input ∧
    (∀ i : Fin views.length,packed.calldata.objects (packed.key i)=some ⟨views[i.val].type,views[i.val].contents⟩) ∧
    packed.rawReference ⟨0,by decide⟩=.cdRef rfl 0 3 ∧
    packed.rawReference ⟨1,by decide⟩=.cdRef rfl 0 3 ∧
    packed.rawReference ⟨3,by decide⟩=.cdRef rfl 32 2 ∧
    packed.rawReference ⟨4,by decide⟩=.cdRef rfl 96 2 ∧
    packed.rawReference ⟨5,by decide⟩=.cdRef rfl 0 1 ∧
    packed.rawReference ⟨6,by decide⟩=.cdRef rfl 0 3 ∧
    calldataBools packed.calldata 0=some [true,false,true] ∧
    calldataUints packed.calldata 1=some [u1,u0,u1] ∧
    calldataBools packed.calldata 3=some [false,true] ∧
    calldataUints packed.calldata 4=some [umax,u0] ∧
    calldataBools packed.calldata 5=some [true] ∧
    calldataBools packed.calldata 6=some [true,false,true] := by
  refine ⟨packed.input_exact,packed.lookup,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_,?_,?_,?_⟩
  all_goals rfl

/-- Physical raw offsets cannot serve as logical keys for these typed views. -/
theorem no_raw_offset_keys : ¬∃ p : V11G34_PackedViews input views,
    ∀ i,p.key i=views[i.val].rawOffset := by
  intro ⟨p,keys⟩
  have same : p.key ⟨0,by decide⟩=p.key ⟨1,by decide⟩ :=
    (keys ⟨0,by decide⟩).trans (keys ⟨1,by decide⟩).symm
  have impossible : views[0].type = views[1].type := ((p.aliases ⟨0,by decide⟩ ⟨1,by decide⟩).mp same).1
  cases impossible

/-- Changing one value of a repeated identity violates the required coherence;
no unconditional packing or favorable decoder payload is assumed. -/
theorem disagreement_not_coherent :
    ¬ V11G34_ViewCoherence [bv 0 [true,false,true],bv 0 [true,true,true]] := by
  intro h
  have equality : (bv 0 [true,false,true]).contents =
      (bv 0 [true,true,true]).contents := eq_of_heq (h.coherent ⟨0,by decide⟩ ⟨1,by decide⟩ rfl rfl rfl)
  have observed : calldataBoolPayload (bv 0 [true,false,true]).contents =
      calldataBoolPayload (bv 0 [true,true,true]).contents := congrArg calldataBoolPayload equality
  change (some [true,false,true] : Option (List Bool))=some [true,true,true] at observed
  cases observed

/-- Arbitrarily many repeated runtime views satisfy coherence without any
injectivity premise or view-count cutoff. -/
theorem repeated_coherent (v : CalldataView D) (n : Nat) :
    V11G34_ViewCoherence (List.replicate n v) := by
  constructor
  intro i j ht ho hl
  have contents (x y : CalldataView D) (h : x=y) : HEq x.contents y.contents := by
    cases h
    rfl
  exact (contents _ v (List.getElem_replicate i.isLt)).trans
    (contents _ v (List.getElem_replicate j.isLt)).symm

/-- The actual producer retains every repeated view at arbitrary runtime count. -/
theorem repeated_lookup (v : CalldataView D) (n : Nat) (bytes : List UInt8)
    (i : Fin (List.replicate n v).length) :
    let p := packCalldataViews bytes (List.replicate n v) (repeated_coherent v n)
    p.calldata.objects (p.key i)=some ⟨v.type,v.contents⟩ := by
  have h : (packCalldataViews bytes (List.replicate n v) (repeated_coherent v n)).calldata.objects
      ((packCalldataViews bytes (List.replicate n v) (repeated_coherent v n)).key i) =
      some ⟨(List.replicate n v)[i.val].type, (List.replicate n v)[i.val].contents⟩ :=
    (packCalldataViews bytes (List.replicate n v) (repeated_coherent v n)).lookup i
  have payload : (⟨(List.replicate n v)[i.val].type,
      (List.replicate n v)[i.val].contents⟩ : Sigma (Source.Data D)) = ⟨v.type,v.contents⟩ :=
    congrArg (fun w : CalldataView D =>
    (⟨w.type,w.contents⟩ : Sigma (Source.Data D))) (List.getElem_replicate i.isLt)
  exact h.trans (congrArg some payload)

/-- Literal empty view collection has no invented logical object at any key. -/
theorem empty_table (bytes : List UInt8) (key : Nat) :
    (packCalldataViews bytes [] (repeated_coherent (bv 0 []) 0)).calldata.objects key=none := by
  rfl

/-- info: 'Solidity.Backend.MemoryOps.ViewPackingControls.fixture_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fixture_coherent
/-- info: 'Solidity.Backend.MemoryOps.ViewPackingControls.packed_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms packed_keys
/-- info: 'Solidity.Backend.MemoryOps.ViewPackingControls.packed_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms packed_observations
/-- info: 'Solidity.Backend.MemoryOps.ViewPackingControls.no_raw_offset_keys' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms no_raw_offset_keys
/-- info: 'Solidity.Backend.MemoryOps.ViewPackingControls.disagreement_not_coherent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms disagreement_not_coherent
/-- info: 'Solidity.Backend.MemoryOps.ViewPackingControls.repeated_coherent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms repeated_coherent
/-- info: 'Solidity.Backend.MemoryOps.ViewPackingControls.repeated_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms repeated_lookup
/-- info: 'Solidity.Backend.MemoryOps.ViewPackingControls.empty_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms empty_table
end Solidity.Backend.MemoryOps.ViewPackingControls
