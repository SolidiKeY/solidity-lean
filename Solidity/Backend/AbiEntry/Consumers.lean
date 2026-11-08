import Solidity.Backend.AbiEntry.RejectionInterface
import Solidity.Backend.CalldataPackets.RawUint.Execution
import Solidity.Backend.AbiEntry.CompositionInterface
import Solidity.Backend.AbiEntry.EntryTransport
import Solidity.Backend.AbiEntry.EntryComposition

/-! Actual inhabitants of the narrow, previously committed helper interfaces.
These reuse the V13 proofs, not an assumed runner or decoder success. Rejection
is conditional emitter execution; composition is semantic entry recursion.
Neither is a certificate for emitted calldata decoding or complete entry.
Typed uint-array views below reuse the raw reader and V11 packer. The mixed
view regression keeps same-byte dynamic/fixed references distinct, preserves
duplicate identities, checks unequal decoded words and preserves an older
destination prefix during transfer; entry guards and
compiler/native execution remain separate obligations. Lazy uint traversal
below retains typed byte-derived contents and exact fuel failures, separately
from entry span guards. Array containers retain the extra constructor fuel
step, including empty-container failure at zero fuel. -/
namespace Solidity.Backend.AbiEntry.Consumers

def rejection : Interface.RejectionConsumer EntryTransport.rejection where
  selected := EntryTransport.rejection_iff
  checked := EntryTransport.entry_revert_exec

def orderedEntry : Interface.EntryCompositionCertificate EntryComposition.appendEntries where
  head_extent := EntryComposition.heads_append
  ordered := EntryComposition.enter_append

/-- info: 'Solidity.Backend.AbiEntry.Consumers.rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rejection
/-- info: 'Solidity.Backend.AbiEntry.Consumers.orderedEntry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms orderedEntry
namespace UIntViews
open Solidity.Backend.MemoryOps
open Solidity.Backend.CalldataPackets.RawUint (payload_length wordValue)

abbrev rawPayload (frame : Source.Fr) (offset count : Nat) : List PrimTy.uint.Denote :=
  Solidity.Backend.CalldataPackets.RawUint.payload frame offset count

/-- A view demand indexed by the existing Source array size. The consistency
field is the existing Data.array invariant, not ABI input admission. -/
structure Demand where
  staticLength : Option Nat
  offset : Nat
  count : Nat
  consistent : ∀ n, staticLength=some n → n=count

def Demand.dynamic (offset count : Nat) : Demand :=
  ⟨none,offset,count,fun _ h => nomatch h⟩

def Demand.fixed (offset count : Nat) : Demand :=
  ⟨some count,offset,count,fun _ h => (Option.some.inj h).symm⟩

private theorem Demand.identity (a b : Demand)
    (types : (Source.STy.array .calldata (.int .u256) a.staticLength)=
      .array .calldata (.int .u256) b.staticLength)
    (offsets : a.offset=b.offset) (counts : a.count=b.count) : a=b := by
  have sizes : a.staticLength=b.staticLength := (Source.STy.array.inj types).2.2
  cases a
  cases b
  cases sizes
  cases offsets
  cases counts
  rfl

/-- Both array kinds retain the actual raw offset/count and decode every word
from the frame, including unaligned offsets and standalone zero padding. -/
def view {D : Source.Layout} (F : Source.Fr) (d : Demand) : Premises.CalldataView D :=
  { type := .array .calldata (.int .u256) d.staticLength
    location := rfl
    rawOffset := d.offset
    rawLength := d.count
    contents := .array (rawPayload F d.offset d.count).length
      (fun n h => (d.consistent n h).trans (payload_length F d.offset d.count).symm)
      (fun i => .val (sourceUint ((rawPayload F d.offset d.count)[i]))) }

def views {D : Source.Layout} (F : Source.Fr) (demands : List Demand) :
    List (Premises.CalldataView D) := demands.map (view F)

/-- Mixed dynamic/static families are coherent by raw identity, with no
supplied decoded payload, successful run or canonical-layout restriction. -/
theorem coherent {D : Source.Layout} (F : Source.Fr) (demands : List Demand) :
    Premises.V11G34_ViewCoherence (views (D := D) F demands) := by
  constructor
  intro i j types offsets counts
  have hi : i.val<demands.length := by simpa only [views,List.length_map] using i.isLt
  have hj : j.val<demands.length := by simpa only [views,List.length_map] using j.isLt
  have vi : (views (D := D) F demands)[i.val]=view F demands[i.val] := by
    simp only [views,List.getElem_map]
  have vj : (views (D := D) F demands)[j.val]=view F demands[j.val] := by
    simp only [views,List.getElem_map]
  rw [vi,vj] at types offsets counts ⊢
  have same : demands[i.val]=demands[j.val] := Demand.identity _ _ types offsets counts
  rw [same]

/-- Concrete construction using the already-published structural producer. -/
def packed {D : Source.Layout} (F : Source.Fr) (demands : List Demand) :
    Premises.V11G34_PackedViews F.cd (views (D := D) F demands) :=
  packCalldataViews F.cd (views F demands) (coherent F demands)

set_option backward.isDefEq.respectTransparency false in
/-- The same existing table reader obtains byte-derived uints for every fixed
or dynamic capture. This is not a Source-reference/logical-key transport law. -/
theorem uints {D : Source.Layout} (F : Source.Fr) (demands : List Demand)
    (i : Fin demands.length) :
    calldataUints (packed (D := D) F demands).calldata
      ((packed (D := D) F demands).key
        ⟨i.val,by simpa only [views,List.length_map] using i.isLt⟩)=
      some (rawPayload F demands[i.val].offset demands[i.val].count) := by
  unfold calldataUints
  rw [(packed (D := D) F demands).lookup
    ⟨i.val,by simpa only [views,List.length_map] using i.isLt⟩]
  simp only [views]
  rw [List.getElem_map]
  change some (List.ofFn (fun j : Fin (rawPayload F demands[i.val].offset demands[i.val].count).length =>
    calldataUint (Source.Data.val (sourceUint (D := D)
      (rawPayload F demands[i.val].offset demands[i.val].count)[j]))))=_
  rw [calldataUint_values]

set_option backward.isDefEq.respectTransparency false in
/-- Existing checked intrinsic transfer consumes either typed shape with only
its original source-slice and destination bounds. No desired execution is given. -/
theorem transfer {D : Source.Layout} {H : HTy} {R : RefTy}
    (F : Source.Fr) (demands : List Demand) (i : Fin demands.length)
    (hp : Heap H) (dst : HRef H R) (a : ArrTy R (.prim .uint))
    (start stop offset : Nat) (bounds : SliceBounds demands[i.val].count start stop)
    (fits : offset+(stop-start)≤hp.len dst a) :
    checkedCalldataUints (packed (D := D) F demands).calldata
      ((packed (D := D) F demands).key
        ⟨i.val,by simpa only [views,List.length_map] using i.isLt⟩)
      hp dst a start stop offset=
      some (overwriteSlice hp dst a offset
        (((rawPayload F demands[i.val].offset demands[i.val].count).drop start).take (stop-start))
        (by rw [(show SliceBounds (rawPayload F demands[i.val].offset demands[i.val].count).length start stop from
          by simpa only [rawPayload,payload_length] using bounds).length];exact fits)) := by
  unfold checkedCalldataUints
  rw [uints]
  simp only [Bind.bind,Option.bind,rawPayload,payload_length,
    dite_eq_left (show start≤stop ∧ stop≤demands[i.val].count from ⟨bounds.ordered,bounds.bounded⟩),dite_eq_left fits]

private def sampleEnv : Source.Env := ⟨[]⟩
private def sampleFrame : Source.Fr :=
  { this := ⟨1,by decide⟩, sender := ⟨2,by decide⟩, value := ⟨0,by decide⟩,
    static := false, contract := "UIntViews",
    cd := [171]++Source.natBytes 32 7++Source.natBytes 32 42 }
private def sampleDemands : List Demand :=
  [Demand.dynamic 1 2,Demand.fixed 1 2,Demand.dynamic 1 2,
   Demand.fixed 33 1,Demand.fixed 1 1]

/-- Regression: dynamic/fixed types at identical bytes remain distinct while
repeated dynamic views alias; overlapping fixed views retain distinct offsets. -/
theorem mixed_aliases :
    let p := packed (D := sampleEnv.layout) sampleFrame sampleDemands
    p.key ⟨0,by decide⟩=p.key ⟨2,by decide⟩ ∧
    p.key ⟨0,by decide⟩≠p.key ⟨1,by decide⟩ ∧
    p.key ⟨3,by decide⟩≠p.key ⟨4,by decide⟩ := by decide

private theorem sample_values : rawPayload sampleFrame 1 2=[wordValue 7,wordValue 42] := by decide

/-- Both positive-width shapes expose the two unequal words after a prefix. -/
theorem mixed_values :
    let p := packed (D := sampleEnv.layout) sampleFrame sampleDemands
    calldataUints p.calldata (p.key ⟨0,by decide⟩)=some [wordValue 7,wordValue 42] ∧
    calldataUints p.calldata (p.key ⟨1,by decide⟩)=some [wordValue 7,wordValue 42] := by
  dsimp only
  constructor
  · rw [uints sampleFrame sampleDemands ⟨0,by decide⟩]
    exact congrArg some sample_values
  · rw [uints sampleFrame sampleDemands ⟨1,by decide⟩]
    exact congrArg some sample_values

private abbrev TargetTy : RefTy := .array (.prim .uint)
private def targetRoot : HRef [TargetTy] TargetTy := ⟨0,rfl⟩
private def targetHeap : Heap [TargetTy] :=
  (⟨[wordValue 99,wordValue 98,wordValue 97],by decide⟩,())
set_option backward.isDefEq.respectTransparency false in
private theorem target_length : targetHeap.len targetRoot .dyn=3 := by
  simp only [Heap.len,Heap.get,Objs.get,targetRoot,targetHeap,MObj.elems_dyn]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The fixed view copies actual bytes while the older prefix word stays 99. -/
theorem mixed_transfer :
    let p := packed (D := sampleEnv.layout) sampleFrame sampleDemands
    (checkedCalldataUints p.calldata (p.key ⟨1,by decide⟩)
      targetHeap targetRoot .dyn 0 2 1).map (fun out => MObj.elems .dyn (out.get targetRoot))=
      some [wordValue 99,wordValue 7,wordValue 42] := by
  dsimp only
  rw [transfer sampleFrame sampleDemands ⟨1,by decide⟩ targetHeap targetRoot .dyn
    0 2 1 ⟨by decide,by decide⟩ (by rw [target_length];decide)]
  simp only [sampleDemands,List.getElem_cons_zero,List.getElem_cons_succ,Demand.fixed,
    sample_values,Option.map_some,overwriteSlice_elems]
  simp only [Heap.get,Objs.get,targetHeap,targetRoot,MObj.elems_dyn,replaceSlice]
  rfl

/-- info: 'Solidity.Backend.AbiEntry.Consumers.UIntViews.coherent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms coherent
/-- info: 'Solidity.Backend.AbiEntry.Consumers.UIntViews.uints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms uints
/-- info: 'Solidity.Backend.AbiEntry.Consumers.UIntViews.transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transfer
/-- info: 'Solidity.Backend.AbiEntry.Consumers.UIntViews.mixed_aliases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mixed_aliases
/-- info: 'Solidity.Backend.AbiEntry.Consumers.UIntViews.mixed_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mixed_values
/-- info: 'Solidity.Backend.AbiEntry.Consumers.UIntViews.mixed_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mixed_transfer
/-- Typed sequence observation using an index-generalising recursor. -/
def sequenceElements {shape : Solidity.AbiEntry.Shape} {length : Nat}
    (values : Solidity.AbiEntry.Seq shape length) : List (Solidity.AbiEntry.Val shape) :=
  Solidity.AbiEntry.Seq.casesOn
    (motive_2 := fun shape _ _ => List (Solidity.AbiEntry.Val shape)) values
    (fun {_} => [])
    (fun {_ _} value rest => value :: sequenceElements rest)
termination_by structural values

private theorem sequenceElements_nil (shape : Solidity.AbiEntry.Shape) :
    sequenceElements (@Solidity.AbiEntry.Seq.nil shape)=[] := rfl

private theorem sequenceElements_cons {shape : Solidity.AbiEntry.Shape} {length : Nat}
    (value : Solidity.AbiEntry.Val shape) (rest : Solidity.AbiEntry.Seq shape length) :
    sequenceElements (.cons value rest)=value::sequenceElements rest := rfl

private def semanticUintWord (input : Solidity.AbiEntry.Input) (address : Nat) :
    Solidity.AbiEntry.Word (.uint 256) where
  val := Solidity.AbiEntry.load input.data address
  lt := Solidity.AbiEntry.load_lt _ _
  valid := by
    change decide (Solidity.AbiEntry.load input.data address<2^256)=true
    apply decide_eq_true_eq.mpr
    rw [←Solidity.AbiEntry.W_eq]
    exact Solidity.AbiEntry.load_lt _ _

/-- Exact word contents at the semantic traversal's wrapped addresses. -/
def semanticUintValues (input : Solidity.AbiEntry.Input) (base index count : Nat) :
    List (Solidity.AbiEntry.Val (.word (.uint 256))) :=
  (List.range' index count).map fun i => .word
    (semanticUintWord input (Solidity.AbiEntry.wrap (base+i*32)))

private theorem semantic_uint_word (input : Solidity.AbiEntry.Input)
    (fuel address length : Nat) :
    Solidity.AbiEntry.cval input (fuel+1) (.word (.uint 256)) address length=
      .ok (.word (semanticUintWord input address)) := by
  simp only [Solidity.AbiEntry.cval]
  split
  · rfl
  · rename_i bad
    exact False.elim (bad (semanticUintWord input address).valid)

private theorem semantic_uint_element (input : Solidity.AbiEntry.Input)
    (fuel base address : Nat) :
    Solidity.AbiEntry.celem input (fuel+2) (.word (.uint 256)) base address=
      .ok (.word (semanticUintWord input address)) := by
  change Solidity.AbiEntry.cval input (fuel+1) (.word (.uint 256)) address 0=_
  exact semantic_uint_word input fuel address 0

/-- Standalone lazy uint traversal derives all typed contents from bytes and
retains the exact fuel failure. Entry span/offset checks are separate; no
canonical-layout, buffer-bound or successful-run premise is introduced. -/
theorem semantic_uint_sequence (input : Solidity.AbiEntry.Input)
    (base index count : Nat) :
    ∃ values : Solidity.AbiEntry.Seq (.word (.uint 256)) count,
      sequenceElements values=semanticUintValues input base index count ∧
      ∀ fuel, Solidity.AbiEntry.cseq input fuel (.word (.uint 256)) base index count=
        if count=0 ∨ count+2≤fuel then .ok values else .error .fuel := by
  induction count generalizing index with
  | zero =>
    refine ⟨.nil,?_,?_⟩
    · rfl
    · intro fuel
      rw [ite_eq_left (Or.inl rfl)]
      cases fuel <;> rfl
  | succ count ih =>
    obtain ⟨tail,contents,execution⟩ := ih (index+1)
    refine ⟨.cons (.word (semanticUintWord input
      (Solidity.AbiEntry.wrap (base+index*32)))) tail,?_,?_⟩
    · rw [sequenceElements_cons,contents]
      simp only [semanticUintValues,List.range'_succ,List.map_cons]
    · intro fuel
      cases fuel with
      | zero =>
        have short : ¬(count+1=0 ∨ count+1+2≤0) := by omega
        rw [ite_eq_right short]
        rfl
      | succ fuel =>
        cases fuel with
        | zero =>
          have short : ¬(count+1=0 ∨ count+1+2≤1) := by omega
          rw [ite_eq_right short]
          rfl
        | succ fuel =>
          cases fuel with
          | zero =>
            have short : ¬(count+1=0 ∨ count+1+2≤2) := by omega
            rw [ite_eq_right short]
            rfl
          | succ fuel =>
            rw [Solidity.AbiEntry.cseq,semantic_uint_element,execution]
            by_cases enough : count=0 ∨ count+2≤fuel+2
            · have enough' : count+1=0 ∨ count+1+2≤fuel+3 := by omega
              simp only [ite_eq_left enough,ite_eq_left enough',Solidity.AbiEntry.Shape.headSize]
            · have short : ¬(count+1=0 ∨ count+1+2≤fuel+3) := by omega
              rw [ite_eq_right enough,ite_eq_right short]


/-- Both array containers reuse the byte-derived sequence and preserve their
extra constructor fuel step. The fixed container ignores the supplied runtime
length exactly as cval does; no entry guard or compiler result is assumed. -/
theorem semantic_uint_containers (input : Solidity.AbiEntry.Input)
    (base count : Nat) :
    ∃ values : Solidity.AbiEntry.Seq (.word (.uint 256)) count,
      sequenceElements values=semanticUintValues input base 0 count ∧
      ∀ fuel length,
        Solidity.AbiEntry.cval input fuel (.array (.word (.uint 256))) base count=
          (if 0<fuel ∧ (count=0 ∨ count+3≤fuel) then
            .ok (.array values) else .error .fuel) ∧
        Solidity.AbiEntry.cval input fuel (.fixed (.word (.uint 256)) count) base length=
          (if 0<fuel ∧ (count=0 ∨ count+3≤fuel) then
            .ok (.fixed values) else .error .fuel) := by
  obtain ⟨values,contents,execution⟩ := semantic_uint_sequence input base 0 count
  refine ⟨values,contents,?_⟩
  intro fuel length
  cases fuel with
  | zero => exact ⟨rfl,rfl⟩
  | succ fuel =>
    by_cases enough : count=0 ∨ count+2≤fuel
    · have full : 0<fuel+1 ∧ (count=0 ∨ count+3≤fuel+1) := by omega
      constructor <;> simp only [Solidity.AbiEntry.cval,execution,ite_eq_left enough,ite_eq_left full]
    · have short : ¬(0<fuel+1 ∧ (count=0 ∨ count+3≤fuel+1)) := by omega
      constructor <;> simp only [Solidity.AbiEntry.cval,execution,ite_eq_right enough,ite_eq_right short]

/-- Regression: empty container fuel zero fails, whereas fuel one succeeds;
the fixed container's arbitrary runtime length remains ignored. -/
theorem semantic_uint_container_empty (input : Solidity.AbiEntry.Input)
    (base length : Nat) :
    Solidity.AbiEntry.cval input 0 (.array (.word (.uint 256))) base 0=.error .fuel ∧
    Solidity.AbiEntry.cval input 1 (.array (.word (.uint 256))) base 0=.ok (.array .nil) ∧
    Solidity.AbiEntry.cval input 1 (.fixed (.word (.uint 256)) 0) base length=
      .ok (.fixed .nil) := ⟨rfl,rfl,rfl⟩

/-- Regression: one actual raw-derived element is refused at fuel three and
accepted at four, in both container forms, without a supplied decoded value. -/
theorem semantic_uint_container_boundary (input : Solidity.AbiEntry.Input)
    (base length : Nat) :
    ∃ values : Solidity.AbiEntry.Seq (.word (.uint 256)) 1,
      Solidity.AbiEntry.cval input 3 (.array (.word (.uint 256))) base 1=.error .fuel ∧
      Solidity.AbiEntry.cval input 4 (.array (.word (.uint 256))) base 1=.ok (.array values) ∧
      Solidity.AbiEntry.cval input 4 (.fixed (.word (.uint 256)) 1) base length=
        .ok (.fixed values) := by
  obtain ⟨values,_,execution⟩ := semantic_uint_containers input base 1
  have short : ¬(0<3 ∧ (1=0 ∨ 1+3≤3)) := by decide
  have enough : 0<4 ∧ (1=0 ∨ 1+3≤4) := by decide
  refine ⟨values,?_,?_,?_⟩
  · simpa only [ite_eq_right short] using (execution 3 length).1
  · simpa only [ite_eq_left enough] using (execution 4 length).1
  · simpa only [ite_eq_left enough] using (execution 4 length).2

/-- info: 'Solidity.Backend.AbiEntry.Consumers.UIntViews.semantic_uint_containers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms semantic_uint_containers
/-- info: 'Solidity.Backend.AbiEntry.Consumers.UIntViews.semantic_uint_container_empty' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms semantic_uint_container_empty
/-- info: 'Solidity.Backend.AbiEntry.Consumers.UIntViews.semantic_uint_container_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms semantic_uint_container_boundary

/-- Empty standalone sequences succeed even at zero fuel; no entry admission
or empty-calldata head check is inferred from this observation. -/
theorem semantic_uint_empty (input : Solidity.AbiEntry.Input)
    (base index fuel : Nat) :
    (Solidity.AbiEntry.cseq input fuel (.word (.uint 256)) base index 0).map
      sequenceElements=.ok [] := by
  obtain ⟨values,contents,execution⟩ := semantic_uint_sequence input base index 0
  rw [execution,ite_eq_left (Or.inl rfl)]
  change Except.ok (sequenceElements values)=_
  rw [contents]
  rfl

/-- Insufficient fuel remains a fuel failure, rather than an empty-data
revert or a successful zero-padded traversal. -/
theorem semantic_uint_fuel (input : Solidity.AbiEntry.Input)
    (base index count fuel : Nat) (nonempty : 0<count) (short : fuel<count+2) :
    Solidity.AbiEntry.cseq input fuel (.word (.uint 256)) base index count=
      .error .fuel := by
  obtain ⟨values,contents,execution⟩ := semantic_uint_sequence input base index count
  have insufficient : ¬(count=0 ∨ count+2≤fuel) := by omega
  rw [execution,ite_eq_right insufficient]

/-- Regression: an unaligned read after a nonempty prefix observes unequal
words 7 and 42. This is standalone traversal, not ABI entry admission. -/
theorem semantic_uint_unequal :
    (Solidity.AbiEntry.cseq ⟨sampleFrame.cd,0⟩ 4 (.word (.uint 256)) 1 0 2).map
      sequenceElements=.ok [.word ⟨7,by decide,by decide⟩,.word ⟨42,by decide,by decide⟩] := by
  obtain ⟨values,contents,execution⟩ := semantic_uint_sequence ⟨sampleFrame.cd,0⟩ 1 0 2
  rw [execution,ite_eq_left (Or.inr (by decide))]
  change Except.ok (sequenceElements values)=_
  rw [contents]
  rfl

/-- Regression: empty input still supplies zero-padded words to standalone
reads at every starting address and index; entry span checks are separate. -/
theorem semantic_uint_zero_padding (free base index : Nat) :
    (Solidity.AbiEntry.cseq ⟨[],free⟩ 4 (.word (.uint 256)) base index 2).map
      sequenceElements=.ok [.word ⟨0,by decide,by decide⟩,.word ⟨0,by decide,by decide⟩] := by
  obtain ⟨values,contents,execution⟩ := semantic_uint_sequence ⟨[],free⟩ base index 2
  rw [execution,ite_eq_left (Or.inr (by decide))]
  change Except.ok (sequenceElements values)=_
  rw [contents]
  simp only [semanticUintValues,List.range'_succ,List.range'_zero,List.map_cons,List.map_nil,
    semanticUintWord,Solidity.AbiEntry.load,Solidity.AbiEntry.byteAt,List.getElem?_nil,Option.getD_none]
  rfl

/-- info: 'Solidity.Backend.AbiEntry.Consumers.UIntViews.sequenceElements' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms sequenceElements
/-- info: 'Solidity.Backend.AbiEntry.Consumers.UIntViews.semantic_uint_sequence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms semantic_uint_sequence
/-- info: 'Solidity.Backend.AbiEntry.Consumers.UIntViews.semantic_uint_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms semantic_uint_empty
/-- info: 'Solidity.Backend.AbiEntry.Consumers.UIntViews.semantic_uint_fuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms semantic_uint_fuel
/-- info: 'Solidity.Backend.AbiEntry.Consumers.UIntViews.semantic_uint_unequal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms semantic_uint_unequal
/-- info: 'Solidity.Backend.AbiEntry.Consumers.UIntViews.semantic_uint_zero_padding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms semantic_uint_zero_padding
end UIntViews

end Solidity.Backend.AbiEntry.Consumers
