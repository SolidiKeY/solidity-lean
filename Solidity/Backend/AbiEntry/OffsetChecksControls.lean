import Solidity.Backend.AbiEntry.OffsetChecks

/-! Actual emitted predicate cases: signed relative offsets and wrapping
products are retained. A true predicate here is not full reference/entry
admission: length64, loads, outer guards and resources are separate. -/
namespace Solidity.Backend.AbiEntry.OffsetChecksControls
open Scalar
private def suffix : Stack := [258,513]
private def negative : Scalar.Word := BitVec.ofNat 256 (2^256-32)
private def high : Scalar.Word := BitVec.ofNat 256 (2^256-1)

theorem tail_edges :
    run OffsetChecks.tailCode (32::68::4::32::suffix)=some (1::suffix) ∧
    run OffsetChecks.tailCode (32::68::4::33::suffix)=some (0::suffix) := by decide

theorem signed_relative :
    run OffsetChecks.tailCode (32::68::4::negative::suffix)=some (1::suffix) ∧
    68<negative.toNat := by decide

theorem zero_extent :
    run OffsetChecks.tailCode (0::0::0::0::suffix)=some (1::suffix) ∧
    run OffsetChecks.tailCode (0::0::0::1::suffix)=some (0::suffix) := by decide

theorem region_edges :
    run OffsetChecks.regionCode (1::32::68::4::suffix)=some (1::suffix) ∧
    run OffsetChecks.regionCode (1::32::67::4::suffix)=some (0::suffix) := by decide

theorem wrapped_product :
    run OffsetChecks.regionCode (BitVec.ofNat 256 (2^255)::2::0::negative::suffix)=some (1::suffix) ∧
    (2^255 : Nat)*2=2^256 := by decide

theorem signed_not_unsigned :
    run OffsetChecks.regionCode (0::1::high::0::suffix)=some (0::suffix) ∧
    (32 : Nat)≤2^256-1 := by decide

private def lazyInput : Solidity.AbiEntry.Input :=
  {data := [0,0,0,0]++Solidity.AbiEntry.wordBytes (2^256-32)++List.replicate 32 0,free := 0}

/-- A real semantic reference accepts the wrapped negative relative offset;
this is not a claim about whole entry/Source/native composition. -/
theorem lazy_negative_reference :
    Solidity.AbiEntry.tailRef lazyInput (.array (.word (.uint 256))) 4 4=.ok (4,0) := by
  have computed :
      (Solidity.AbiEntry.tailRef lazyInput (.array (.word (.uint 256))) 4 4).toOption =
        some (4,0) := by decide
  generalize Solidity.AbiEntry.tailRef lazyInput (.array (.word (.uint 256))) 4 4 = result at computed ⊢
  cases result with
  | error e => cases computed
  | ok pair => exact congrArg Except.ok (Option.some.inj computed)

theorem height_boundaries : stackBound OffsetChecks.tailCode 1024=false ∧
    stackBound OffsetChecks.regionCode 1024=true := by decide

theorem inhabited_frames :
    (OffsetChecks.tailFrame 68 4 32 32).peak=1 ∧
    run (OffsetChecks.tailFrame 68 4 32 32).code (32::68::4::32::suffix)=some (1::suffix) ∧
    (OffsetChecks.regionFrame 68 4 1 32).peak=1 ∧
    run (OffsetChecks.regionFrame 68 4 1 32).code (1::32::68::4::suffix)=some (1::suffix) :=
  ⟨rfl,tail_edges.1,rfl,region_edges.1⟩

/-- info: 'Solidity.Backend.AbiEntry.OffsetChecksControls.tail_edges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tail_edges
/-- info: 'Solidity.Backend.AbiEntry.OffsetChecksControls.signed_relative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms signed_relative
/-- info: 'Solidity.Backend.AbiEntry.OffsetChecksControls.zero_extent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_extent
/-- info: 'Solidity.Backend.AbiEntry.OffsetChecksControls.region_edges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms region_edges
/-- info: 'Solidity.Backend.AbiEntry.OffsetChecksControls.wrapped_product' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrapped_product
/-- info: 'Solidity.Backend.AbiEntry.OffsetChecksControls.signed_not_unsigned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms signed_not_unsigned
/-- info: 'Solidity.Backend.AbiEntry.OffsetChecksControls.lazy_negative_reference' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms lazy_negative_reference
/-- info: 'Solidity.Backend.AbiEntry.OffsetChecksControls.height_boundaries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms height_boundaries
/-- info: 'Solidity.Backend.AbiEntry.OffsetChecksControls.inhabited_frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inhabited_frames
end Solidity.Backend.AbiEntry.OffsetChecksControls
