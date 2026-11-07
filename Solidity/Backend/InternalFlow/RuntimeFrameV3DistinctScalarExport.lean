import Solidity.Backend.InternalFlow.RuntimeFrameV3DistinctScalarControls
import Solidity.Backend.InternalFlow.RuntimeFrameResult

/-! A private scalar result is exported to a physically distinct retained
caller destination after actual different-reference parent restoration.
The full reached representation comes from the proved save/entry/unwind
client. This is not a recursive-call compiler or source-call history proof. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource CountdownWitness
namespace P
abbrev C := DistinctScalarUnwind.Controls.P.C
abbrev F := DistinctScalarUnwind.Controls.P.F
abbrev addresses := DistinctScalarUnwind.Controls.P.addresses
abbrev state := DistinctScalarUnwind.Controls.output
noncomputable abbrev machine := DistinctScalarUnwind.Controls.last
abbrev before := DistinctScalarUnwind.Controls.P.before
end P

def scope : Ext (Parameters A) (Frame A) := .push .refl
def destination : Idx (Parameters A) (.val .uint) := .here
def result : Idx (Frame A) (.val .uint) := .here
def code := Result.code 2 scope destination result
def output := (P.state.setLocal (destination.ext scope) (TEnv.get result P.state.env)).drop scope
noncomputable def after := writeMachine P.machine (cellOf 2 destination) (P.machine.mem (cellOf 2 result))
def completeCode := DistinctScalarUnwind.Controls.completeCode ++ code

theorem exported : run code P.machine=.ok after 0 ∧
 StateRepr 1 2 16 (P.F.restrict (Parameters A)) output P.addresses after :=
 Result.export_result DistinctScalarUnwind.Controls.endpoint scope destination result

theorem source_exit : output=(P.state.drop scope).setLocal destination (TEnv.get result P.state.env) :=
 Result.source_export scope destination result P.state

theorem completed : run completeCode P.before=.ok after 0 := by
 rw [completeCode,run_append_ok DistinctScalarUnwind.Controls.completed]
 exact exported.1

theorem exact_code : code=[.mload 4,.mstore 3] := rfl

theorem source_bindings :
 ((TEnv.get (.here : Idx (Parameters A) (.val .uint)) output.env).val,
  (TEnv.get (.there .here : Idx (Parameters A) (.mem A)) output.env).map HRef.id)=
 (8,some 1) := rfl

theorem result_word : P.machine.mem 4=w[8] :=
 DistinctScalarUnwind.Controls.specification.choose_spec.2.2.2.2.2.2.1

theorem reference_word : P.machine.mem 2=w[20] :=
 DistinctScalarUnwind.Controls.specification.choose_spec.2.2.2.2.1

theorem counter_before : P.machine.mem 3=w[2] :=
 DistinctScalarUnwind.Controls.specification.choose_spec.2.2.2.2.2.1

theorem exterior (address : Nat) (different : address≠3) : after.mem address=P.machine.mem address :=
 Result.outside P.machine 2 destination result address different

theorem words : (after.stack,after.mem 2,after.mem 3,after.mem 4,after.mem 8)=
 ([w[77]],w[20],w[8],w[8],w[10]) := by
 have stack : after.stack=[w[77]] := congrArg Prod.fst DistinctScalarUnwind.Controls.words
 have reference : after.mem 2=w[20] := (exterior 2 (by decide)).trans reference_word
 have written : after.mem 3=w[8] := (upd_same P.machine.mem 3 (P.machine.mem 4)).trans result_word
 have privateResult : after.mem 4=w[8] := (exterior 4 (by decide)).trans result_word
 have cursor : after.mem 8=w[10] := (exterior 8 (by decide)).trans
  DistinctScalarUnwind.Controls.specification.choose_spec.2.2.2.1
 exact Prod.ext stack (Prod.ext reference (Prod.ext written (Prod.ext privateResult cursor)))

theorem allocator : GrowsAllocator 2 16 0 P.state P.addresses P.machine output P.addresses after :=
 Result.allocator DistinctScalarUnwind.Controls.endpoint scope destination result

theorem not_noop : after≠P.machine := by
 intro wrong
 have equal := congrArg (fun m : Machine => m.mem 3) wrong
 have written : after.mem 3=w[8] := (upd_same P.machine.mem 3 (P.machine.mem 4)).trans result_word
 have impossible : w[8]=w[2] := written.symm.trans (equal.trans counter_before)
 have different : w[8]≠w[2] := by decide +kernel
 exact different impossible

theorem not_child_reference : after.mem 2≠w[16] := by
 have restored : after.mem 2=w[20] := (exterior 2 (by decide)).trans reference_word
 rw [restored]
 decide +kernel

theorem not_erased_private : after.mem 4≠w[0] := by
 have retained : after.mem 4=w[8] := (exterior 4 (by decide)).trans result_word
 rw [retained]
 decide +kernel

theorem not_revert : run completeCode P.before≠.revert := by
 rw [completed]
 intro wrong
 cases wrong

end Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.exported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.exported

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.source_exit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.source_exit

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.completed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.completed

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.exact_code' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.exact_code

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.source_bindings' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.source_bindings

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.result_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.result_word

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.reference_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.reference_word

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.counter_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.counter_before

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.exterior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.exterior

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.words

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.allocator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.allocator

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.not_noop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.not_noop

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.not_child_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.not_child_reference

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.not_erased_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.not_erased_private

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.not_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarExport.not_revert
