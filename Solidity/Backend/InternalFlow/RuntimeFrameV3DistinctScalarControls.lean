import Solidity.Backend.InternalFlow.RuntimeFrameV3DistinctScalarUnwind
import Solidity.Backend.InternalFlow.RuntimeFrameV3DistinctParentControls

/-! Actual saved parent reference20/counter2, child reference16/result7, then
checked source and target increment to8. The saved counter is deliberately
independent of the live result. This is a local return-control slice, not a
recursive-call compiler or source-history certificate. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarUnwind.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource CountdownWitness
namespace P
abbrev parent := DistinctParentRestore.Controls.parent
abbrev child := DistinctParentRestore.Controls.child
abbrev before := DistinctParentRestore.Controls.before
noncomputable abbrev after := DistinctParentRestore.Controls.after
abbrev F := DistinctParentRestore.Controls.F
abbrev addresses := CountdownWitness.P.base
abbrev C := CountdownWitness.P.C
end P

def restored := (P.child.setLocal (.there (.there .here)) (some CompileExamples.r1)).setLocal
 (.there .here) (countValue 2 (by decide))
def output := finished restored 8 (by decide)
def code := ScalarUnwind.code (C:=P.C) 2 8 P.F
def completeCode := DistinctParentRestore.Controls.captureCode ++
 DistinctParentRestore.Controls.entryCode ++ code

theorem source_advance : increment.run restored=.ok ⟨output,List.prefix_refl _⟩ :=
 increment_run restored 7 (by decide) rfl

theorem specification : ∃ last,
 run code P.after=.ok last 0 ∧ StateRepr 1 2 16 P.F output P.addresses last ∧
 last.stack=P.after.stack ∧ last.mem 8=w[10] ∧ last.mem 2=w[20] ∧ last.mem 3=w[2] ∧
 last.mem 4=w[8] ∧ GrowsAllocator 2 16 0 P.child P.addresses P.after output P.addresses last ∧
 (∀ x, x≠8 → x≠2 → x≠3 → x≠4 → last.mem x=P.after.mem x) :=
 step P.child P.addresses P.after DistinctParentRestore.Controls.after_repr 2 (by decide) CompileExamples.r1
  7 (by decide) rfl 5 8 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  DistinctParentRestore.Controls.payload.2.2 DistinctParentRestore.Controls.payload.1 DistinctParentRestore.Controls.payload.2.1

noncomputable def last := specification.choose

theorem completed : run completeCode P.before=.ok last 0 := by
 have prepared : run (DistinctParentRestore.Controls.captureCode ++ DistinctParentRestore.Controls.entryCode) P.before=
   .ok P.after 0 := by
  rw [run_append_ok DistinctParentRestore.Controls.capture_run]
  exact DistinctParentRestore.Controls.entry_run
 rw [completeCode,run_append_ok prepared]
 exact specification.choose_spec.1

theorem endpoint : StateRepr 1 2 16 P.F output P.addresses last := specification.choose_spec.2.1

theorem words : (last.stack,last.mem 2,last.mem 3,last.mem 4,last.mem 8)=
 ([w[77]],w[20],w[2],w[8],w[10]) := by
 unfold last
 have s := specification.choose_spec
 have stack : P.after.stack=[w[77]] := DistinctParentRestore.Controls.capture_spec.2.1.stack
 refine Prod.ext (s.2.2.1.trans stack) ?_
 refine Prod.ext s.2.2.2.2.1 ?_
 refine Prod.ext s.2.2.2.2.2.1 ?_
 exact Prod.ext s.2.2.2.2.2.2.1 s.2.2.2.1

theorem source_bindings :
 ((TEnv.get (.here : Idx (Frame A) (.val .uint)) output.env).val,
  (TEnv.get (.there .here : Idx (Frame A) (.val .uint)) output.env).val,
  (TEnv.get (.there (.there .here) : Idx (Frame A) (.mem A)) output.env).map HRef.id)=
 (8,2,some 1) := rfl

theorem not_child_reference : last.mem 2≠w[16] := by
 have reference : last.mem 2=w[20] := specification.choose_spec.2.2.2.2.1
 rw [reference]
 decide +kernel

theorem not_old_result : last.mem 4≠w[7] := by
 have result : last.mem 4=w[8] := specification.choose_spec.2.2.2.2.2.2.1
 rw [result]
 decide +kernel

theorem not_result_counter : last.mem 3≠w[8] := by
 have counter : last.mem 3=w[2] := specification.choose_spec.2.2.2.2.2.1
 rw [counter]
 decide +kernel

theorem not_revert : run completeCode P.before≠.revert := by
 rw [completed]
 intro wrong
 cases wrong

end Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarUnwind.Controls

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarUnwind.Controls.source_advance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarUnwind.Controls.source_advance

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarUnwind.Controls.specification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarUnwind.Controls.specification

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarUnwind.Controls.completed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarUnwind.Controls.completed

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarUnwind.Controls.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarUnwind.Controls.endpoint

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarUnwind.Controls.words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarUnwind.Controls.words

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarUnwind.Controls.source_bindings' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarUnwind.Controls.source_bindings

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarUnwind.Controls.not_child_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarUnwind.Controls.not_child_reference

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarUnwind.Controls.not_old_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarUnwind.Controls.not_old_result

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarUnwind.Controls.not_result_counter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarUnwind.Controls.not_result_counter

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarUnwind.Controls.not_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctScalarUnwind.Controls.not_revert
