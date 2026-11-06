import Solidity.Backend.Passes.CapturedReadback
import Solidity.Backend.Passes.ShortCircuitWitness
import Solidity.Backend.Passes.ConditionalReferenceInput
import Solidity.Backend.Passes.RuntimeCaptureReflection
import Solidity.Backend.Passes.ReferenceControls

/-! Reached, inhabited clients of four context/failure packaging laws. All
observations are internal symbolic execution; no public ABI/resource claim. -/
namespace Solidity.Backend.Passes.QueueCompletionControls
open Evm Evm.Memory Evm.Compiler
open Controls.Fixture
open ReferenceControls (Γb fb state target input_repr)
def good : Val C Γb .bool := .simple (.local .here)
def gc : CompiledVal 0 fb good := ⟨_,.core _ rfl⟩
def update : Val C (.val .bool :: Γb) .bool := .simple (.bool false)
def uc : CompiledVal 0 (fb.push (.val .bool) .ok) update := ⟨_,.core _ rfl⟩
def after (a : Bool) (tail : List Word) : Machine :=
  writeMachine (writeMachine {(target a) with stack := tail} 5 (.val (bword a))) 4 w[0]

theorem joined (a : Bool) (tail : List Word) :
    run ((CapturedValueStability.compiled (.user "saved") good gc .here update uc).code ++ [.mload 5])
      {(target a) with stack := tail} = .ok ((after a tail).push (.val (bword a))) 0 := by
  obtain ⟨cw,uw,hc,hu,runs⟩ := CapturedValueStability.joined_readback
    (.user "saved") good gc .here update uc (input_repr a) (by decide) a false rfl rfl
  have cap : cw = .val (bword a) := hc
  have updated : uw = w[0] := hu
  subst cw
  subst uw
  exact runs tail

def cells : List Nat := [5,4,3,2,1,0,16,17,18,20,21]
theorem joined_observations (a : Bool) (tail : List Word) :
    (cells.map ((after a tail).push (.val (bword a))).mem,
      ((after a tail).push (.val (bword a))).stack) =
      ([.val (bword a),w[0],w[0],w[16],w[16],w[20],w[2],w[7],w[9],w[1],w[4]],
        .val (bword a) :: tail) := rfl

/-- Reading the changed old local cannot replace reading the captured local. -/
theorem wrong_readback : (after true []).mem 4 ≠ (after true []).mem 5 := by decide

def bad : Val C Γb .bool := .binop .eqB rfl rfl
  (.readMem (.index .dyn (.var (.there (.there (.there (.there .here)))) rfl) (.simple (.lit 1 rfl))))
  (.simple (.lit 0 rfl))
def bc : CompiledVal 0 fb bad := (compileVal 0 fb bad).get (by decide +kernel)
theorem bad_source (a : Bool) : bad.evalT (state a) = .error .revert := by
  cases a <;> with_unfolding_all rfl

theorem immediate_failure (skip a : Bool) (tail : List Word) :
    run (ShortCircuitBoundary.compiled skip bc gc).code {(target a) with stack := tail} = .revert ∧
    bad.evalT (state a) = .error .revert ∧ run bc.code {(target a) with stack := tail} = .revert := by
  have failed := (value_revert_iff bc (input_repr a) tail).mpr (bad_source a)
  exact ⟨(ShortCircuitBoundary.revert_witness_iff skip bc gc (input_repr a) tail).mpr
    (.inl ⟨bad_source a,failed⟩),bad_source a,failed⟩

theorem reached_failure (skip : Bool) (tail : List Word) :
    run (ShortCircuitBoundary.compiled skip gc bc).code {(target (!skip)) with stack := tail} = .revert ∧
    run gc.code {(target (!skip)) with stack := tail} =
      .ok ({(target (!skip)) with stack := tail}.push (.val (bword (!skip)))) 0 ∧
    StateRepr 1 0 6 fb (state (!skip)) base {(target (!skip)) with stack := tail} ∧
    run bc.code {(target (!skip)) with stack := tail} = .revert := by
  have needed : (!skip) ≠ skip := by cases skip <;> decide
  have left := (ShortCircuitBoundary.execution skip gc bc (input_repr (!skip)) (!skip) rfl tail).1
  have right := (value_revert_iff bc (input_repr (!skip)) tail).mpr (bad_source (!skip))
  exact ⟨(ShortCircuitBoundary.revert_witness_iff skip gc bc (input_repr (!skip)) tail).mpr
    (.inr ⟨!skip,rfl,needed,left,(input_repr (!skip)).stack tail,bad_source (!skip),right⟩),
      left,(input_repr (!skip)).stack tail,right⟩

theorem skipped_failure (skip : Bool) (tail : List Word) :
    run (ShortCircuitBoundary.compiled skip gc bc).code {(target skip) with stack := tail} =
      .ok ({(target skip) with stack := tail}.push (.val (bword skip))) 0 := by
  simpa only [if_pos rfl] using (ShortCircuitBoundary.execution skip gc bc (input_repr skip) skip rfl tail).2

abbrev A : RefTy := .array (.prim .uint)
abbrev dst : Idx Γb (.mem A) := .there (.there .here)
abbrev yes : Idx Γb (.mem A) := .there (.there (.there (.there .here)))
abbrev no : Idx Γb (.mem A) := .there (.there (.there .here))
def refStage := ConditionalReferenceCapture.compiled (.user "alias") good gc dst yes no rfl

theorem reference_input (a : Bool) : refStage.Input 1 6 base (state a) (target a) :=
  ConditionalReferenceCapture.input (.user "alias") good gc dst yes no rfl (input_repr a) (by decide)
def reference_execution (a : Bool) :=
  ConditionalReferenceCapture.execution (.user "alias") good gc dst yes no rfl
    (reference_input a) a rfl

theorem reference_frame_refused (a : Bool) : ¬ refStage.Input 1 5 base (state a) (target a) := by
  intro h
  have room := h.2.1
  change 6 ≤ 5 at room
  omega

theorem bad_capture_input (a : Bool) :
    (CapturedValueStability.captureStage (.user "bad") bad bc).Input 1 6 base (state a) (target a) :=
  ⟨input_repr a,by decide,Or.inl rfl⟩

theorem capture_failure (a : Bool) (tail : List Word) :
    run (CapturedValueStability.captureStage (.user "bad") bad bc).code (appendTail (target a) tail) = .revert :=
  (capture_stage_revert_iff (.user "bad") bad bc (bad_capture_input a) tail).mpr (bad_source a)

theorem capture_success_not_failure (a : Bool) (tail : List Word) :
    run (CapturedValueStability.captureStage (.user "good") good gc).code (appendTail (target a) tail) ≠ .revert := by
  have physical : (CapturedValueStability.captureStage (.user "good") good gc).Input 1 6 base (state a) (target a) :=
    ⟨input_repr a,by decide,Or.inl rfl⟩
  intro h
  have impossible := (capture_stage_revert_iff (.user "good") good gc physical tail).mp h
  cases impossible

end Solidity.Backend.Passes.QueueCompletionControls
