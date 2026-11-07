import Solidity.Lowering.Readonly.SourceDispatchInterfaceV2
import Solidity.Lowering.Readonly.SourceAllHistoriesV2
import Solidity.Lowering.Readonly.SourceDispatchControls

/-! Each V2 dispatch constructor has an actual selector witness. The two frozen
V1 empty-selected premises have no witness; their theorems remain unchanged. -/
namespace Solidity.Lowering.Readonly.SourceDispatchV2.Controls
open Solidity.Source Solidity.Source.SemanticsExamples Solidity.Source.Examples
open Solidity.Roadmap

def global := SourceDispatchControls.global
def cbDecl : Decl := ⟨.function, "cb", some "C", false, fn "cb" .nil .nil⟩
theorem function_selected : global.pickFn FC SourceDispatchControls.cb = some cbDecl := rfl
def function_witness : Selection global FC SourceDispatchControls.cb :=
  .function cbDecl function_selected (by decide)

def getterEnv : Env := counter.env
def getterProgram : Program getterEnv where
  body _ := none
  consts _ := none
  inits _ := []
  ctor _ := none
  ctorLocals _ := []
  baseArgs _ := []
  contracts := ["Counter"]
def getterGlobal : Glob getterEnv :=
  ⟨getterProgram, .legacy, toyFixed, fun _ => word 0, fun _ _ => false,
    fun _ => .answer (.success []), word 0⟩
def getterFrame : Fr := {F0 with contract := "Counter"}
def getterInput := getterGlobal.selector "count()".toList
def getterDecl : Decl :=
  ⟨.stateVar, "count", some "Counter", false,
    .stateVar u256 (some .pub) none none false "count" .none⟩
theorem getter_no_function : getterGlobal.pickFn getterFrame getterInput = none := by rfl
theorem getter_selected : getterGlobal.pickGetter getterFrame getterInput =
    some (getterDecl, [], uint) := by rfl
def getter_witness : Selection getterGlobal getterFrame getterInput :=
  .getter getterDecl [] uint getter_no_function getter_selected

def empty_witness : Selection global FC [] :=
  .special (pickFn_empty _ _) (pickGetter_empty _ _)
def unknown_witness : Selection (G0 .viaIR) F0 [0,0,0,0] :=
  .special rfl rfl

theorem empty_function_impossible (G : Glob E) (F : Fr) (d : Decl) :
    G.pickFn F [] ≠ some d := by
  rw [pickFn_empty]
  exact Option.noConfusion

theorem empty_getter_impossible (G : Glob E) (F : Fr) (d : Decl)
    (ps : List STy) (r : STy) : G.pickGetter F [] ≠ some (d,ps,r) := by
  rw [pickGetter_empty]
  exact Option.noConfusion

theorem migrated_at_zero : SourceHistory.Effect FC.static
    (dispatch global FC 1 SourceDispatchControls.cb) :=
  dispatch_succ global FC 0 (SourceHistory.at_zero global) SourceDispatchControls.cb

theorem empty_result : (SourceDispatchControls.run true []).1 = .error (.revert []) := rfl
theorem callback_write_refused : (SourceDispatchControls.run true SourceDispatchControls.cb).1 =
    .error (.revert []) := rfl
theorem horizon_zero : (SourceDispatchControls.run true SourceDispatchControls.cb 0).1 =
    .error .timeout := rfl
theorem migrated_all_callbacks :
    EnvironmentHistory.CallbackHistories global true 3 := all_callbacks global true 3

theorem migrated_all_at : SourceHistory.At global 3 := all_at global 3

/-! Joint satisfiability: every hypothesis of each V1 branch lemma that V2
routes through holds together, at one global, frame, input and bound. -/

theorem function_jointly_satisfiable : ∃ (G : Glob EB) (F : Fr) (input : Bytes) (n : Nat) (d : Decl),
    SourceHistory.At G n ∧ G.pickFn F input = some d ∧ input.isEmpty = false :=
  ⟨global, FC, SourceDispatchControls.cb, 3, cbDecl, all_at global 3, function_selected, rfl⟩

theorem getter_jointly_satisfiable : ∃ (G : Glob getterEnv) (F : Fr) (input : Bytes) (n : Nat)
    (d : Decl) (ps : List STy) (r : STy),
    SourceHistory.At G n ∧ G.pickFn F input = none ∧ G.pickGetter F input = some (d, ps, r) :=
  ⟨getterGlobal, getterFrame, getterInput, 3, getterDecl, [], uint, all_at getterGlobal 3,
    getter_no_function, getter_selected⟩

theorem special_jointly_satisfiable : ∃ (G : Glob EB) (F : Fr) (input : Bytes) (n : Nat),
    SourceHistory.At G n ∧ G.pickFn F input = none ∧ G.pickGetter F input = none :=
  ⟨global, FC, [], 3, all_at global 3, pickFn_empty _ _, pickGetter_empty _ _⟩

/-! Negative controls: the two frozen V1 empty-selected lemmas have
unsatisfiable premises for every environment, global, frame and input. -/

theorem v1_getter_empty_vacuous {E : Env} (G : Glob E) (F : Fr) (input : Bytes) (fd : Decl)
    (present : G.pickFn F input = some fd) (empty : input.isEmpty = true) : False := by
  have nonempty := selected_nonempty G F input fd present
  rw [empty] at nonempty
  cases nonempty

theorem v1_special_empty_vacuous {E : Env} (G : Glob E) (F : Fr) (input : Bytes) (fd : Decl)
    (present : G.pickFn F input = some fd) (empty : input.isEmpty = true) : False :=
  v1_getter_empty_vacuous G F input fd present empty

end Solidity.Lowering.Readonly.SourceDispatchV2.Controls

/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.selector_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.selector_length
/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.selector_ne_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.selector_ne_empty
/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.pickFn_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.pickFn_empty
/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.pickGetter_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.pickGetter_empty
/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.selected_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.selected_nonempty
/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.classify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.classify
/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.dispatch_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.dispatch_succ
/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.all_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.all_at
/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.all_callbacks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.all_callbacks
/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.static_call_storage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.static_call_storage
/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.Controls.function_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.Controls.function_selected
/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.Controls.function_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.Controls.function_witness
/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.Controls.getter_no_function' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.Controls.getter_no_function
/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.Controls.getter_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.Controls.getter_selected
/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.Controls.getter_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.Controls.getter_witness
/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.Controls.empty_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.Controls.empty_witness
/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.Controls.unknown_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.Controls.unknown_witness
/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.Controls.empty_function_impossible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.Controls.empty_function_impossible
/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.Controls.empty_getter_impossible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.Controls.empty_getter_impossible
/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.Controls.migrated_at_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.Controls.migrated_at_zero
/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.Controls.empty_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.Controls.empty_result
/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.Controls.callback_write_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.Controls.callback_write_refused
/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.Controls.horizon_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.Controls.horizon_zero
/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.Controls.migrated_all_callbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.Controls.migrated_all_callbacks
/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.Controls.migrated_all_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.Controls.migrated_all_at

/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.Controls.function_jointly_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.Controls.function_jointly_satisfiable

/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.Controls.getter_jointly_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.Controls.getter_jointly_satisfiable

/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.Controls.special_jointly_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.Controls.special_jointly_satisfiable

/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.Controls.v1_getter_empty_vacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.Controls.v1_getter_empty_vacuous

/-- info: 'Solidity.Lowering.Readonly.SourceDispatchV2.Controls.v1_special_empty_vacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.Readonly.SourceDispatchV2.Controls.v1_special_empty_vacuous
