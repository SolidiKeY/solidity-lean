import Solidity.Backend.Passes.DeferredConditionFailure
import Solidity.Backend.Passes.DeferredConditionControls

/-! A real captured prefix followed by a typed out-of-bounds Boolean read;
immediate ordinary revert and asserting panic remain distinct source halts. -/
namespace Solidity.Backend.Passes.DeferredConditionFailure.Controls
open Evm Evm.Memory Evm.Compiler
open Passes.Controls.Fixture
open ReferenceControls (Γb fb state target input_repr)
open QueueCompletionControls (good update after cells)

def bad : Val C (.val .bool :: Γb) .bool :=
  QueueCompletionControls.bad.wk (Thin.drop .refl)
def operand : DeferredSource.Operand C Γb (.prim .bool) :=
  ⟨.val .bool :: Γb,DeferredCondition.Controls.operand.code,.val bad⟩
def code : CompiledProg 0 fb operand.code := DeferredCondition.Controls.code
def reader : CompiledVal 0 code.frag (DeferredCondition.expression operand) :=
  (Memory.compileVal 0 code.frag (DeferredCondition.expression operand)).get (by decide +kernel)

theorem prefix_public : Memory.compileProg 0 fb operand.code = some code :=
  DeferredCondition.Controls.code_public
theorem reader_public : Memory.compileVal 0 code.frag (DeferredCondition.expression operand) = some reader :=
  (Option.some_get _).symm

def captured (a : Bool) : Solidity.Out C (state a).H (.val .bool :: Γb) :=
  ⟨((state a).push (t := .val .bool) a).setLocal (.there .here) false,List.prefix_refl _⟩
theorem prefix_source (a : Bool) : operand.code.run (state a) = .ok (captured a) :=
  CapturedValueStability.source (.user "saved") good .here update (state a) a false rfl rfl

theorem failed_read (a : Bool) :
    (DeferredCondition.expression operand).evalT (captured a).st = .error .revert := by
  cases a <;> with_unfolding_all rfl

theorem correlated (a : Bool) : type_of%
    (reached_shared operand code reader (DeferredCondition.Controls.input a) (by rfl)
      (captured a) (prefix_source a) (failed_read a)) :=
  reached_shared operand code reader (DeferredCondition.Controls.input a) (by rfl)
    (captured a) (prefix_source a) (failed_read a)

theorem prefix_target (a : Bool) (tail : List Word) :
    run code.code {(target a) with stack := tail} = .ok (after a tail) 0 := rfl

theorem reached_reader (a : Bool) (tail : List Word) :
    run reader.code (after a tail) = .revert := by
  obtain ⟨canonical,stack,hstack,rep⟩ := compilation_success (.memory code)
    (compilation_input_stack (.memory code) (DeferredCondition.Controls.input a) tail)
    (by rfl) (prefix_source a)
  have same : canonical = after a tail :=
    (Evm.Out.ok.inj (stack.symm.trans (prefix_target a tail))).1
  subst canonical
  obtain ⟨selected,full⟩ := (mapped_output_iff (.memory code) _ _ _ _ _ _ _).mp rep
  rw [code.cert.pushes_zero,Nat.add_zero] at full
  exact (value_revert_iff reader full.1 tail).mpr (failed_read a)

theorem joined (a : Bool) (tail : List Word) :
    run (code.code ++ reader.code) {(target a) with stack := tail} = .revert := by
  rw [run_append_ok (prefix_target a tail)]
  exact reached_reader a tail

/-- Complete successful-prefix vector is observed before the failing read. -/
theorem observations (a : Bool) (tail : List Word) :
    (cells.map (after a tail).mem,(after a tail).stack) =
      ([.val (bword a),w[0],w[0],w[16],w[16],w[20],w[2],w[7],w[9],w[1],w[4]],tail) := rfl

def observe : Evm.Out → Option (List Word × List Word)
  | .ok m _ => some (cells.map m.mem,m.stack)
  | _ => none

theorem skipped_effect : observe (run reader.code (target true)) = none ∧
    observe (.ok (target true) 0) ≠ observe (run code.code (target true)) := by
  constructor <;> decide +kernel

theorem corrupt_prefix_tail : observe (run code.code {(target true) with stack := [w[77],w[88]]}) ≠
    observe (.ok (after true [w[88],w[77]]) 0) := by decide +kernel

def immediate (asserting : Bool) : DeferredSource.Operand C Γb (.prim .bool) :=
  ⟨Γb,.cons (if asserting then .assert (.simple (.bool false))
      else .require (.simple (.bool false))) .nil,.val good⟩
def immediateCode : CompiledProg 0 fb (immediate false).code :=
  (Memory.compileProg 0 fb (immediate false).code).get (by decide +kernel)
def immediateReader : CompiledVal 0 immediateCode.frag
    (DeferredCondition.expression (immediate false)) :=
  (Memory.compileVal 0 immediateCode.frag
    (DeferredCondition.expression (immediate false))).get (by decide +kernel)

theorem immediate_public : Memory.compileProg 0 fb (immediate false).code = some immediateCode :=
  (Option.some_get _).symm

theorem immediate_input (a : Bool) :
    (Compilation.memory immediateCode).Input 1 6 base (state a) (target a) := by
  exact ⟨input_repr a,by decide +kernel,.inl rfl⟩

theorem immediate_source (a : Bool) :
    (immediate false).run (state a) = .error .revert ∧
    (immediate true).run (state a) = .error .panic ∧
    (immediate true).code.asserts = true := ⟨rfl,rfl,rfl⟩

theorem immediate_target (a : Bool) (tail : List Word) :
    run (immediateCode.code ++ immediateReader.code) {(target a) with stack := tail} = .revert := by
  have terminal : run immediateCode.code {(target a) with stack := tail} = .revert :=
    (compilation_revert_iff (.memory immediateCode)
      (compilation_input_stack _ (immediate_input a) tail) (by rfl)).mpr (.inl rfl)
  exact run_append_revert terminal

/-- Preserve the actual narrow memory selector refusal; core accepts assert. -/
theorem panic_memory_refused : (Memory.compileProg 0 fb (immediate true).code).isNone = true := by
  decide +kernel

def panicCode : Compilation 0 fb (immediate true).code :=
  (Compiler.compile 0 fb (immediate true).code).get (by decide +kernel)
def panicReader : CompiledVal 0 panicCode.frag (DeferredCondition.expression (immediate true)) :=
  (Memory.compileVal 0 panicCode.frag
    (DeferredCondition.expression (immediate true))).get (by decide +kernel)
theorem panic_public : Compiler.compile 0 fb (immediate true).code = some panicCode :=
  (Option.some_get _).symm

theorem panic_input (a : Bool) : panicCode.Input 1 6 base (state a) (target a) := by
  exact ⟨(input_repr a).core,by decide⟩

theorem panic_target (a : Bool) (tail : List Word) :
    run (panicCode.code ++ panicReader.code) {(target a) with stack := tail} = .revert := by
  have terminal := (compilation_revert_iff panicCode
    (compilation_input_stack panicCode (panic_input a) tail) (by rfl)).mpr (.inr ⟨rfl,rfl⟩)
  exact run_append_revert terminal

theorem wrong_stage : operand.code.run (state true) ≠ .error .revert := by
  rw [prefix_source true]
  intro h
  cases h

theorem witness (a : Bool) (tail : List Word) : type_of%
    ((revert_witness_iff operand code reader
      (compilation_input_stack (.memory code) (DeferredCondition.Controls.input a) tail)
      (by rfl)).mp (joined a tail)) :=
  (revert_witness_iff operand code reader
    (compilation_input_stack (.memory code) (DeferredCondition.Controls.input a) tail)
    (by rfl)).mp (joined a tail)

/-- These actual ordinary failures are neither asserting panic nor divergence. -/
theorem halt_separation (a : Bool) :
    operand.run (state a) ≠ .error .panic ∧ operand.run (state a) ≠ .error .diverge := by
  have failed := (correlated a).1
  rw [failed]
  constructor <;> intro h <;> cases h

theorem native_terminal (a : Bool) (tail : List Word) :
    run (code.code ++ reader.code) {(target a) with stack := tail} = .revert ↔
      operand.run (state a) = .error .revert ∨
      (operand.code.asserts = true ∧ operand.run (state a) = .error .panic) :=
  revert_iff operand code reader
    (compilation_input_stack (.memory code) (DeferredCondition.Controls.input a) tail) (by rfl)

end Solidity.Backend.Passes.DeferredConditionFailure.Controls

/-- info: 'Solidity.Backend.Passes.DeferredConditionFailure.Controls.prefix_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredConditionFailure.Controls.prefix_public

/-- info: 'Solidity.Backend.Passes.DeferredConditionFailure.Controls.reader_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredConditionFailure.Controls.reader_public

/-- info: 'Solidity.Backend.Passes.DeferredConditionFailure.Controls.prefix_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredConditionFailure.Controls.prefix_source

/-- info: 'Solidity.Backend.Passes.DeferredConditionFailure.Controls.failed_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredConditionFailure.Controls.failed_read

/-- info: 'Solidity.Backend.Passes.DeferredConditionFailure.Controls.correlated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredConditionFailure.Controls.correlated

/-- info: 'Solidity.Backend.Passes.DeferredConditionFailure.Controls.prefix_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredConditionFailure.Controls.prefix_target

/-- info: 'Solidity.Backend.Passes.DeferredConditionFailure.Controls.reached_reader' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredConditionFailure.Controls.reached_reader

/-- info: 'Solidity.Backend.Passes.DeferredConditionFailure.Controls.joined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredConditionFailure.Controls.joined

/-- info: 'Solidity.Backend.Passes.DeferredConditionFailure.Controls.observations' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredConditionFailure.Controls.observations

/-- info: 'Solidity.Backend.Passes.DeferredConditionFailure.Controls.skipped_effect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredConditionFailure.Controls.skipped_effect

/-- info: 'Solidity.Backend.Passes.DeferredConditionFailure.Controls.corrupt_prefix_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredConditionFailure.Controls.corrupt_prefix_tail

/-- info: 'Solidity.Backend.Passes.DeferredConditionFailure.Controls.immediate_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredConditionFailure.Controls.immediate_public

/-- info: 'Solidity.Backend.Passes.DeferredConditionFailure.Controls.immediate_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredConditionFailure.Controls.immediate_input

/-- info: 'Solidity.Backend.Passes.DeferredConditionFailure.Controls.immediate_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredConditionFailure.Controls.immediate_source

/-- info: 'Solidity.Backend.Passes.DeferredConditionFailure.Controls.immediate_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredConditionFailure.Controls.immediate_target

/-- info: 'Solidity.Backend.Passes.DeferredConditionFailure.Controls.panic_memory_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredConditionFailure.Controls.panic_memory_refused

/-- info: 'Solidity.Backend.Passes.DeferredConditionFailure.Controls.panic_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredConditionFailure.Controls.panic_public

/-- info: 'Solidity.Backend.Passes.DeferredConditionFailure.Controls.panic_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredConditionFailure.Controls.panic_input

/-- info: 'Solidity.Backend.Passes.DeferredConditionFailure.Controls.panic_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredConditionFailure.Controls.panic_target

/-- info: 'Solidity.Backend.Passes.DeferredConditionFailure.Controls.wrong_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredConditionFailure.Controls.wrong_stage

/-- info: 'Solidity.Backend.Passes.DeferredConditionFailure.Controls.witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredConditionFailure.Controls.witness

/-- info: 'Solidity.Backend.Passes.DeferredConditionFailure.Controls.halt_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredConditionFailure.Controls.halt_separation

/-- info: 'Solidity.Backend.Passes.DeferredConditionFailure.Controls.native_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.DeferredConditionFailure.Controls.native_terminal
