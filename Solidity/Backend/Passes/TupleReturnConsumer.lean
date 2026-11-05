import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerRefTupleControls
import Solidity.Backend.Passes.MappedTail
import Solidity.Backend.Passes.CapturedValueStability

/-! Consume the published checked mixed-tuple emitter through the existing
Compilation.memoryCalls constructor and its ACTUAL returned map. This does not
claim the automatic whole-call recognizer accepts tuple returns. -/
namespace Solidity.Backend.Passes.TupleReturnConsumer
open Evm Evm.Memory Evm.Compiler
open Backend.InternalFlow.RuntimeFrame
open Backend.InternalFlow.RuntimeFrame.V3CallProducerRef
open Backend.InternalFlow.RuntimeFrame.V3CallProducerRef.Tuple.Controls

abbrev program : Prog C Γ (rs ++ Γ) := .cons call .nil

def compiled : Compilation 1 F program := .memoryCalls selected.checked (by rfl)

theorem expanded_public : Composition.compileProgram 1 F
    (Tuple.expand ArrayControls.args binders body) = some expanded := by
  exact (Option.some_get _).symm

private theorem frame_bound : 1 + selected.checked.need ≤ 64 := by decide

theorem input (n : Fin W) : compiled.Input 1 64 ArrayControls.bases
    (ArrayControls.caller n) (ArrayControls.machine n) := by
  change StateRepr 1 1 64 F _ _ _ ∧ 1 + selected.checked.need ≤ 64 ∧
    AllocationInput 1 64 (selected.checked.cost _) _ _ _
  exact ⟨(ArrayControls.initial n).1,frame_bound,capacity n⟩

noncomputable def result : Solidity.Out C (ArrayControls.caller (wmod 0)).H (rs ++ Γ) :=
  Classical.choose source_success

theorem program_source : program.run (ArrayControls.caller (wmod 0)) = .ok result := by
  have actual : call.run (ArrayControls.caller (wmod 0)) = .ok result := Classical.choose_spec source_success
  rw [program,Prog.run_cons_ok actual,Prog.run_nil]
  rfl

def reader : Val C (rs ++ Γ) .uint := .simple (.local .here)
def readerCode : CompiledVal 1 compiled.frag reader :=
  (Memory.compileVal 1 compiled.frag reader).get (by decide +kernel)

theorem reader_public : Memory.compileVal 1 compiled.frag reader = some readerCode :=
  (Option.some_get _).symm

/-- No result map, state or receiving representation is assumed. The actual
published tuple certificate supplies it at the reached mixed return context. -/
theorem shared :
    ∃ (canonical : Machine) (addresses : Nat → Fin W) (word : Word), canonical.stack = [] ∧
      ReprV .uint (TEnv.get .here result.st.env) word ∧
      BaseExtends (ArrayControls.caller (wmod 0)).H ArrayControls.bases addresses ∧ ∀ tail,
      run compiled.code {(ArrayControls.machine (wmod 0)) with stack := tail} =
        .ok {canonical with stack := tail} 0 ∧
      MappedOutput compiled 1 64 ArrayControls.bases (ArrayControls.caller (wmod 0))
        {(ArrayControls.machine (wmod 0)) with stack := tail} result.st
        {canonical with stack := tail} addresses ∧
      StateRepr 1 1 64 compiled.frag result.st addresses {canonical with stack := tail} ∧
      run readerCode.code {canonical with stack := tail} =
        .ok ({canonical with stack := tail}.push word) 0 ∧
      run (compiled.code ++ readerCode.code) {(ArrayControls.machine (wmod 0)) with stack := tail} =
        .ok ({canonical with stack := tail}.push word) 0 := by
  obtain ⟨canonical,addresses,_,empty,runs⟩ :=
    compilation_success_shared_mapped compiled (input (wmod 0)) (by rfl) program_source
  have mapped : MappedOutput compiled 1 64 ArrayControls.bases (ArrayControls.caller (wmod 0))
      {(ArrayControls.machine (wmod 0)) with stack := []} result.st {canonical with stack := []} addresses :=
    (runs []).2
  have evaluated : reader.evalT result.st = .ok (TEnv.get .here result.st.env) := rfl
  obtain ⟨word,repr,reads⟩ := CapturedValueStability.value_shared reader readerCode mapped.1
    (TEnv.get .here result.st.env) evaluated
  refine ⟨canonical,addresses,word,empty,repr,mapped.2.1,?_⟩
  intro tail
  have represented : StateRepr 1 1 64 compiled.frag result.st addresses {canonical with stack := tail} :=
    (runs tail).2.1
  have read := reads tail
  refine ⟨(runs tail).1,(runs tail).2,represented,read,?_⟩
  rw [run_append_ok (runs tail).1]
  exact read

theorem reached_revert (tail : List Word) :
    run (compiled.code ++ readerCode.code) {(ArrayControls.machine (wmod 2)) with stack := tail} = .revert := by
  have failed : program.run (ArrayControls.caller (wmod 2)) = .error .revert :=
    Prog.run_cons_error source_revert
  have target := (compilation_revert_iff compiled
    (compilation_input_stack compiled (input (wmod 2)) tail) (by rfl)).mpr (.inl failed)
  exact run_append_revert target

/-- Keep automatic selection separate from the actual checked emission. -/
theorem automatic_refused : (Compiler.compile 1 F program).isNone = true := by decide +kernel

/-- info: 'Solidity.Backend.Passes.TupleReturnConsumer.expanded_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expanded_public
/-- info: 'Solidity.Backend.Passes.TupleReturnConsumer.reader_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reader_public
/-- info: 'Solidity.Backend.Passes.TupleReturnConsumer.input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms input
/-- info: 'Solidity.Backend.Passes.TupleReturnConsumer.shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shared
/-- info: 'Solidity.Backend.Passes.TupleReturnConsumer.reached_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reached_revert
/-- info: 'Solidity.Backend.Passes.TupleReturnConsumer.automatic_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms automatic_refused
end Solidity.Backend.Passes.TupleReturnConsumer
