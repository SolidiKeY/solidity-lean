import Solidity.Backend.Passes.FreshBooleanFailure
import Solidity.Backend.Passes.MemoryCompilerSequence

/-! The concrete joined application is accepted by the existing compiler,
and its actual emitted instructions equal the separately linked pass code. -/
namespace Solidity.Backend.Passes.FreshBooleanCompilation
open Evm Evm.Memory Evm.Compiler
open Controls.Fixture FixedBooleanSequence FreshBooleanFailure

def wholeStage (b : Bool) : Memory.CompiledProg 1 (Frag.init []) (wholeProgram b) :=
  (Memory.compileProg 1 (Frag.init []) (wholeProgram b)).get (by cases b <;> decide +kernel)

theorem whole_recognized (b : Bool) :
    (Compiler.compile 1 (Frag.init []) (wholeProgram b)).map (·.isMemory) = some true := by
  cases b <;> decide +kernel

theorem whole_code (b : Bool) : (wholeStage b).code = wholeCode b := by
  have hc : Memory.compileProg 1 receiver.frag capturePrefix = some captureStage := (Option.some_get _).symm
  have ho : Memory.compileProg 1 captureStage.frag badObserve = some badStage := (Option.some_get _).symm
  have hr : Memory.compileProg 1 BF ReferenceControls.branchThenRead = some receiver := (Option.some_get _).symm
  have hi : Memory.compileProg 1 F (ReferenceControls.initializeBool b) = some (initializer b) :=
    (Option.some_get _).symm
  have hp : Memory.compileProg 1 (Frag.init []) ReachabilityControls.populatedBuilder = some population :=
    (Option.some_get _).symm
  obtain ⟨suffix,hs,_,cs⟩ := memory_compile_join captureStage badStage hc ho
  obtain ⟨body,hbody,_,cb⟩ := memory_compile_join receiver suffix hr hs
  obtain ⟨initBody,hinit,_,ci⟩ := memory_compile_join (initializer b) body hi hbody
  have aligned := memory_reindex_compile population_fragment initBody hinit
  obtain ⟨joined,hj,_,cj⟩ := memory_compile_join population
    (memory_reindex population_fragment initBody) hp aligned
  have actual : Memory.compileProg 1 (Frag.init []) (wholeProgram b) = some joined := by
    simpa only [wholeProgram,prefixProgram,typed_sequencing_assoc] using hj
  have get : some (wholeStage b) = Memory.compileProg 1 (Frag.init []) (wholeProgram b) :=
    Option.some_get _
  have same : wholeStage b = joined := Option.some.inj (get.trans actual)
  rw [same,cj,memory_reindex_code,ci,cb,cs]
  simp only [wholeCode,prefixCode,List.append_assoc]

theorem public_whole (b : Bool) :
    Compiler.compile 1 (Frag.init []) (wholeProgram b) = some (.memory (wholeStage b)) := by
  have core : inFragP (Frag.init []) (wholeProgram b) = none :=
    Option.isNone_iff_eq_none.mp (by cases b <;> decide +kernel)
  have memory : some (wholeStage b) = Memory.compileProg 1 (Frag.init []) (wholeProgram b) :=
    Option.some_get _
  unfold Compiler.compile
  split
  · rename_i frag hc
    rw [core] at hc
    cases hc
  · simp only [← memory]

theorem public_whole_code (b : Bool) :
    (Compiler.compile 1 (Frag.init []) (wholeProgram b)).map (·.code) = some (wholeCode b) := by
  rw [public_whole]
  simpa only [Option.map_some,Compilation.code] using congrArg some (whole_code b)

theorem whole_input (b : Bool) :
    (Compilation.memory (wholeStage b)).Input 1 128 initialBase initial initialMachine :=
  ⟨MemoryCallControls.initial_repr.1,by cases b <;> decide +kernel,
    .inr ⟨by cases b <;> decide +kernel,wmod 256,MemoryCallControls.initial_repr.2,
      by cases b <;> decide +kernel⟩⟩

theorem whole_certificate (b : Bool) (tail : List Word) :
    (Compilation.memory (wholeStage b)).Agrees 1 128 initialBase initial
      {initialMachine with stack := tail} :=
  (Compilation.memory (wholeStage b)).correct
    (compilation_input_stack (.memory (wholeStage b)) (whole_input b) tail)

theorem actual_revert (tail : List Word) :
    run (wholeStage true).code {initialMachine with stack := tail} = .revert := by
  rw [whole_code]
  exact (fresh_revert tail).2.1

theorem actual_opposite_target : ∃ out : Machine, ∀ tail,
    run (wholeStage false).code {initialMachine with stack := tail} = .ok {out with stack := tail} 0 := by
  obtain ⟨pb,ib,rb,cb,ob,mid,captured,out,hall⟩ := fresh_opposite_shared
  refine ⟨out,?_⟩
  intro tail
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hwhole,_⟩ := hall tail
  rw [whole_code]
  exact hwhole

end Solidity.Backend.Passes.FreshBooleanCompilation
