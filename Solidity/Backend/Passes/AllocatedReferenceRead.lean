import Solidity.Backend.Passes.MemoryJoinedAllocation
import Solidity.Backend.Passes.CapturedValueStability

/-! Consume the actual newly allocated reference at its reached selected map.
The alternative old alias has a different bound. Both readers are selected
by the existing public value compiler; no Source lowering is asserted. -/
namespace Solidity.Backend.Passes.AllocatedReferenceRead
open Evm Evm.Memory Evm.Compiler
open Backend.Passes.Controls.Fixture
open AllocatingControls MemoryJoinCost.Controls MemoryJoinedAllocation

abbrev ReadCtx : Ctx := .mem (.array (.prim .uint)) :: Γ

def reader : Val C ReadCtx .uint :=
  .readMem (.index .dyn (.var .here rfl) (.simple (.lit 2 rfl)))
def wrongReader : Val C ReadCtx .uint :=
  .readMem (.index .dyn (.var (.there (.there .here)) rfl) (.simple (.lit 2 rfl)))
def readerCode : CompiledVal 1 suffixCode.frag reader :=
  (Memory.compileVal 1 suffixCode.frag reader).get (by decide)
def wrongCode : CompiledVal 1 suffixCode.frag wrongReader :=
  (Memory.compileVal 1 suffixCode.frag wrongReader).get (by decide)
def zero : PrimTy.uint.Denote := CompileExamples.uint 0 (by decide)

theorem reader_public : Memory.compileVal 1 suffixCode.frag reader = some readerCode := by
  exact (Option.some_get _).symm

theorem wrong_public : Memory.compileVal 1 suffixCode.frag wrongReader = some wrongCode := by
  exact (Option.some_get _).symm

theorem reader_source : reader.evalT (suffixOut σ).st = .ok zero := by
  with_unfolding_all rfl

theorem wrong_source : wrongReader.evalT (suffixOut σ).st = .error .revert := by
  with_unfolding_all rfl

theorem source_success :
    ((ReachabilityControls.populatedBuilder.join appendAllocation).run (State.init C) >>= fun out =>
      reader.evalT out.st) = .ok zero := by
  simp only [joined_source,bind,Except.bind,reader_source]

theorem source_failure :
    ((ReachabilityControls.populatedBuilder.join appendAllocation).run (State.init C) >>= fun out =>
      wrongReader.evalT out.st) = .error .revert := by
  simp only [joined_source,bind,Except.bind,wrong_source]

/-- The actual selected allocation map supplies the receiving value compiler.
A typed wrong-alias read fails only after the same real allocation prefix. -/
theorem execution :
    ∃ joined : CompiledProg 1 (Frag.init [])
      (ReachabilityControls.populatedBuilder.join appendAllocation),
      Memory.compileProg 1 (Frag.init [])
        (ReachabilityControls.populatedBuilder.join appendAllocation) = some joined ∧
      ∃ (final : Machine) (selected : Nat → Fin W), final.stack = [] ∧ ∀ tail,
        run joined.code {initialMachine with stack := tail} = .ok {final with stack := tail} 0 ∧
        MappedOutput (.memory joined) 1 6 initialBase (State.init C)
          {initialMachine with stack := tail} (suffixOut σ).st {final with stack := tail} selected ∧
        StateRepr 1 1 6 suffixCode.frag (suffixOut σ).st selected {final with stack := tail} ∧
        run readerCode.code {final with stack := tail} = .ok ({final with stack := tail}.push w[0]) 0 ∧
        run (joined.code ++ readerCode.code) {initialMachine with stack := tail} =
          .ok ({final with stack := tail}.push w[0]) 0 ∧
        run wrongCode.code {final with stack := tail} = .revert ∧
        run (joined.code ++ wrongCode.code) {initialMachine with stack := tail} = .revert ∧
        {final with stack := tail}.mem 0 = w[25] := by
  obtain ⟨joined,accepted,_,middle,final,middleBase,selected,stack,_,_,allTails⟩ :=
    MemoryJoinedAllocation.execution
  have rightMapped := (allTails []).2.2.2.2.1
  obtain ⟨word,repr,readRuns⟩ := CapturedValueStability.value_shared
    reader readerCode rightMapped.1 zero reader_source
  rcases repr with ⟨actual,rfl,numeric⟩
  have actualZero : actual = (⟨0,by decide⟩ : Fin W) := by
    apply Fin.ext
    change actual.val = 0
    change (0:Int) = actual.val at numeric
    omega
  rw [actualZero] at readRuns
  refine ⟨joined,accepted,final,selected,stack,?_⟩
  intro tail
  rcases allTails tail with ⟨_,_,_,_,lastMapped,prefixRun,wholeMapped,cursor⟩
  have readRun := readRuns tail
  have badRun := (value_revert_iff wrongCode lastMapped.1 tail).mpr wrong_source
  refine ⟨prefixRun,wholeMapped,lastMapped.1,readRun,?_,badRun,?_,cursor⟩
  · rw [run_append_ok prefixRun]
    exact readRun
  · rw [run_append_ok prefixRun]
    exact badRun

#print axioms reader_source
#print axioms wrong_source
#print axioms execution
end Solidity.Backend.Passes.AllocatedReferenceRead
