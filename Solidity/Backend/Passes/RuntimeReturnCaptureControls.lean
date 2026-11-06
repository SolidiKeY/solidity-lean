import Solidity.Backend.Passes.RuntimeReturnCapture
import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerControls

/-! Real caller memory parameters survive a runtime-frame call returning seven,
then the reached caller result is captured in a new typed local. The SAME
compiled call instead reverts for index two; no post-failure map is invented. -/
namespace Solidity.Backend.Passes.RuntimeReturnCapture.Controls
open Evm Evm.Memory
open Solidity.Backend.InternalFlow.RuntimeFrame
namespace Fixture
open V3CallProducer.Controls
def operand : Val P Γ .uint := .simple (.local .here)
def valueCode : CompiledVal 0 selected.checked.frag operand :=
  (compileVal 0 selected.checked.frag operand).get (by decide +kernel)
def suffix := CapturedValueStability.captureStage (.user "captured") operand valueCode
def code : List Instr := (V3CallProducer.plan selected 8 8).code ++ suffix.code
def cells : List Nat := [3,4,2,1,0,8,9,16,17,18,20,21]
def expected : List Word := [w[7],w[7],w[16],w[16],w[20],w[10],w[0],w[2],w[7],w[9],w[1],w[4]]

theorem evaluated : operand.evalT output = .ok (uint 7 (by decide)) := rfl

/-- The actual physical admission and source call instantiate the correlated
consumer; its full intermediate map/output and all tails remain available. -/
def instantiated : type_of% (capture selected 8 8 flags positive_member
  ⟨output,List.prefix_refl _⟩ source_success (.user "captured") operand valueCode
  (uint 7 (by decide)) evaluated (by decide)) := capture selected 8 8 flags positive_member
  ⟨output,List.prefix_refl _⟩ source_success (.user "captured") operand valueCode
  (uint 7 (by decide)) evaluated (by decide)

theorem ordered :
    ∃ final, run code machine = .ok final 0 ∧
      final.stack = [w[77]] ∧ cells.map final.mem = expected := by
  obtain ⟨source,mid,addresses,word,final,repr,callRun,reached,stack,extension,growth,
    cursor,older,suffixInput,mapped,captureRun,joined,finalStack,finalCursor,finalOlder,total,tails⟩ :=
    instantiated
  have represented := mapped.1
  have fresh := represented.core.vals (.here : Idx (.val .uint :: Γ) (.val .uint))
  have returned := represented.core.vals (.there .here : Idx (.val .uint :: Γ) (.val .uint))
  have freshWord : final.mem 4 = w[7] :=
    Restored.value_unique fresh (ReprV.uint_of rfl)
  have returnedWord : final.mem 3 = w[7] :=
    Restored.value_unique returned (ReprV.uint_of rfl)
  have map0 : addresses 0 = bases 0 := extension CompileExamples.r0
  have map1 : addresses 1 = bases 1 := extension CompileExamples.r1
  obtain ⟨ref0,binding0,pointer0⟩ := represented.pointers
    (.there (.there .here) : Idx (.val .uint :: Γ) (.mem A))
  have same0 : ref0 = CompileExamples.r0 := (Option.some.inj binding0).symm
  subst ref0
  change final.mem 2 = .val (addresses 0) at pointer0
  rw [map0] at pointer0
  obtain ⟨ref1,binding1,pointer1⟩ := represented.pointers
    (.there (.there (.there .here)) : Idx (.val .uint :: Γ) (.mem A))
  have same1 : ref1 = CompileExamples.r0 := (Option.some.inj binding1).symm
  subst ref1
  change final.mem 1 = .val (addresses 0) at pointer1
  rw [map0] at pointer1
  obtain ⟨ref2,binding2,pointer2⟩ := represented.pointers
    (.there (.there (.there (.there .here))) : Idx (.val .uint :: Γ) (.mem A))
  have same2 : ref2 = CompileExamples.r1 := (Option.some.inj binding2).symm
  subst ref2
  change final.mem 0 = .val (addresses 1) at pointer2
  rw [map1] at pointer2
  have array0 := represented.heap.arrays CompileExamples.r0
  have array1 := represented.heap.arrays CompileExamples.r1
  change ArrayRepr CompileExamples.hp CompileExamples.r0 (addresses 0) final at array0
  change ArrayRepr CompileExamples.hp CompileExamples.r1 (addresses 1) final at array1
  rw [map0] at array0
  rw [map1] at array1
  have len0 : final.mem 16 = w[2] := by
    simpa only [Heap.len,CompileExamples.hp,CompileExamples.r0,CompileExamples.H,
      Heap.get,Objs.get,MObj.elems_dyn,List.length_cons,List.length_nil] using array0.length
  have len1 : final.mem 20 = w[1] := by
    simpa only [Heap.len,CompileExamples.hp,CompileExamples.r1,CompileExamples.H,
      Heap.get,Objs.get,MObj.elems_dyn,List.length_cons,List.length_nil] using array1.length
  have elem0 : final.mem 17 = w[7] :=
    Restored.value_unique (array0.elements 0 (uint 7 (by decide)) (by with_unfolding_all rfl)) (ReprV.uint_of rfl)
  have elem1 : final.mem 18 = w[9] :=
    Restored.value_unique (array0.elements 1 (uint 9 (by decide)) (by with_unfolding_all rfl)) (ReprV.uint_of rfl)
  have independent : final.mem 21 = w[4] :=
    Restored.value_unique (array1.elements 0 (uint 4 (by decide)) (by with_unfolding_all rfl)) (ReprV.uint_of rfl)
  have olderWord : final.mem 9 = w[0] := finalOlder 9 (by decide) (by decide)
  refine ⟨final,joined,finalStack,?_⟩
  change [final.mem 3,final.mem 4,final.mem 2,final.mem 1,final.mem 0,final.mem 8,
    final.mem 9,final.mem 16,final.mem 17,final.mem 18,final.mem 20,final.mem 21] = _
  rw [returnedWord,freshWord,pointer0,pointer1,pointer2,finalCursor,
    olderWord,len0,elem0,elem1,len1,independent]
  rfl

/-- Real failure of the SAME call occurs before the consumer is reached. -/
theorem failure : run code failedMachine = .revert :=
  run_append_revert target_reverts

theorem failure_source :
    (Prog.cons call (.cons (.declLocal .uint (.user "captured") (some operand)) .nil)).run
      failing = .error .revert :=
  Prog.run_cons_error source_revert

theorem failure_tail (tail : List Word) :
    run code (appendTail failedMachine tail) = .revert := by
  have actual := run_tail code failedMachine tail
    (by rw [failure]; intro impossible; cases impossible)
  simpa only [failure,appendOut] using actual

/-- This is the actual consumer code, not an alternate evaluator. -/
theorem suffix_instructions : suffix.code = [.mload 3,.mstore 4] := rfl

theorem wrong_order : run suffix.code machine =
    .ok (writeMachine machine 4 w[0]) 0 := by
  rw [suffix_instructions]
  rfl

theorem wrong_capture :
    (writeMachine machine 4 w[0]).mem 4 ≠ w[7] := by decide

theorem wrong_tail (tail : List Word) :
    ∃ final, run code (appendTail machine tail) = .ok (appendTail final tail) 0 ∧
      (appendTail final tail).stack ≠ w[78] :: tail := by
  obtain ⟨final,actual,stack,observed⟩ := ordered
  have transported := run_tail code machine tail
    (by rw [actual]; intro impossible; cases impossible)
  refine ⟨final,?_,?_⟩
  · simpa only [actual,appendOut] using transported
  · simp only [appendTail,stack,List.cons_append,List.nil_append]
    intro same
    have bad : w[77] = (w[78] : Word) := (List.cons.inj same).1
    exact (by decide : (w[77] : Word) ≠ w[78]) bad

theorem insufficient_private_frame :
    ¬ V3CallProducer.admitted selected 8 8 1 16 initial bases
      V3CallProducer.Controls.capacityMachine 14 :=
  V3CallProducer.Controls.refuses_arena_capacity

end Fixture
end Solidity.Backend.Passes.RuntimeReturnCapture.Controls
