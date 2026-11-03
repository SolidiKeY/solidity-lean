import Solidity.Backend.Passes.RuntimeVoidCapture
import Solidity.Backend.InternalFlow.RuntimeFrameV3FixedThunkProducer
import Solidity.Backend.InternalFlow.RuntimeFrameRestoredRepresentation

namespace Solidity.Backend.Passes.RuntimeVoidCapture.Controls
open Evm Evm.Memory
open Solidity.Backend.InternalFlow.RuntimeFrame
open V3FixedThunkProducer.Witness

def operand : Val P.C P.Γ .uint :=
  .readMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 0 rfl)))
def valueCode : CompiledVal 0 selected.checked.frag operand :=
  (compileVal 0 selected.checked.frag operand).get (by first | rfl | decide | omega)
attribute [irreducible] valueCode

def suffix := CapturedValueStability.captureStage (.user "captured") operand valueCode
def code : List Instr := (NoneProducer.plan selected 8 8).code ++ suffix.code
def cells : List Nat := [3,4,2,1,0,8,9,16,17,18,20,21]
def expected : List Word :=
  [w[0],w[37],w[16],w[16],w[20],w[10],w[99],w[2],w[37],w[9],w[1],w[4]]

theorem evaluated : operand.evalT reached = .ok (P.uint 37 (by decide)) := by
  first | rfl | decide | omega | with_unfolding_all rfl

theorem evaluated_before : operand.evalT caller0 = .ok (P.uint 7 (by decide)) := by
  first | rfl | decide | omega | with_unfolding_all rfl

def entry := V3FixedThunkProducer.coverage thunk selected 8 8 nonallocating
  1 16 caller0 P.base machine0 10 member0

def instantiated : type_of% (capture selected 8 8
  (NoneProducer.init_flags selected.checked.frag .refl) entry
  ⟨reached,List.prefix_refl _⟩ source0 (.user "captured") operand valueCode
  (P.uint 37 (by decide)) evaluated (by decide)) :=
  capture selected 8 8 (NoneProducer.init_flags selected.checked.frag .refl) entry
    ⟨reached,List.prefix_refl _⟩ source0 (.user "captured") operand valueCode
    (P.uint 37 (by decide)) evaluated (by decide)

/-- All caller aliases, both array payloads, runtime cursor and protected word. -/
theorem ordered :
    ∃ final, run code machine0 = .ok final 0 ∧
      final.stack = [w[77]] ∧ cells.map final.mem = expected := by
  obtain ⟨source,mid,addresses,word,final,repr,callRun,callRepr,stack,extension,growth,
    cursor,older,suffixInput,mapped,captureRun,joined,finalStack,finalCursor,finalOlder,total,tails⟩ :=
    instantiated
  have represented := mapped.1
  have fresh := represented.core.vals (.here : Idx (.val .uint :: P.Γ) (.val .uint))
  have returned := represented.core.vals (.there .here : Idx (.val .uint :: P.Γ) (.val .uint))
  have freshWord : final.mem 4 = w[37] :=
    Restored.value_unique fresh (ReprV.uint_of rfl)
  have indexWord : final.mem 3 = w[0] :=
    Restored.value_unique returned (ReprV.uint_of rfl)
  have map0 : addresses 0 = P.base 0 := extension CompileExamples.r0
  have map1 : addresses 1 = P.base 1 := extension CompileExamples.r1
  obtain ⟨ref0,binding0,pointer0⟩ := represented.pointers
    (.there (.there .here) : Idx (.val .uint :: P.Γ) (.mem A))
  have same0 : ref0 = CompileExamples.r0 := (Option.some.inj binding0).symm
  subst ref0
  change final.mem 2 = .val (addresses 0) at pointer0
  rw [map0] at pointer0
  obtain ⟨ref1,binding1,pointer1⟩ := represented.pointers
    (.there (.there (.there .here)) : Idx (.val .uint :: P.Γ) (.mem A))
  have same1 : ref1 = CompileExamples.r0 := (Option.some.inj binding1).symm
  subst ref1
  change final.mem 1 = .val (addresses 0) at pointer1
  rw [map0] at pointer1
  obtain ⟨ref2,binding2,pointer2⟩ := represented.pointers
    (.there (.there (.there (.there .here))) : Idx (.val .uint :: P.Γ) (.mem A))
  have same2 : ref2 = CompileExamples.r1 := (Option.some.inj binding2).symm
  subst ref2
  change final.mem 0 = .val (addresses 1) at pointer2
  rw [map1] at pointer2
  have array0 := represented.heap.arrays CompileExamples.r0
  have array1 := represented.heap.arrays CompileExamples.r1
  change ArrayRepr reached.heap CompileExamples.r0 (addresses 0) final at array0
  change ArrayRepr reached.heap CompileExamples.r1 (addresses 1) final at array1
  rw [map0] at array0
  rw [map1] at array1
  have len0 : final.mem 16 = w[2] := by
    with_unfolding_all exact array0.length
  have len1 : final.mem 20 = w[1] := by
    with_unfolding_all exact array1.length
  have elem0 : final.mem 17 = w[37] :=
    Restored.value_unique (array0.elements 0 (P.uint 37 (by decide)) (by with_unfolding_all rfl)) (ReprV.uint_of rfl)
  have elem1 : final.mem 18 = w[9] :=
    Restored.value_unique (array0.elements 1 (P.uint 9 (by decide)) (by with_unfolding_all rfl)) (ReprV.uint_of rfl)
  have independent : final.mem 21 = w[4] :=
    Restored.value_unique (array1.elements 0 (P.uint 4 (by decide)) (by with_unfolding_all rfl)) (ReprV.uint_of rfl)
  have olderWord : final.mem 9 = w[99] := finalOlder 9 (by decide) (by decide)
  refine ⟨final,joined,finalStack,?_⟩
  change [final.mem 3,final.mem 4,final.mem 2,final.mem 1,final.mem 0,final.mem 8,
    final.mem 9,final.mem 16,final.mem 17,final.mem 18,final.mem 20,final.mem 21] = _
  rw [indexWord,freshWord,pointer0,pointer1,pointer2,finalCursor,
    olderWord,len0,elem0,elem1,len1,independent]
  rfl

/-- A body bounds failure occurs before the capture stage. -/
theorem failure : run code machine9 = .revert :=
  run_append_revert (NoneProducer.bare_revert selected 8 8 1 16 caller9 P.base machine9 10
    (V3FixedThunkProducer.coverage thunk selected 8 8 nonallocating
      1 16 caller9 P.base machine9 10 member9) source9)

theorem failure_source :
    (Prog.cons call (.cons (.declLocal .uint (.user "captured") (some operand)) .nil)).run
      caller9 = .error .revert := Prog.run_cons_error source9

theorem failure_tail (tail : List Word) : run code (appendTail machine9 tail) = .revert := by
  have actual := run_tail code machine9 tail
    (by rw [failure]; intro impossible; cases impossible)
  simpa only [failure,appendOut] using actual

theorem fragment : selected.checked.frag = F := by
  first | rfl | decide | omega | decide +kernel

/-- Capturing before the mutation reads the old seven, not the reached 37. -/
theorem premature_capture : run suffix.code machine0 =
    .ok (writeMachine machine0 4 w[7]) 0 := by
  have represented : StateRepr 1 0 16 selected.checked.frag caller0 P.base machine0 := by
    rw [fragment]
    exact represented0
  obtain ⟨word,repr,actual⟩ := value_success_tail valueCode represented evaluated_before machine0.stack
  have same : word = w[7] := Restored.value_unique repr (ReprV.uint_of rfl)
  have valueRun : run valueCode.code machine0 = .ok (machine0.push w[7]) 0 := by
    simpa only [same] using actual
  change run ((valueCode.code ++ [.mstore 4]) ++ []) machine0 = _
  rw [List.append_nil,run_append_ok valueRun]
  rfl

theorem stale_capture_refused : (writeMachine machine0 4 w[7]).mem 4 ≠ w[37] := by decide

theorem corrupt_tail_refused (tail : List Word) :
    ∃ final, run code (appendTail machine0 tail) = .ok (appendTail final tail) 0 ∧
      (appendTail final tail).stack ≠ w[78] :: tail := by
  obtain ⟨final,actual,stack,observed⟩ := ordered
  have transported := run_tail code machine0 tail
    (by rw [actual]; intro impossible; cases impossible)
  refine ⟨final,?_,?_⟩
  · simpa only [actual,appendOut] using transported
  · simp only [appendTail,stack,List.cons_append,List.nil_append]
    intro same
    have bad : w[77] = (w[78] : Word) := (List.cons.inj same).1
    exact (by decide : (w[77] : Word) ≠ w[78]) bad

theorem insufficient_private_frame : ¬ domain 1 14 caller0 P.base machine0 10 :=
  insufficient_frame_refused

end Solidity.Backend.Passes.RuntimeVoidCapture.Controls
