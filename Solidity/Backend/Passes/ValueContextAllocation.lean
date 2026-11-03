import Solidity.Backend.Passes.ValueContextControls

/-! Real emitted allocation, fresh reference declaration and unchanged old
value code. Both original source and actual physical maps remain explicit. -/
namespace Solidity.Backend.Passes.ValueContextAllocation
open Solidity.Evm Solidity.Evm.Compiler Solidity.Evm.Memory
open Solidity.Backend.Passes.Controls.Fixture
open Solidity.Backend.Passes.AllocatingControls
open Solidity.Backend.Passes.TripleControls
open Solidity.Backend.Passes.ValueSequenceControls
open Solidity.Backend.Passes.ValueContextControls
private abbrev A : RefTy := .array (.prim .uint)
private abbrev oldR1 : Idx Γ (.mem A) := .there (.there (.there .here))

def freshRefStage : CompiledProg 1 allocationStage.frag refProg :=
  (compileProg 1 allocationStage.frag refProg).get (by decide +kernel)

theorem allocated_reference : ∃ (mid : Machine) (mb : Nat → Fin W) (word : Word),
    run allocationStage.code initialMachine = .ok mid 0 ∧
    MappedOutput (.memory allocationStage) 1 7 initialBase (State.init C)
      initialMachine σ mid mb ∧
    refProg.run σ = .ok ⟨σ.push (t := .mem A) (some CompileExamples.r1), List.prefix_refl _⟩ ∧
    run freshRefStage.code mid = .ok (writeMachine mid 5 (.val (mb CompileExamples.r1.id))) 0 ∧
    StateRepr 1 1 7 (allocationStage.frag.push (.mem A) .ok)
      (σ.push (t := .mem A) (some CompileExamples.r1)) mb
      (writeMachine mid 5 (.val (mb CompileExamples.r1.id))) ∧
    ReprV .uint seven word ∧
    run (allocationStage.code ++ (freshRefStage.code ++ freshA.code)) initialMachine =
      .ok ((writeMachine mid 5 (.val (mb CompileExamples.r1.id))).push word) 0 := by
  obtain ⟨mid, hm, _, hr⟩ := compilation_success (.memory allocationStage)
    prefix_input7 rfl ReachabilityControls.fresh_state_reaches_fixture
  obtain ⟨mb, ha⟩ := (mapped_output_iff (.memory allocationStage) _ _ _ _ _ _ _).mp hr
  have ma : MappedOutput (.memory allocationStage) 1 7 initialBase (State.init C)
      initialMachine σ mid mb := by
    simpa only [allocationStage.cert.pushes_zero, Nat.add_zero] using ha
  obtain ⟨rr, hs, hp⟩ := ma.1.pointers oldR1
  change some CompileExamples.r1 = some rr at hs
  have he : rr = CompileExamples.r1 := (Option.some.inj hs).symm
  cases he
  change mid.mem 1 = .val (mb CompileExamples.r1.id) at hp
  have hd : run freshRefStage.code mid =
      .ok (writeMachine mid 5 (.val (mb CompileExamples.r1.id))) 0 := by
    change Evm.Out.ok (writeMachine mid 5 (mid.mem 1)) 0 = _
    rw [hp]
  have hi := memory_extend_reference ma.1 CompileExamples.r1 (frame' := 7) (by decide)
    ma.1.heap.above ma.1.structs.above mid.stack
  obtain ⟨word, hw, ht⟩ := value_after_fresh_reference freshA ma.1 CompileExamples.r1
    (frame' := 7) (by decide) ma.1.heap.above ma.1.structs.above first_source mid.stack
  have hm' : run allocationStage.code initialMachine = .ok mid 0 := hm
  exact ⟨mid, mb, word, hm', ma, reference_source, hd, hi, hw,
    by rw [run_append_ok hm', run_append_ok hd]; exact ht⟩


def recognizedOldValue : CompiledVal 1 (allocationStage.frag.push (.mem A) .ok)
    (first.wk (Thin.drop (t := .mem A) .refl)) :=
  (compileVal 1 _ _).get (by decide +kernel)
private theorem old_recognized (F : Frag Γ) :
    ((compileVal 1 F first).get (by rfl)).code =
      readLocalValueCode 1 (.there .here : Idx Γ (.mem A)) [.push w[0]] := by rfl

private theorem fresh_recognized (F : Frag (.mem A :: Γ)) :
    ((compileVal 1 F (first.wk (Thin.drop (t := .mem A) .refl))).get (by rfl)).code =
      readLocalValueCode 1 (.there (.there .here) : Idx (.mem A :: Γ) (.mem A)) [.push w[0]] := by rfl

theorem recognizer_same_code : recognizedOldValue.code = freshA.code := by
  rw [show recognizedOldValue.code = _ from fresh_recognized (allocationStage.frag.push (.mem A) .ok),
    show freshA.code = _ from old_recognized allocationStage.frag]
  rfl

def code : List Instr := allocationStage.code ++ (freshRefStage.code ++ freshA.code)
private def cell (n : Nat) : Evm.Out → Option Nat
  | .ok m _ => match m.mem n with | .val w => some w.val | _ => none
  | _ => none

private theorem c5 : cell 5 (run code initialMachine) = some 19 := by decide +kernel
private theorem c4 : cell 4 (run code initialMachine) = some 0 := by decide +kernel
private theorem c2 : cell 2 (run code initialMachine) = some 16 := by decide +kernel
private theorem c3 : cell 3 (run code initialMachine) = some 16 := by decide +kernel
private theorem c1 : cell 1 (run code initialMachine) = some 19 := by decide +kernel
private theorem c17 : cell 17 (run code initialMachine) = some 7 := by decide +kernel
private theorem c18 : cell 18 (run code initialMachine) = some 9 := by decide +kernel
private theorem c20 : cell 20 (run code initialMachine) = some 4 := by decide +kernel
private theorem c0 : cell 0 (run code initialMachine) = some 21 := by decide +kernel

/-- Fresh alias plus every original allocation observation, including both
old aliases/elements, independent cell and cursor; no dropped unchanged cell. -/
theorem ordered_observations : [5,4,2,3,1,17,18,20,0].mapM
    (fun n => cell n (run code initialMachine)) = some [19,0,16,16,19,7,9,4,21] := by
  simp only [List.mapM_cons, List.mapM_nil, c5, c4, c2, c3, c1, c17, c18, c20, c0]
  rfl

end Solidity.Backend.Passes.ValueContextAllocation
