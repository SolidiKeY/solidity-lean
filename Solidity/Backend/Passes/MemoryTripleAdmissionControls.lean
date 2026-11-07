import Solidity.Backend.Passes.MemoryTripleAdmission
import Solidity.Backend.Passes.MemoryJoinedAllocation
import Solidity.Backend.Passes.TripleControls
import Solidity.Backend.Passes.AllocatedReferenceRead

namespace Solidity.Backend.Passes.MemoryTripleAdmission.Controls
open Evm Evm.Memory Evm.Compiler
open Backend.Passes.Controls.Fixture
open AllocatingControls MemoryJoinCost.Controls MemoryJoinedAllocation

abbrev ReadCtx : Ctx := .mem (.array (.prim .uint)) :: Γ
def lengthValue : Val C ReadCtx .uint := .mlen (.var .here rfl) rfl
def capture : Prog C ReadCtx (.val .uint :: ReadCtx) :=
  .cons (.declLocal .uint (.user "length") (some lengthValue)) .nil
noncomputable def captureOut : Solidity.Out C (suffixOut σ).st.H (.val .uint :: ReadCtx) :=
  ⟨(suffixOut σ).st.push (t:=.val .uint) (CompileExamples.uint 3 (by decide)),List.prefix_refl _⟩

theorem length_source : lengthValue.evalT (suffixOut σ).st =
    .ok (CompileExamples.uint 3 (by decide)) := by
  with_unfolding_all rfl

theorem capture_source : capture.run (suffixOut σ).st = .ok captureOut := by
  have declaration : (Stmt.declLocal .uint (.user "length") (some lengthValue)).run
      (suffixOut σ).st = .ok captureOut := by
    change TRun.declLocal .uint (some lengthValue) _ = _
    simp only [TRun.declLocal,length_source,bind,Except.bind,pure,Except.pure]
    rfl
  rw [capture,Prog.run_cons_ok declaration,Prog.run_nil]
  rfl

def captureCode : CompiledProg 1 suffixCode.frag capture :=
  (Memory.compileProg 1 suffixCode.frag capture).get (by decide)
theorem capture_public : Memory.compileProg 1 suffixCode.frag capture = some captureCode := by
  exact (Option.some_get _).symm

theorem total_cost : allocationCostProg
    (ReachabilityControls.populatedBuilder.join (appendAllocation.join capture)) (State.init C) = 9 := by
  rw [MemoryJoinCost.successful_prefix _ _ _ _ ReachabilityControls.fresh_state_reaches_fixture,
    MemoryJoinCost.successful_prefix _ _ _ _ (suffix_source σ)]
  change allocationStage.cert.cost (State.init C) + (allocationCostProg appendAllocation σ + 0) = 9
  rw [reached_cost,MemoryJoinCost.Controls.suffix_cost]

theorem budget : AllocationInput 1 7
    (allocationCostProg (ReachabilityControls.populatedBuilder.join (appendAllocation.join capture)) (State.init C))
    (State.init C) initialBase initialMachine := by
  refine .inr ⟨by decide,⟨16,by decide⟩,TripleControls.initial_repr7.2,?_⟩
  rw [total_cost]
  decide

def admitted := public_admission allocationStage suffixCode captureCode prefix_public suffix_public capture_public
  initialBase (State.init C) initialMachine TripleControls.initial_repr7.1
  (by decide) (by decide) (by decide) budget

def source_both := triple_source_success (State.init C)
  ReachabilityControls.fresh_state_reaches_fixture (suffix_source σ) capture_source

/-- All stage maps and machines precede tails. Both links used here were
derived from the single original public joined Input, not supplied as premises. -/
theorem shared :
    ∃ (mb nb ob : Nat → Fin W) (middle next final : Machine),
      middle.stack = [] ∧ next.stack = [] ∧ final.stack = [] ∧ ∀ tail,
      run allocationStage.code {initialMachine with stack := tail} = .ok {middle with stack := tail} 0 ∧
      run suffixCode.code {middle with stack := tail} = .ok {next with stack := tail} 0 ∧
      run captureCode.code {next with stack := tail} = .ok {final with stack := tail} 0 ∧
      run ((allocationStage.code ++ suffixCode.code) ++ captureCode.code)
        {initialMachine with stack := tail} = .ok {final with stack := tail} 0 ∧
      run (allocationStage.code ++ (suffixCode.code ++ captureCode.code))
        {initialMachine with stack := tail} = .ok {final with stack := tail} 0 ∧
      MappedOutput (.memory allocationStage) 1 7 initialBase (State.init C)
        {initialMachine with stack := tail} σ {middle with stack := tail} mb ∧
      MappedOutput (.memory suffixCode) 1 7 mb σ {middle with stack := tail}
        (suffixOut σ).st {next with stack := tail} nb ∧
      MappedOutput (.memory captureCode) 1 7 nb (suffixOut σ).st {next with stack := tail}
        captureOut.st {final with stack := tail} ob := by
  obtain ⟨inner,whole,_,_,_,_,_,_,firstInput,firstLink,secondLink⟩ := admitted
  exact compilation_triple_shared (.memory allocationStage) (.memory suffixCode) (.memory captureCode)
    firstInput rfl firstLink secondLink rfl rfl rfl
    ReachabilityControls.fresh_state_reaches_fixture (suffix_source σ) capture_source

def code : List Instr := allocationStage.code ++ (suffixCode.code ++ captureCode.code)

private def readCell (n : Nat) : Evm.Out → Option Nat
  | .ok machine _ => match machine.mem n with | .val word => some word.val | _ => none
  | _ => none
private theorem cell0 : readCell 6 (run code initialMachine) = some 3 := by decide +kernel
private theorem cell1 : readCell 5 (run code initialMachine) = some 21 := by decide +kernel
private theorem cell2 : readCell 4 (run code initialMachine) = some 0 := by decide +kernel
private theorem cell3 : readCell 2 (run code initialMachine) = some 16 := by decide +kernel
private theorem cell4 : readCell 3 (run code initialMachine) = some 16 := by decide +kernel
private theorem cell5 : readCell 1 (run code initialMachine) = some 19 := by decide +kernel
private theorem cell6 : readCell 7 (run code initialMachine) = some 0 := by decide +kernel
private theorem cell7 : readCell 16 (run code initialMachine) = some 2 := by decide +kernel
private theorem cell8 : readCell 17 (run code initialMachine) = some 7 := by decide +kernel
private theorem cell9 : readCell 18 (run code initialMachine) = some 9 := by decide +kernel
private theorem cell10 : readCell 19 (run code initialMachine) = some 1 := by decide +kernel
private theorem cell11 : readCell 20 (run code initialMachine) = some 4 := by decide +kernel
private theorem cell12 : readCell 21 (run code initialMachine) = some 3 := by decide +kernel
private theorem cell13 : readCell 22 (run code initialMachine) = some 0 := by decide +kernel
private theorem cell14 : readCell 23 (run code initialMachine) = some 0 := by decide +kernel
private theorem cell15 : readCell 24 (run code initialMachine) = some 0 := by decide +kernel
private theorem cell16 : readCell 0 (run code initialMachine) = some 25 := by decide +kernel

theorem complete_result :
    [6,5,4,2,3,1,7,16,17,18,19,20,21,22,23,24,0].mapM
      (fun n => readCell n (run code initialMachine)) =
      some [3,21,0,16,16,19,0,2,7,9,1,4,3,0,0,0,25] := by
  simp only [List.mapM_cons,List.mapM_nil,cell0,cell1,cell2,cell3,cell4,cell5,cell6,cell7,cell8,cell9,cell10,cell11,cell12,cell13,cell14,cell15,cell16]
  rfl

theorem wrong_old_length : readCell 6 (run code initialMachine) ≠ some 2 := by
  rw [cell0]
  decide

theorem third_frame_required
    (whole : CompiledProg 1 (Frag.init [])
      (ReachabilityControls.populatedBuilder.join (appendAllocation.join capture))) :
    ¬ (Compilation.memory whole).Input 1 6 initialBase (State.init C) initialMachine := by
  intro input
  have bound := ((MemoryJoinFrame.input_iff whole initialBase (State.init C) initialMachine).mp input).2.2.1
  change 1 + max 5 6 ≤ 6 at bound
  omega

def badCapture : Prog C ReadCtx (.val .uint :: ReadCtx) :=
  .cons (.declLocal .uint (.user "bad") (some AllocatedReferenceRead.wrongReader)) .nil
def badCaptureCode : CompiledProg 1 suffixCode.frag badCapture :=
  (Memory.compileProg 1 suffixCode.frag badCapture).get (by decide)
theorem bad_public : Memory.compileProg 1 suffixCode.frag badCapture = some badCaptureCode := by
  exact (Option.some_get _).symm

theorem bad_source : badCapture.run (suffixOut σ).st = .error .revert := by
  have declaration : (Stmt.declLocal .uint (.user "bad") (some AllocatedReferenceRead.wrongReader)).run
      (suffixOut σ).st = .error .revert := by
    change TRun.declLocal .uint (some AllocatedReferenceRead.wrongReader) _ = _
    simp only [TRun.declLocal,AllocatedReferenceRead.wrong_source,bind,Except.bind]
  exact Prog.run_cons_error declaration

theorem bad_budget : AllocationInput 1 7
    (allocationCostProg (ReachabilityControls.populatedBuilder.join (appendAllocation.join badCapture)) (State.init C))
    (State.init C) initialBase initialMachine := by
  have cost : allocationCostProg
      (ReachabilityControls.populatedBuilder.join (appendAllocation.join badCapture)) (State.init C) = 9 := by
    rw [MemoryJoinCost.successful_prefix _ _ _ _ ReachabilityControls.fresh_state_reaches_fixture,
      MemoryJoinCost.successful_prefix _ _ _ _ (suffix_source σ)]
    change allocationStage.cert.cost (State.init C) + (allocationCostProg appendAllocation σ + 0) = 9
    rw [reached_cost,MemoryJoinCost.Controls.suffix_cost]
  refine .inr ⟨by decide,⟨16,by decide⟩,TripleControls.initial_repr7.2,?_⟩
  rw [cost]
  decide

theorem reached_third_failure (tail : List Word) :
    run (allocationStage.code ++ (suffixCode.code ++ badCaptureCode.code))
      {initialMachine with stack := tail} = .revert := by
  obtain ⟨inner,whole,_,_,_,_,_,wholeInput,_,_,_⟩ :=
    public_admission allocationStage suffixCode badCaptureCode prefix_public suffix_public bad_public
      initialBase (State.init C) initialMachine TripleControls.initial_repr7.1
      (by decide) (by decide) (by decide) bad_budget
  have wholeTail := compilation_input_stack (.memory whole) wholeInput tail
  obtain ⟨firstInput,firstLink,secondLink⟩ := links allocationStage suffixCode badCaptureCode inner whole wholeTail
  apply (compilation_triple_revert_iff (.memory allocationStage) (.memory suffixCode) (.memory badCaptureCode)
    firstInput firstLink secondLink rfl rfl rfl).mpr
  exact .inr ⟨_,ReachabilityControls.fresh_state_reaches_fixture,
    .inr ⟨_,suffix_source σ,.inl bad_source⟩⟩

#print axioms shared
#print axioms complete_result
end Solidity.Backend.Passes.MemoryTripleAdmission.Controls
