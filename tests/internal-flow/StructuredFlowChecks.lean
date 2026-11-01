import Solidity.Backend.InternalFlow.StructuredFrame
import tests.«internal-flow».CompletedLoopFrameChecks
namespace Solidity.Backend.InternalFlow.StructuredChecks
open Evm Evm.Memory PublishedLoopChecks SuccessfulLoop CompletedLoopChecks
open AllocatingLoopHalts (allocate)

def loopBlock : Stmt C Caller Caller := .block (.cons actualLoop .nil)
def arm : Prog C Caller (.mem A :: Caller) := .cons loopBlock (.cons allocate .nil)
def branch (selected : Bool) : Stmt C Caller Caller :=
  .ite (.simple (.bool selected)) arm (.cons .revert .nil)
def program (selected : Bool) : Prog C Caller Caller :=
  .cons (.block (.cons (branch selected) .nil)) .nil

def allocatedAfter : Solidity.Out C finalOut.st.H (.mem A :: Caller) :=
  ⟨finalOut.st.allocPush (defaultArray .uint (wmod 2)),List.prefix_append _ _⟩
def armOut : Solidity.Out C callMid.st.H (.mem A :: Caller) :=
  ⟨allocatedAfter.st,finalOut.ext.trans allocatedAfter.ext⟩
def reached : Solidity.Out C callMid.st.H Caller :=
  ⟨allocatedAfter.st.drop (Ext.push Ext.refl),armOut.ext⟩

theorem loop_block_run : loopBlock.run callMid.st = .ok finalOut := by
  change ((Prog.cons actualLoop Prog.nil).run callMid.st).map _ = _
  rw [Prog.run_cons_ok actual_loop]
  rfl

theorem allocation_run : allocate.run finalOut.st = .ok allocatedAfter :=
  newArray_decl finalOut.st .uint (.lit 2 rfl) (wmod 2) rfl

theorem arm_run : arm.run callMid.st = .ok armOut := by
  rw [show arm = .cons loopBlock (.cons allocate .nil) from rfl,Prog.run_cons_ok loop_block_run]
  rw [Prog.run_cons_ok allocation_run]
  rfl

theorem branch_run : (branch true).run callMid.st = .ok reached := by
  change (arm.run callMid.st).map _ = _
  rw [arm_run]
  rfl

theorem actual_run : (program true).run callMid.st = .ok reached := by
  have hb : (Stmt.block (.cons (branch true) .nil)).run callMid.st = .ok reached := by
    change ((Prog.cons (branch true) Prog.nil).run callMid.st).map _ = _
    rw [Prog.run_cons_ok branch_run]
    rfl
  exact (Prog.run_cons_ok hb).trans rfl

def loopProof (i : Idx Caller (.mem A)) : FrameStmt .view (.mem A) actualLoop i :=
  .loop .auto (condition true) SuccessfulLoop.body i (by decide +kernel) allocation_body_within (by
    cases i with
    | here => decide +kernel
    | there i => cases i with
      | here => decide +kernel
      | there i => cases i with | there i => cases i)

def armProof (i : Idx Caller (.mem A)) : FrameProg .view (.mem A) arm i :=
  .cons (.block (.cons (loopProof i) (.nil _)))
    (.cons (.leaf allocate i (by decide +kernel) (by exact List.not_mem_nil)) (.nil _))

def proofFor (selected : Bool) (i : Idx Caller (.mem A)) :
    FrameProg .view (.mem A) (program selected) i :=
  .cons (.block (.cons (.branch (.simple (.bool selected)) (by cases selected <;> rfl)
    (armProof i) (.cons (.leaf .revert i (by decide +kernel) (by exact List.not_mem_nil)) (.nil _))) (.nil _))) (.nil _)

theorem framed : TGFrameM .view callMid.st reached.st reached.ext ∧
    TEnv.get (.here : Idx Caller (.mem A)) reached.st.env =
      LTy.TDenote.wk reached.ext (.mem A) (TEnv.get .here callMid.st.env) ∧
    TEnv.get (.there .here : Idx Caller (.mem A)) reached.st.env =
      LTy.TDenote.wk reached.ext (.mem A) (TEnv.get (.there .here) callMid.st.env) := by
  have a := FrameProg.sound (proofFor true .here) actual_run
  have b := FrameProg.sound (proofFor true (.there .here)) actual_run
  exact ⟨a.1,a.2,b.2⟩

theorem old_contents : Heap.Keeps reached.ext callMid.st.heap reached.st.heap := framed.1.keeps

theorem complete_values :
 (reached.st.H.length,[callArray reached.st 0,callArray reached.st 1,callArray reached.st 2,callArray reached.st 3],
    caller reached.st,count reached.st) =
 (4,[some [0],some [2,7,11],some [2,0,0],some [2,0,0]],[some 1,some 1,some 0],some 9) := by decide +kernel

theorem existing_guard_unchanged : Prog.withinM .view (program true) = false := by decide +kernel

theorem false_branch : (program false).run callMid.st = .error .revert := by rfl

theorem wrong_observations : caller reached.st ≠ [some 3,some 1,some 0] ∧
    callArray reached.st 1 ≠ some [2,7,99] ∧ reached.st.H.length ≠ 3 := by
  repeat' constructor
  all_goals decide +kernel

theorem actual_writer_excluded : ¬ FrameProg .view (.mem A) followup (.here : Idx Caller (.mem A)) := by
  intro proof
  exact writer_not_kept (FrameProg.sound proof use_source).1.keeps

theorem changed_marker_not_protected : ¬ FrameProg .view (.val .uint) (program true)
    (.there (.there .here) : Idx Caller (.val .uint)) := by
  intro proof
  have h := (FrameProg.sound proof actual_run).2
  have wrong : TEnv.get (.there (.there .here) : Idx Caller (.val .uint)) reached.st.env ≠
      LTy.TDenote.wk reached.ext (.val .uint)
        (TEnv.get (.there (.there .here) : Idx Caller (.val .uint)) callMid.st.env) := by decide +kernel
  exact wrong h

#print axioms changed_marker_not_protected
#print axioms FrameStmt.sound
#print axioms FrameProg.sound
#print axioms actual_run
#print axioms framed
#print axioms old_contents
#print axioms complete_values
#print axioms existing_guard_unchanged
#print axioms false_branch
#print axioms wrong_observations
#print axioms actual_writer_excluded
end Solidity.Backend.InternalFlow.StructuredChecks
