import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarContinuation

/-! Exact bare revert after a successful scalar recursive return. The returned
three is consumed as an invalid index into the old length-two array. This is
separate from failure in the argument prefix and yields no failed state. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarContinuation.Revert
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
open DisjointScalarReturn.Client

def write : Stmt CountdownWitness.P.C Γ Γ :=
 .assignMem (.index .dyn (.var reference rfl) (.simple scalar)) (.val (.simple (.lit 0 rfl)))
def suffix : Prog CountdownWitness.P.C Γ Γ := .cons write .nil
def compiled : CompiledProg 1 F suffix := (compileProg 1 F suffix).get (by rfl)
def checked : Calls.Program 1 F suffix := Calls.plain compiled

theorem selected : compileProg 1 F suffix=some compiled := rfl

theorem actual_index : scalar.evalT origin=countValue 3 (by decide) := rfl

theorem invalid_index : ¬(3:Nat)<origin.heap.len ScalarContinuation.ref .dyn := by
 rw [old_length]
 decide

theorem source_suffix : suffix.run origin=.error .revert := by
 with_unfolding_all rfl

theorem exact_cost : checked.cost origin=0 := checked.zeroCost rfl origin

def program : Prog CountdownWitness.P.C Γ Γ := .cons (ScalarDual.statement 4) suffix
def image : List Instr := (ScalarDemandDual.outputPlan.at 4).code++checked.code

theorem source_program : program.run caller=.error .revert := by
 rw [program,Prog.run_cons_ok ScalarDual.good_source,source_suffix]
 rfl

theorem matched : GrowingResult 1 1 16 0 checked.frag caller CountdownWitness.P.base before
 (program.run caller) (run image before) := by
 have actual := ReturnContinuation.after_return
   (ScalarDemandDual.producer.required_return 4) (ScalarDemandDual.good_entry 4)
   ScalarDual.good_source suffix checked (by decide) (by
     change AllocationInput 1 16 (0+checked.cost origin) caller CountdownWitness.P.base before
     rw [exact_cost]
     exact .inl rfl)
 simpa only [ScalarDemandDual.outputPlan,ScalarDemand.plan,InterfaceV1.RecursiveEmission.at,Nat.zero_add,exact_cost] using actual

theorem suffix_target : run checked.code machine=.revert := by
 have actual := checked.sound specification.2.2.1 (by decide) (by rw [exact_cost];exact .inl rfl)
 rcases actual with ⟨out,target,addresses,source,rest⟩ | ⟨source,target⟩
 · rw [source_suffix] at source
   cases source
 · exact target

theorem target_revert : run image before=.revert :=
 (run_append_ok (ScalarDemandDual.good_execution 4)).trans suffix_target

/-- The intermediate target is obtained from the same actual recursive call;
no failed output state or rollback relation is asserted. -/
theorem returned_then_reverted :
 run (ScalarDemandDual.outputPlan.at 4).code before=.ok machine 0 ∧
 run checked.code machine=.revert ∧ run image before=.revert :=
 ⟨ScalarDemandDual.good_execution 4,suffix_target,target_revert⟩

theorem not_fault : run image before≠.fault := by
 rw [target_revert]
 intro wrong
 cases wrong

theorem not_success (state : Machine) (remaining : Nat) : run image before≠.ok state remaining := by
 rw [target_revert]
 intro wrong
 cases wrong

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarContinuation.Revert
