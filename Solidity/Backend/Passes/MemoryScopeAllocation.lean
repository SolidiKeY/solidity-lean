import Solidity.Backend.Passes.MemoryScopeBoundary
import Solidity.Backend.Passes.PositiveAllocationFailure

namespace Solidity.Backend.Passes.MemoryScopeBoundary.Allocation
open Evm Evm.Memory
open PositiveAllocationFailure (C Γ F before base machine)

def bodyProgram : Prog C Γ (.mem PositiveAllocationFailure.A :: Γ) :=
  .cons PositiveAllocationFailure.allocate .nil
def body : CompiledProg 1 F bodyProgram :=
  (Memory.compileProg 1 F bodyProgram).get (by decide +kernel)
def outerCode := MemoryScopeBoundary.compiled body
noncomputable def reachedOut : Solidity.Out C before.H (.mem PositiveAllocationFailure.A :: Γ) :=
  (bodyProgram.run before).toOption.get (by rfl)
theorem source_run : bodyProgram.run before = .ok reachedOut := by
  have h : some reachedOut = (bodyProgram.run before).toOption := by
    unfold reachedOut
    exact Option.some_get _
  generalize bodyProgram.run before = result at h ⊢
  cases result with
  | ok out => exact congrArg Except.ok (Option.some.inj h).symm
  | error halt => cases h

theorem body_cost : body.cert.cost before = 1 := rfl
theorem scope_cost : outerCode.cert.cost before = 1 :=
  (MemoryScopeBoundary.cost body before).trans body_cost

theorem initial_input : (Evm.Compiler.Compilation.memory body).Input 1 16 base before (machine (wmod 64)) := by
  refine ⟨(PositiveAllocationFailure.initial (wmod 64) (by decide)).1, by decide +kernel, ?_⟩
  exact .inr ⟨by decide, wmod 64, (PositiveAllocationFailure.initial (wmod 64) (by decide)).2, by decide⟩

theorem shared_allocation :
    ∃ (canonical : Machine) (selected : Nat → Fin W), canonical.stack = [] ∧ ∀ tail,
      run outerCode.code {machine (wmod 64) with stack := tail} = .ok {canonical with stack := tail} 0 ∧
      MappedOutput (.memory outerCode) 1 16 base before {machine (wmod 64) with stack := tail}
        (reachedOut.st.drop bodyProgram.ext) {canonical with stack := tail} selected ∧
      StructAllocatorRepr (reachedOut.st.drop bodyProgram.ext).heap selected 16 (wmod 65)
        {canonical with stack := tail} := by
  obtain ⟨canonical,selected,empty,runs⟩ := MemoryScopeBoundary.shared body initial_input rfl source_run
  refine ⟨canonical,selected,empty,?_⟩
  intro tail
  have h := (runs tail).2.2
  have allocated := h.2.2 (wmod 64) (by decide)
    ((PositiveAllocationFailure.initial (wmod 64) (by decide)).2.mem_eq rfl) (by decide)
  exact ⟨(runs tail).2.1,h,allocated⟩

theorem scoped_source : (program bodyProgram).run before =
    .ok (⟨reachedOut.st.drop bodyProgram.ext, reachedOut.ext⟩ : Solidity.Out C before.H Γ) :=
  MemoryScopeBoundary.source_success source_run

theorem positive_cost : outerCode.cert.cost before ≠ 0 := by rw [scope_cost]; decide

end Solidity.Backend.Passes.MemoryScopeBoundary.Allocation
