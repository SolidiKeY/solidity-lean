import Solidity.Backend.InternalFlow.RuntimeFrameV3NativeAllocationCoherence
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarTarget

/-! Exact populated native heap/output identity across sufficient indices,
with genuinely insufficient quotation retained as exhaustion. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.NativeAllocationCoherence.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
abbrev C := CompileExamples.C
abbrev A := CountdownWitness.A
abbrev σ := AllocatingScalarTarget.initial

def expected : Solidity.Out C σ.H (Frame A) :=
 ⟨finished (AllocatingScalarSource.allocated (AllocatingScalarSource.allocated σ)) 2 (by decide),
   (AllocatingScalarSource.extension σ).trans (AllocatingScalarSource.extension (AllocatingScalarSource.allocated σ))⟩

theorem exact_heap :
 (AllocatingScalarSource.body A (by rfl) 3).run σ=.ok expected ∧
 (AllocatingScalarSource.body A (by rfl) 5).run σ=.ok expected ∧
 expected.st.H.length=4 ∧
 (AllocatingScalarSource.body A (by rfl) 2).run σ=.error .exhausted ∧
 (AllocatingScalarSource.body A (by rfl) 2).run σ≠(AllocatingScalarSource.body A (by rfl) 5).run σ := by
 have actual : (AllocatingScalarSource.body A (by rfl) 3).run σ=.ok expected :=
   AllocatingScalarSource.two_return (by rfl) σ 0 CountdownWitness.P.r0 rfl rfl
 have stable := NativeAllocationCoherence.stable (by rfl) 3 5 σ 2 (by decide) CountdownWitness.P.r0 rfl rfl (by decide) (by decide)
 have longer : (AllocatingScalarSource.body A (by rfl) 5).run σ=.ok expected := stable.symm.trans actual
 have short := AllocatingScalarSource.exhaustion (by rfl) 2 σ 2 (by decide) CountdownWitness.P.r0 rfl rfl (by decide)
 refine ⟨actual,longer,rfl,short,?_⟩
 rw [short,longer]
 intro impossible
 cases impossible

end Solidity.Backend.InternalFlow.RuntimeFrame.NativeAllocationCoherence.Controls

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.NativeAllocationCoherence.Controls.exact_heap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.NativeAllocationCoherence.Controls.exact_heap
