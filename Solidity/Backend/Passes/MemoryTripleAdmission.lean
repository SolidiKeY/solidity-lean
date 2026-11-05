import Solidity.Backend.Passes.MemoryJoinFrame
import Solidity.Backend.Passes.TripleSequence

/-! Three public legacy-memory stages obtain both physical links from one
original admitted joined Input. No independent link or future-run budget
family is assumed. Other compiler branches retain their distinct interfaces. -/
namespace Solidity.Backend.Passes.MemoryTripleAdmission
open Evm Evm.Memory Evm.Compiler
variable {C : Contract} {b L frame : Nat} {Γ Δ Ξ Ω : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ} {Q : Prog C Δ Ξ} {R : Prog C Ξ Ω}

/-- First derive the actual Q+R Input after P. Its prefix Input supplies Q,
and its binary link supplies R after Q, using the same actual selected maps. -/
theorem links (a : CompiledProg b F P) (d : CompiledProg b a.frag Q)
    (e : CompiledProg b d.frag R) (inner : CompiledProg b a.frag (Q.join R))
    (whole : CompiledProg b F (P.join (Q.join R)))
    {base : Nat → Fin W} {state : State C Γ} {machine : Machine}
    (admitted : (Compilation.memory whole).Input L frame base state machine) :
    (Compilation.memory a).Input L frame base state machine ∧
    MappedBoundaryLink (.memory a) (.memory d) L frame base state machine ∧
    ReachedMappedLink (.memory a) (.memory d) (.memory e) L frame base state machine := by
  have outer := MemoryJoinFrame.boundary_link a inner whole admitted
  refine ⟨MemoryJoinFrame.left_input a whole admitted,?_,?_⟩
  · intro out middle selected reached target mapped
    exact MemoryJoinFrame.left_input d inner (outer out middle selected reached target mapped)
  · intro out middle selected reached target mapped
    exact MemoryJoinFrame.boundary_link d e inner (outer out middle selected reached target mapped)

/-- One initial joined allocation budget and three unchanged static bounds
admit three ACTUAL public compiler stages and close both dependent links. -/
theorem public_admission
    (a : CompiledProg b F P) (d : CompiledProg b a.frag Q) (e : CompiledProg b d.frag R)
    (ha : Memory.compileProg b F P = some a)
    (hd : Memory.compileProg b a.frag Q = some d)
    (he : Memory.compileProg b d.frag R = some e)
    (base : Nat → Fin W) (state : State C Γ) (machine : Machine)
    (represented : StateRepr L b frame F state base machine)
    (capP : b + frameNeedProg P ≤ frame) (capQ : b + frameNeedProg Q ≤ frame)
    (capR : b + frameNeedProg R ≤ frame)
    (budget : AllocationInput b frame (allocationCostProg (P.join (Q.join R)) state)
      state base machine) :
    ∃ (inner : CompiledProg b a.frag (Q.join R))
      (whole : CompiledProg b F (P.join (Q.join R))),
      Memory.compileProg b a.frag (Q.join R) = some inner ∧
      Memory.compileProg b F (P.join (Q.join R)) = some whole ∧
      inner.frag = e.frag ∧ whole.frag = e.frag ∧
      whole.code = a.code ++ (d.code ++ e.code) ∧
      (Compilation.memory whole).Input L frame base state machine ∧
      (Compilation.memory a).Input L frame base state machine ∧
      MappedBoundaryLink (.memory a) (.memory d) L frame base state machine ∧
      ReachedMappedLink (.memory a) (.memory d) (.memory e) L frame base state machine := by
  obtain ⟨inner,innerAccepted,innerFrag,innerCode⟩ := memory_compile_join d e hd he
  obtain ⟨whole,wholeAccepted,wholeFrag,wholeCode,input,_,_⟩ :=
    MemoryJoinFrame.public_admission a inner ha innerAccepted base state machine represented capP
      (by rw [MemoryJoinFrame.frame_join]; omega) budget
  obtain ⟨firstInput,firstLink,secondLink⟩ := links a d e inner whole input
  refine ⟨inner,whole,innerAccepted,wholeAccepted,innerFrag,wholeFrag.trans innerFrag,
    ?_,input,firstInput,firstLink,secondLink⟩
  rw [wholeCode,innerCode]

#print axioms links
#print axioms public_admission
end Solidity.Backend.Passes.MemoryTripleAdmission
