import Solidity.Backend.Passes.MemoryJoinedOutput

/-! Association transport for actual legacy-memory compiler selections.
Admission and the full mapped relation retain frame/capacity and the same
chosen map. This is not a public resource/session adequacy theorem. -/
namespace Solidity.Backend.Passes.MemoryAssociation
open Evm Evm.Memory Evm.Compiler
variable {C : Contract} {b L frame : Nat} {Γ Δ Ξ Ω : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ} {Q : Prog C Δ Ξ} {R : Prog C Ξ Ω}

/-- The original static frame bound and actual prefix-cost budget agree
under intrinsic program association, for successes and all failure cases. -/
theorem input_iff (left : CompiledProg b F ((P.join Q).join R))
    (right : CompiledProg b F (P.join (Q.join R)))
    (base : Nat → Fin W) (state : State C Γ) (machine : Machine) :
    (Compilation.memory left).Input L frame base state machine ↔
    (Compilation.memory right).Input L frame base state machine := by
  change (StateRepr L b frame F state base machine ∧
    b + frameNeedProg ((P.join Q).join R) ≤ frame ∧
    AllocationInput b frame (allocationCostProg ((P.join Q).join R) state) state base machine) ↔ _
  rw [typed_sequencing_assoc]
  rfl

/-- Public selection fixes both actual output fragments and emitted code;
no equality of represented machine components is inferred from Rep. -/
theorem selected (left : CompiledProg b F ((P.join Q).join R))
    (right : CompiledProg b F (P.join (Q.join R)))
    (hl : Memory.compileProg b F ((P.join Q).join R) = some left)
    (hr : Memory.compileProg b F (P.join (Q.join R)) = some right) :
    left.frag = right.frag ∧ left.code = right.code := by
  have compare {A B : Prog C Γ Ω} (equal : A = B)
      (x : CompiledProg b F A) (y : CompiledProg b F B)
      (hx : Memory.compileProg b F A = some x)
      (hy : Memory.compileProg b F B = some y) : x.frag = y.frag ∧ x.code = y.code := by
    cases equal
    have same : x = y := Option.some.inj (hx.symm.trans hy)
    cases same
    exact ⟨rfl,rfl⟩
  exact compare (typed_sequencing_assoc P Q R) left right hl hr

/-- Public recognition is preserved, not merely a supplied left certificate. -/
theorem public_left (right : CompiledProg b F (P.join (Q.join R)))
    (hr : Memory.compileProg b F (P.join (Q.join R)) = some right) :
    ∃ left : CompiledProg b F ((P.join Q).join R),
      Memory.compileProg b F ((P.join Q).join R) = some left := by
  rw [typed_sequencing_assoc]
  exact ⟨right,hr⟩

/-- The same actual final map, state and machine satisfy both whole outputs.
There is no existential reselection or post-failure witness. -/
theorem output_iff (left : CompiledProg b F ((P.join Q).join R))
    (right : CompiledProg b F (P.join (Q.join R)))
    (hl : Memory.compileProg b F ((P.join Q).join R) = some left)
    (hr : Memory.compileProg b F (P.join (Q.join R)) = some right)
    (base selectedBase : Nat → Fin W) (state : State C Γ) (finalState : State C Ω)
    (initial final : Machine) :
    MappedOutput (.memory left) L frame base state initial finalState final selectedBase ↔
    MappedOutput (.memory right) L frame base state initial finalState final selectedBase := by
  have frag := (selected left right hl hr).1
  change (StateRepr L b frame left.frag finalState selectedBase final ∧
    BaseExtends state.H base selectedBase ∧
    GrowsAllocator b frame (allocationCostProg ((P.join Q).join R) state)
      state base initial finalState selectedBase final) ↔ _
  rw [frag,typed_sequencing_assoc]
  rfl

/-- Includes success, internal revert and divergence/fault without applying
raw tail transport to faulting code: the actual selected code is equal. -/
theorem terminal_eq (left : CompiledProg b F ((P.join Q).join R))
    (right : CompiledProg b F (P.join (Q.join R)))
    (hl : Memory.compileProg b F ((P.join Q).join R) = some left)
    (hr : Memory.compileProg b F (P.join (Q.join R)) = some right)
    (machine : Machine) : run left.code machine = run right.code machine := by
  rw [(selected left right hl hr).2]

#print axioms input_iff
#print axioms selected
#print axioms public_left
#print axioms output_iff
#print axioms terminal_eq
end Solidity.Backend.Passes.MemoryAssociation
