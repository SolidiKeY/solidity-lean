import Solidity.Backend.Passes.MemoryJoinCost

/-! Exact static frame and reached allocation admission for the public legacy
memory compiler. This does not replace the distinct loop/call certificate
need/Room interfaces or public session-resource semantics. -/
namespace Solidity.Backend.Passes.MemoryJoinFrame
open Evm Evm.Memory Evm.Compiler
variable {C : Contract}

theorem frame_start {Γ Δ : Ctx} (P : Prog C Γ Δ) : Γ.length ≤ frameNeedProg P := by
  cases P with
  | nil => exact Nat.le_refl _
  | cons s P =>
    change Γ.length ≤ max (frameNeedStmt s) (frameNeedProg P)
    exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)

theorem frame_join : {Γ Δ Ξ : Ctx} → (P : Prog C Γ Δ) → (Q : Prog C Δ Ξ) →
    frameNeedProg (P.join Q) = max (frameNeedProg P) (frameNeedProg Q)
  | _,_,_,.nil,Q => by
    change frameNeedProg Q = max _ (frameNeedProg Q)
    exact (Nat.max_eq_right (frame_start Q)).symm
  | _,_,_,.cons s P,Q => by
    change max (frameNeedStmt s) (frameNeedProg (P.join Q)) =
      max (max (frameNeedStmt s) (frameNeedProg P)) (frameNeedProg Q)
    rw [frame_join P Q,Nat.max_assoc]

theorem input_iff {b L frame : Nat} {Γ Δ Ξ : Ctx} {F : Frag Γ}
    {P : Prog C Γ Δ} {Q : Prog C Δ Ξ} (joined : CompiledProg b F (P.join Q))
    (base : Nat → Fin W) (state : State C Γ) (machine : Machine) :
    (Compilation.memory joined).Input L frame base state machine ↔
      StateRepr L b frame F state base machine ∧
      b + frameNeedProg P ≤ frame ∧ b + frameNeedProg Q ≤ frame ∧
      AllocationInput b frame (allocationCostProg P state +
        match P.run state with | .ok out => allocationCostProg Q out.st | .error _ => 0)
        state base machine := by
  change (StateRepr L b frame F state base machine ∧
    b + frameNeedProg (P.join Q) ≤ frame ∧
    AllocationInput b frame (allocationCostProg (P.join Q) state) state base machine) ↔ _
  rw [frame_join,MemoryJoinCost.cost_join]
  constructor
  · rintro ⟨represented,capacity,budget⟩
    exact ⟨represented,by omega,by omega,budget⟩
  · rintro ⟨represented,leftCapacity,rightCapacity,budget⟩
    exact ⟨represented,by omega,budget⟩

theorem left_input {b L frame : Nat} {Γ Δ Ξ : Ctx} {F : Frag Γ}
    {P : Prog C Γ Δ} {Q : Prog C Δ Ξ}
    (left : CompiledProg b F P) (joined : CompiledProg b F (P.join Q))
    {base : Nat → Fin W} {state : State C Γ} {machine : Machine}
    (admitted : (Compilation.memory joined).Input L frame base state machine) :
    (Compilation.memory left).Input L frame base state machine := by
  obtain ⟨represented,leftCapacity,_,budget⟩ := (input_iff joined base state machine).mp admitted
  exact ⟨represented,leftCapacity,budget.of_le (Nat.le_add_right _ _)⟩

/-- A real joined Input discharges the per-run mapped link. Frame demand is
static; allocation capacity is transported only after actual prefix success. -/
theorem boundary_link {b L frame : Nat} {Γ Δ Ξ : Ctx} {F : Frag Γ}
    {P : Prog C Γ Δ} {Q : Prog C Δ Ξ}
    (left : CompiledProg b F P) (right : CompiledProg b left.frag Q)
    (joined : CompiledProg b F (P.join Q))
    {base : Nat → Fin W} {state : State C Γ} {machine : Machine}
    (admitted : (Compilation.memory joined).Input L frame base state machine) :
    MappedBoundaryLink (.memory left) (.memory right) L frame base state machine := by
  intro out middle selected reached target mapped
  obtain ⟨_,_,rightCapacity,budget⟩ := (input_iff joined base state machine).mp admitted
  have originalBudget : AllocationInput b frame (allocationCostProg (P.join Q) state)
      state base machine := by
    rw [MemoryJoinCost.cost_join]
    exact budget
  exact ⟨mapped.1,rightCapacity,
    MemoryJoinCost.suffix_allocation_input P Q state out reached originalBudget mapped.2.2⟩

/-- All supplied certificates are actual public compiler selections. The
joined admission produces both the initial prefix Input and mapped link. -/
theorem public_admission {b L frame : Nat} {Γ Δ Ξ : Ctx} {F : Frag Γ}
    {P : Prog C Γ Δ} {Q : Prog C Δ Ξ}
    (left : CompiledProg b F P) (right : CompiledProg b left.frag Q)
    (hl : Memory.compileProg b F P = some left)
    (hr : Memory.compileProg b left.frag Q = some right)
    (base : Nat → Fin W) (state : State C Γ) (machine : Machine)
    (represented : StateRepr L b frame F state base machine)
    (leftCapacity : b + frameNeedProg P ≤ frame)
    (rightCapacity : b + frameNeedProg Q ≤ frame)
    (budget : AllocationInput b frame (allocationCostProg (P.join Q) state) state base machine) :
    ∃ joined : CompiledProg b F (P.join Q),
      Memory.compileProg b F (P.join Q) = some joined ∧ joined.frag = right.frag ∧
      joined.code = left.code ++ right.code ∧
      (Compilation.memory joined).Input L frame base state machine ∧
      (Compilation.memory left).Input L frame base state machine ∧
      MappedBoundaryLink (.memory left) (.memory right) L frame base state machine := by
  obtain ⟨joined,accepted,frag,code,_⟩ := MemoryJoinCost.public_join left right hl hr state
  have admitted : (Compilation.memory joined).Input L frame base state machine := by
    refine ⟨represented,?_,budget⟩
    change b + frameNeedProg (P.join Q) ≤ frame
    rw [frame_join]
    omega
  exact ⟨joined,accepted,frag,code,admitted,left_input left joined admitted,
    boundary_link left right joined admitted⟩

#print axioms frame_join
#print axioms input_iff
#print axioms boundary_link
#print axioms public_admission
end Solidity.Backend.Passes.MemoryJoinFrame
