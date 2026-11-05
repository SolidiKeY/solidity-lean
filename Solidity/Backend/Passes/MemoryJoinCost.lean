import Solidity.Backend.Passes.MemoryCompilerSequence
import Solidity.Backend.Passes.MappedSequence

/-! Exact reached-prefix cost for the existing intrinsic program and public
memory compiler join. This is the existing allocation-cell cost, not public
session gas or Source/bytecode adequacy. -/
namespace Solidity.Backend.Passes.MemoryJoinCost
open Evm Evm.Memory Evm.Compiler
variable {C : Contract}

theorem cost_join : {Γ Δ Ξ : Ctx} → (P : Prog C Γ Δ) → (Q : Prog C Δ Ξ) →
    (state : State C Γ) →
    allocationCostProg (P.join Q) state = allocationCostProg P state +
      match P.run state with
      | .ok out => allocationCostProg Q out.st
      | .error _ => 0
  | _,_,_,.nil,Q,state => by
    simp only [Prog.join,allocationCostProg,Prog.run_nil,Nat.zero_add]
  | _,_,_,.cons s P,Q,state => by
    rw [Prog.join,allocationCostProg_cons,allocationCostProg_cons]
    cases hs : s.run state with
    | error err =>
      have stopped : (Prog.cons s P).run state = .error err := Prog.run_cons_error hs
      simp only [stopped,Nat.add_zero]
    | ok out =>
      dsimp only
      rw [cost_join P Q out.st,Prog.run_cons_ok hs]
      cases hp : P.run out.st <;> simp only [Except.map,Nat.add_assoc]

theorem successful_prefix {Γ Δ Ξ : Ctx} (P : Prog C Γ Δ) (Q : Prog C Δ Ξ)
    (state : State C Γ) (out : Solidity.Out C state.H Δ)
    (reached : P.run state = .ok out) :
    allocationCostProg (P.join Q) state =
      allocationCostProg P state + allocationCostProg Q out.st := by
  simp only [cost_join,reached]

theorem failed_prefix {Γ Δ Ξ : Ctx} (P : Prog C Γ Δ) (Q : Prog C Δ Ξ)
    (state : State C Γ) (halt : THalt) (failed : P.run state = .error halt) :
    allocationCostProg (P.join Q) state = allocationCostProg P state := by
  simp only [cost_join,failed,Nat.add_zero]

/-- The joined certificate is selected by compileProg itself. Its suffix
cost is charged only at the actual successful prefix's typed state. -/
theorem public_join {b : Nat} {Γ Δ Ξ : Ctx} {F : Frag Γ}
    {P : Prog C Γ Δ} {Q : Prog C Δ Ξ}
    (left : CompiledProg b F P) (right : CompiledProg b left.frag Q)
    (hl : Memory.compileProg b F P = some left)
    (hr : Memory.compileProg b left.frag Q = some right) (state : State C Γ) :
    ∃ joined : CompiledProg b F (P.join Q),
      Memory.compileProg b F (P.join Q) = some joined ∧ joined.frag = right.frag ∧
      joined.code = left.code ++ right.code ∧
      joined.cert.cost state = left.cert.cost state +
        match P.run state with
        | .ok out => right.cert.cost out.st
        | .error _ => 0 := by
  obtain ⟨joined,accepted,frag,code⟩ := memory_compile_join left right hl hr
  exact ⟨joined,accepted,frag,code,cost_join P Q state⟩

/-- An initial joined allocation budget transports through actual prefix
growth to the suffix budget at its selected map. Full frame/StateRepr and
suffix compiler acceptance remain separate, unchanged obligations. -/
theorem suffix_allocation_input {b frame : Nat} {Γ Δ Ξ : Ctx}
    (P : Prog C Γ Δ) (Q : Prog C Δ Ξ) (state : State C Γ)
    (out : Solidity.Out C state.H Δ) (reached : P.run state = .ok out)
    {base selected : Nat → Fin W} {initial middle : Machine}
    (budget : AllocationInput b frame (allocationCostProg (P.join Q) state)
      state base initial)
    (growth : GrowsAllocator b frame (allocationCostProg P state)
      state base initial out.st selected middle) :
    AllocationInput b frame (allocationCostProg Q out.st) out.st selected middle := by
  rw [successful_prefix P Q state out reached] at budget
  exact growth.nextInput budget

#print axioms cost_join
#print axioms public_join
#print axioms suffix_allocation_input
end Solidity.Backend.Passes.MemoryJoinCost
