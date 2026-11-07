import Solidity.Backend.Payments.Versioned

/-!
# Actual checked-entry success on the supported core fragment

Guards the reject-all/always-revert regression that a conditional agreement
claim alone cannot exclude. The existing fragment certificate makes the actual
`Compiler.compile` return a result; the published payment-exact success theorem
then supplies its successful execution, protected stack and representation.
No new admission predicate, success oracle or frozen-interface change is used.
-/
namespace Solidity.Evm.Compiler

variable {C : Contract} {Γ Δ : Ctx} {b L : Nat}
  {F : Frag Γ} {F' : Frag Δ} {P : Solidity.Prog C Γ Δ}
  {σ : State C Γ} {m : Machine}

/-- Every accepted core fragment is returned by the actual checked entry. -/
theorem compile_core_some (fragment : inFragP F P = some F') :
    compile b F P = some (.core F' fragment) := by
  unfold compile
  split <;> grind

/-- Actual compiler acceptance and execution success for all supported core
inputs, retaining the original simulation/resource/source-success premises. -/
theorem compile_core_success (fragment : inFragP F P = some F')
    (represented : Sim C L b F σ m) (room : L + Evm.Prog.pushes P ≤ Lmax)
    {o : Solidity.Out C σ.H Δ} (source : Solidity.Prog.run σ P = .ok o) :
    ∃ compiled : Compilation b F P, compile b F P = some compiled ∧
      ∃ m', run compiled.code m = .ok m' 0 ∧ m'.stack = m.stack ∧
        Sim C (L + Evm.Prog.pushes P) b F' o.st m' := by
  refine ⟨.core F' fragment, compile_core_some fragment, ?_⟩
  exact Payments.compile_success fragment represented room source

/-- info: 'Solidity.Evm.Compiler.compile_core_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compile_core_some

/-- info: 'Solidity.Evm.Compiler.compile_core_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compile_core_success

end Solidity.Evm.Compiler
