import Solidity.Assurance.NonVacuityH28.Outcomes
import Solidity.Assurance.NonVacuityH28.Callbacks

/-! One actual entry state jointly inhabits calculus callback executions and
scoped compiler inputs. Compiler observations use the deterministic payment;
callback resumption retains its separately observable ledger. -/
namespace Solidity.Assurance.NonVacuityH28
open Solidity Semantics
variable (C : Contract)

/-- Transport of the common entry data, not itself a semantic witness. -/
theorem payment_entry_identification : paymentSource C = funded C := rfl

theorem joint_payment_world :
    Evm.Sim C 1 0 (Evm.Frag.init []) (funded C) paymentMachine ∧
    Prog.run (funded C) (callbackProgram C) = .ok ⟨paid C, List.prefix_refl _⟩ ∧
    Evm.run (Evm.compileProg 0 (callbackProgram C)) paymentMachine = .ok afterPaymentMachine 0 ∧
    ExecP (openPolicy C true) (funded C) (callbackProgram C)
      (.ok ⟨resumed C, List.prefix_refl _⟩) ∧
    ExecP (openPolicy C false) (funded C) (callbackProgram C)
      (.ok ⟨paid C, List.prefix_refl _⟩) ∧
    Evm.netAt (paid C).net 9 = -5 ∧ Evm.netAt (resumed C).net 9 = -7 :=
  ⟨payment_simulation C, rfl, payment_target C,
    callback_program_resume C, callback_program_noCallback C, rfl, rfl⟩

/-- An actual Main compiler application at the same callback-entry state. -/
theorem joint_payment_compiler_application :
    ∃ o, Prog.run (funded C) (callbackProgram C) = .ok o ∧
      (∀ a : Fin Evm.W, a ≠ afterPaymentMachine.self →
        Evm.netAt o.st.net a.1 = (afterPaymentMachine.bal₀ a : Int) - afterPaymentMachine.bal a) ∧
      Evm.netAt o.st.net afterPaymentMachine.self = 0 :=
  Main.compiler_net (payment_fragment C) (joint_payment_world C).1
    (by change 1 ≤ Evm.Lmax; decide) (joint_payment_world C).2.2.1

end Solidity.Assurance.NonVacuityH28
