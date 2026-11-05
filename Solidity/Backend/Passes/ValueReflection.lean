import Solidity.Backend.Passes.ValueCertificate

/-! Successful selected value execution reflects its independent intrinsic
evaluation and exact representing word under the original full state input. -/
namespace Solidity.Backend.Passes.ValueReflection
open Evm Evm.Memory
variable {C : Contract} {Γ : Ctx} {p : PrimTy}
/-- Reflect a concrete successful run using the full original typed input.
No final value or preservation equation is assumed. -/
theorem success {b L frame : Nat} {F : Frag Γ} {e : Val C Γ p}
    (compiled : CompiledVal b F e) {state : State C Γ}
    {base : Nat → Fin W} {machine : Machine} (word : Word)
    (represented : StateRepr L b frame F state base machine)
    (actual : run compiled.code machine = .ok (machine.push word) 0) :
    ∃ value, e.evalT state = .ok value ∧ ReprV p value word := by
  rcases compiled.cert.correct represented with
    ⟨value, selected, source, relation, target⟩ | ⟨_, target⟩
  · have machines : machine.push selected = machine.push word :=
      (Out.ok.inj (target.symm.trans actual)).1
    have heads : selected = word :=
      (List.cons.inj (congrArg Machine.stack machines)).1
    cases heads
    exact ⟨value, source, relation⟩
  · rw [actual] at target
    cases target

/-- info: 'Solidity.Backend.Passes.ValueReflection.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms success
end Solidity.Backend.Passes.ValueReflection
