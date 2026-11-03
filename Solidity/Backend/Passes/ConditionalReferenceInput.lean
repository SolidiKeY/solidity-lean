import Solidity.Backend.Passes.ConditionalReferenceCapture
namespace Solidity.Backend.Passes.ConditionalReferenceCapture
open Evm Evm.Memory Evm.Compiler
theorem input {C : Contract} {Γ : Ctx} {R : RefTy}
    {b L frame : Nat} {F : Frag Γ}
    (name : Var) (condition : Val C Γ .bool) (cc : CompiledVal b F condition)
    (dst yes no : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+(Γ.length+1) ≤ frame) :
    (compiled name condition cc dst yes no hm).Input L frame base state machine := by
  refine ⟨represented,?_,Or.inl rfl⟩
  let n := Γ.length
  change b + max
    (max n (max n (max (max (max n (max n 0)) n) (max (max n (max n 0)) n))))
    (max (max n (max (n+1) 0)) (n+1)) ≤ frame
  dsimp only [n]
  omega

end Solidity.Backend.Passes.ConditionalReferenceCapture
