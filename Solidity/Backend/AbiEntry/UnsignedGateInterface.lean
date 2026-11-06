import Solidity.Backend.AbiEntry.WordValidation
import Solidity.Backend.AbiEntry.SelectorRoutes

/-! Actual unsigned word validation through the public intrinsic compiler.
Raw loading, aggregate offsets and signed/fixed-byte validators are separate. -/
namespace Solidity.Backend.AbiEntry.Interface
def unsignedGateOutcome (base bound : Nat) (label word : Fin Evm.W) (machine : Evm.Machine) : Evm.Out :=
  if word.val<bound then .ok {machine with mem := Evm.upd machine.mem (base+1) (.val label)} 0 else .revert
structure UnsignedGateCertificate
    (program : (C : Contract) → Nat → Fin Evm.W → Prog C RouteCtx RouteCtx) : Prop where
  selected : ∀ (C : Contract) (base bound : Nat) (label : Fin Evm.W),
    ∃ result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program C bound label),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program C bound label)=some result
  executed : ∀ (C : Contract) (base bound : Nat) (label : Fin Evm.W)
    (result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program C bound label)),
    Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program C bound label)=some result →
    ∀ (machine : Evm.Machine) (word : Fin Evm.W), machine.mem base=.val word →
    Evm.run result.code machine=unsignedGateOutcome base bound label word machine
end Solidity.Backend.AbiEntry.Interface
