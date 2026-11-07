import Solidity.Backend.AbiEntry.UnsignedGate

/-! Signed cleanup validation through the existing public compiler. Words
retain their unsigned representation; accepted sign-extended values survive. -/
namespace Solidity.Backend.AbiEntry.Interface
def signedGateOutcome (base bits : Nat) (label word : Fin Evm.W) (machine : Evm.Machine) : Evm.Out :=
  if (Solidity.AbiEntry.Kind.int bits).valid word.val then
    .ok {machine with mem := Evm.upd machine.mem (base+1) (.val label)} 0 else .revert
structure SignedGateCertificate
    (program : (C : Contract) → Nat → Fin Evm.W → Prog C RouteCtx RouteCtx) : Prop where
  selected : ∀ (C : Contract) (base bits : Nat) (label : Fin Evm.W),
    ∃ result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program C bits label),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program C bits label)=some result
  executed : ∀ (C : Contract) (base bits : Nat) (label : Fin Evm.W)
    (result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program C bits label)),
    Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program C bits label)=some result →
    ∀ (machine : Evm.Machine) (word : Fin Evm.W), machine.mem base=.val word →
    Evm.run result.code machine=signedGateOutcome base bits label word machine
end Solidity.Backend.AbiEntry.Interface
