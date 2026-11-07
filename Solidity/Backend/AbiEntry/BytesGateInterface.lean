import Solidity.Backend.AbiEntry.SignedGate

/-! Actual fixed-byte low-padding validation. Every semantic size is kept;
input words are validated without cleanup or native-loading assumptions. -/
namespace Solidity.Backend.AbiEntry.Interface
def bytesGateOutcome (base size : Nat) (label word : Fin Evm.W) (machine : Evm.Machine) : Evm.Out :=
  if (Solidity.AbiEntry.Kind.fixedBytes size).valid word.val then
    .ok {machine with mem := Evm.upd machine.mem (base+1) (.val label)} 0 else .revert
structure BytesGateCertificate
    (program : (C : Contract) → Nat → Fin Evm.W → Prog C RouteCtx RouteCtx) : Prop where
  selected : ∀ (C : Contract) (base size : Nat) (label : Fin Evm.W),
    ∃ result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program C size label),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program C size label)=some result
  executed : ∀ (C : Contract) (base size : Nat) (label : Fin Evm.W)
    (result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program C size label)),
    Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program C size label)=some result →
    ∀ (machine : Evm.Machine) (word : Fin Evm.W), machine.mem base=.val word →
    Evm.run result.code machine=bytesGateOutcome base size label word machine
end Solidity.Backend.AbiEntry.Interface
