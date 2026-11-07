import Solidity.Backend.AbiEntry.BytesGateInterface

/-! A unified actual compiler contract for every existing ABI word kind.
Aggregate decoding and successful ABI entry/body execution remain separate. -/
namespace Solidity.Backend.AbiEntry.Interface
def wordGateOutcome (base : Nat) (kind : Solidity.AbiEntry.Kind) (label word : Fin Evm.W)
    (machine : Evm.Machine) : Evm.Out :=
  if kind.valid word.val then .ok {machine with mem := Evm.upd machine.mem (base+1) (.val label)} 0 else .revert
structure WordGateCertificate
    (program : (C : Contract) → Solidity.AbiEntry.Kind → Fin Evm.W → Prog C RouteCtx RouteCtx) : Prop where
  selected : ∀ (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin Evm.W),
    ∃ result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program C kind label),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program C kind label)=some result
  executed : ∀ (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin Evm.W)
    (result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program C kind label)),
    Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program C kind label)=some result →
    ∀ (machine : Evm.Machine) (word : Fin Evm.W), machine.mem base=.val word →
    Evm.run result.code machine=wordGateOutcome base kind label word machine
end Solidity.Backend.AbiEntry.Interface
