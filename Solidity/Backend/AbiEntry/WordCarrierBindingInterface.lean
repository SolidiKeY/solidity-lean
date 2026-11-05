import Solidity.Backend.AbiEntry.UIntBinding

/-! Binding of an accepted primitive ABI word into the existing uint carrier.
This is a raw representation local, not a replacement for Boolean/signed locals
or a Source signature-erasure theorem. Native loading remains explicit. -/
namespace Solidity.Backend.AbiEntry.Interface

def wordCarrierOutcome (base : Nat) (kind : Solidity.AbiEntry.Kind)
    (label word size : Fin Evm.W) (machine : Evm.Machine) : Evm.Out :=
  if size.val<36 then .revert else
  if kind.valid word.val then .ok (uintBoundMachine base label word machine) 0 else .revert

structure WordCarrierBindingCertificate
    (program : (C : Contract) → Solidity.AbiEntry.Kind → Fin Evm.W → Prog C RouteCtx UIntBoundCtx) : Prop where
  selected : ∀ (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin Evm.W),
    ∃ result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program C kind label),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program C kind label)=some result
  executed : ∀ (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin Evm.W)
    (result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program C kind label)),
    Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program C kind label)=some result →
    ∀ (machine : Evm.Machine) (word size : Fin Evm.W), machine.mem base=.val word →
    machine.mem (base+1)=.val size →
    Evm.run result.code machine=wordCarrierOutcome base kind label word size machine
  entry_rejection : ∀ (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin Evm.W)
    (result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program C kind label)),
    Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program C kind label)=some result →
    ∀ (input : Solidity.AbiEntry.Input) (fuel : Nat) (machine : Evm.Machine) (size : Fin Evm.W),
    machine.mem base=.val (rawArgumentWord input) → machine.mem (base+1)=.val size → size.val=input.size →
    (Evm.run result.code machine=.revert ↔
      Solidity.AbiEntry.entry input (fuel+2) (singleWordParams kind)=.error .revert)
end Solidity.Backend.AbiEntry.Interface
