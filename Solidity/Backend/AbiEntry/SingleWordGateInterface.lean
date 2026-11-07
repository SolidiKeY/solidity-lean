import Solidity.Backend.AbiEntry.HeadGate
import Solidity.Backend.AbiEntry.WordGate

/-! Head then primitive validation for one value parameter. Raw loads are
representation facts; native loading and multi-parameter/aggregate decoding
are separate. The semantic comparison keeps the explicit two-level fuel need. -/
namespace Solidity.Backend.AbiEntry.Interface
def singleWordParams (kind : Solidity.AbiEntry.Kind) : List Solidity.AbiEntry.Param :=
  [{shape := .word kind,loc := .value}]
def rawArgumentWord (input : Solidity.AbiEntry.Input) : Fin Evm.W :=
  ⟨Solidity.AbiEntry.load input.data 4,Solidity.AbiEntry.load_lt _ _⟩
def singleWordOutcome (base : Nat) (kind : Solidity.AbiEntry.Kind) (label word size : Fin Evm.W)
    (machine : Evm.Machine) : Evm.Out :=
  if size.val<36 then .revert else wordGateOutcome base kind label word machine
structure SingleWordGateCertificate
    (program : (C : Contract) → Solidity.AbiEntry.Kind → Fin Evm.W → Prog C RouteCtx RouteCtx) : Prop where
  selected : ∀ (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin Evm.W),
    ∃ result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program C kind label),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program C kind label)=some result
  executed : ∀ (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin Evm.W)
    (result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program C kind label)),
    Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program C kind label)=some result →
    ∀ (machine : Evm.Machine) (word size : Fin Evm.W), machine.mem base=.val word →
    machine.mem (base+1)=.val size →
    Evm.run result.code machine=singleWordOutcome base kind label word size machine
  entry_rejection : ∀ (C : Contract) (base : Nat) (kind : Solidity.AbiEntry.Kind) (label : Fin Evm.W)
    (result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program C kind label)),
    Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program C kind label)=some result →
    ∀ (input : Solidity.AbiEntry.Input) (fuel : Nat) (machine : Evm.Machine) (size : Fin Evm.W),
    machine.mem base=.val (rawArgumentWord input) → machine.mem (base+1)=.val size → size.val=input.size →
    (Evm.run result.code machine=.revert ↔
      Solidity.AbiEntry.entry input (fuel+2) (singleWordParams kind)=.error .revert)
end Solidity.Backend.AbiEntry.Interface
