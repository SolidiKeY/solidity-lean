import Solidity.Backend.AbiEntry.HeadCheck
import Solidity.Backend.AbiEntry.SelectorRoutes

/-! Actual typed head-span guard, not successful argument decoding. The full
semantic extent is retained even when no target word can represent it. -/
namespace Solidity.Backend.AbiEntry.Interface
def headGateOutcome (base : Nat) (parameters : List Solidity.AbiEntry.Param) (label size : Fin Evm.W)
    (machine : Evm.Machine) : Evm.Out :=
  if size.val<HeadCheck.need parameters then .revert else
    .ok {machine with mem := Evm.upd machine.mem (base+1) (.val label)} 0
structure HeadGateCertificate
    (program : (C : Contract) → List Solidity.AbiEntry.Param → Fin Evm.W → Prog C RouteCtx RouteCtx) : Prop where
  selected : ∀ (C : Contract) (base : Nat) (parameters : List Solidity.AbiEntry.Param) (label : Fin Evm.W),
    ∃ result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program C parameters label),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program C parameters label)=some result
  executed : ∀ (C : Contract) (base : Nat) (parameters : List Solidity.AbiEntry.Param) (label : Fin Evm.W)
    (result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program C parameters label)),
    Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program C parameters label)=some result →
    ∀ (machine : Evm.Machine) (size : Fin Evm.W), machine.mem (base+1)=.val size →
    Evm.run result.code machine=headGateOutcome base parameters label size machine
end Solidity.Backend.AbiEntry.Interface
