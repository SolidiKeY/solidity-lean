import Solidity.Evm.Compiler
import Solidity.Evm.Correct

/-! Join removal for actual core compilations from represented typed inputs,
under the existing compiler's unchanged allocation bound. These are input
representation/resource facts, not a normal-return or execution premise.
Source/native realization of that representation remains separate. -/
namespace Solidity.Backend.AbiEntry.Interface
structure CoreJoinCertificate : Prop where
  selected : ∀ {C : Contract} {Γ Δ : Ctx} (base : Nat) (frag : Evm.Frag Γ)
    (body : Prog C Γ Δ) (outFrag : Evm.Frag Δ), Evm.inFragP frag body=some outFrag →
    ∃ result : Evm.Compiler.Compilation base frag body, Evm.Compiler.compile base frag body=some result
  joined : ∀ {C : Contract} {Γ Δ : Ctx} (L base : Nat) (frag : Evm.Frag Γ)
    (body : Prog C Γ Δ) (outFrag : Evm.Frag Δ), Evm.inFragP frag body=some outFrag →
    ∀ (result : Evm.Compiler.Compilation base frag body), Evm.Compiler.compile base frag body=some result →
    ∀ (state : State C Γ) (machine : Evm.Machine), Evm.Sim C L base frag state machine →
    L+Evm.Prog.pushes body≤Evm.Lmax → ∀ rest : List Evm.Instr,
      Evm.run (result.code++[.jump rest.length]++rest) machine=Evm.run result.code machine
end Solidity.Backend.AbiEntry.Interface
