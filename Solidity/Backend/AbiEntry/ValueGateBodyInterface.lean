import Solidity.Backend.AbiEntry.ValueGateInterface

/-! Intrinsic value-gate/body composition for the existing core classifier.
This supported family does not stand for all admitted Source entry bodies.
No body result, selected artifact or target run is assumed. -/
namespace Solidity.Backend.AbiEntry.Interface

structure ValueGateBodyCertificate
    (guard : {C : Contract} → {Γ Δ : Ctx} → Bool → Prog C Γ Δ → Prog C Γ Δ) : Prop where
  selected : ∀ {C : Contract} {Γ Δ : Ctx} (base : Nat) (frag : Evm.Frag Γ)
    (body : Prog C Γ Δ) (payable : Bool) (outFrag : Evm.Frag Δ),
    Evm.inFragP frag body=some outFrag →
    ∃ (whole : Evm.Compiler.Compilation base frag (guard payable body))
      (selectedBody : Evm.Compiler.Compilation base frag body),
      Evm.Compiler.compile base frag (guard payable body)=some whole ∧
      Evm.Compiler.compile base frag body=some selectedBody ∧
      whole.code=(if payable then [] else
        [.callvalue,.push (.val (Evm.wmod 0)),.eq,.jumpi 1,.revert])++selectedBody.code
  executed : ∀ {C : Contract} {Γ Δ : Ctx} (base : Nat) (frag : Evm.Frag Γ)
    (body : Prog C Γ Δ) (payable : Bool) (outFrag : Evm.Frag Δ),
    Evm.inFragP frag body=some outFrag →
    ∀ (whole : Evm.Compiler.Compilation base frag (guard payable body))
      (selectedBody : Evm.Compiler.Compilation base frag body),
      Evm.Compiler.compile base frag (guard payable body)=some whole →
      Evm.Compiler.compile base frag body=some selectedBody →
      ∀ machine : Evm.Machine,
        Evm.run whole.code machine=if payable || decide (machine.callvalue.val=0)
          then Evm.run selectedBody.code machine else .revert

end Solidity.Backend.AbiEntry.Interface
