import Solidity.Backend.AbiEntry.WordCarrierEntryBody

/-! An actual selector guard on a chosen intrinsic uint local, followed by a
publicly selected core body. This supports a single-match/reject continuation;
short-calldata routing, selector loading and Source table authenticity remain
separate obligations. No desired body run or result is a premise. -/
namespace Solidity.Backend.AbiEntry.Interface
structure SelectorGateBodyCertificate
    (program : {C : Contract} → {Γ Δ : Ctx} → Idx Γ (.val .uint) → Fin Evm.W →
      Prog C Γ Δ → Prog C Γ Δ) : Prop where
  selected : ∀ {C : Contract} {Γ Δ : Ctx} (base : Nat) (frag : Evm.Frag Γ)
    (index : Idx Γ (.val .uint)) (tag : Fin Evm.W) (body : Prog C Γ Δ) (outFrag : Evm.Frag Δ),
    Evm.inFragP frag body=some outFrag →
    ∃ (whole : Evm.Compiler.Compilation base frag (program index tag body))
      (back : Evm.Compiler.Compilation base frag body),
      Evm.Compiler.compile base frag (program index tag body)=some whole ∧
      Evm.Compiler.compile base frag body=some back
  executed : ∀ {C : Contract} {Γ Δ : Ctx} (base : Nat) (frag : Evm.Frag Γ)
    (index : Idx Γ (.val .uint)) (tag : Fin Evm.W) (body : Prog C Γ Δ) (outFrag : Evm.Frag Δ),
    Evm.inFragP frag body=some outFrag →
    ∀ (whole : Evm.Compiler.Compilation base frag (program index tag body))
      (back : Evm.Compiler.Compilation base frag body),
      Evm.Compiler.compile base frag (program index tag body)=some whole →
      Evm.Compiler.compile base frag body=some back →
      ∀ (machine : Evm.Machine) (selector : Fin Evm.W),
      machine.mem (Evm.cellOf base index)=.val selector →
      Evm.run whole.code machine=if tag.val=selector.val then Evm.run back.code machine else .revert
end Solidity.Backend.AbiEntry.Interface
