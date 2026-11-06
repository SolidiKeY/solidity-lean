import Solidity.Evm.Compiler

/-! Intrinsic value-gate compilation contracts. Selection uses the existing
public checked compiler; gas, ABI failure bytes, selector dispatch and physical
Source origin are separate obligations. No entry-admission predicate is added. -/
namespace Solidity.Backend.AbiEntry.Interface

structure ValueGateCertificate
    (program : {C : Contract} → {Γ : Ctx} → Bool → Prog C Γ Γ) : Prop where
  selected : ∀ {C : Contract} {Γ : Ctx} (base : Nat) (frag : Evm.Frag Γ) (payable : Bool),
    ∃ compiled : Evm.Compiler.Compilation base frag (program (C := C) payable),
      Evm.Compiler.compile base frag (program payable)=some compiled ∧
      compiled.code=if payable then [] else
        [.callvalue,.push (.val (Evm.wmod 0)),.eq,.jumpi 1,.revert]
  executed : ∀ {C : Contract} {Γ : Ctx} (base : Nat) (frag : Evm.Frag Γ) (payable : Bool)
    (compiled : Evm.Compiler.Compilation base frag (program (C := C) payable)),
    Evm.Compiler.compile base frag (program payable)=some compiled →
    ∀ machine : Evm.Machine,
      Evm.run compiled.code machine=
        if payable || decide (machine.callvalue.val=0) then .ok machine 0 else .revert

end Solidity.Backend.AbiEntry.Interface
