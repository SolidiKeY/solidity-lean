import Solidity.Backend.AbiEntry.WordCarrierBinding

/-! One existing compiler program checks value, validates primitive input, binds
its raw uint carrier and runs an existing core-admitted typed body. Source
signature/body linkage and native loading are separate obligations. -/
namespace Solidity.Backend.AbiEntry.Interface
structure WordCarrierEntryBodyCertificate
    (program : {C : Contract} → {Δ : Ctx} → Solidity.AbiEntry.Kind → Bool → Fin Evm.W →
      Prog C UIntBoundCtx Δ → Prog C RouteCtx Δ) : Prop where
  selected : ∀ {C : Contract} {Δ : Ctx} (base : Nat) (kind : Solidity.AbiEntry.Kind) (payable : Bool) (label : Fin Evm.W)
    (body : Prog C UIntBoundCtx Δ) (outFrag : Evm.Frag Δ),
    Evm.inFragP (Evm.Frag.init UIntBoundCtx) body=some outFrag →
    ∃ (whole : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program kind payable label body))
      (back : Evm.Compiler.Compilation base (Evm.Frag.init UIntBoundCtx) body),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program kind payable label body)=some whole ∧
      Evm.Compiler.compile base (Evm.Frag.init UIntBoundCtx) body=some back
  executed : ∀ {C : Contract} {Δ : Ctx} (base : Nat) (kind : Solidity.AbiEntry.Kind) (payable : Bool) (label : Fin Evm.W)
    (body : Prog C UIntBoundCtx Δ) (outFrag : Evm.Frag Δ),
    Evm.inFragP (Evm.Frag.init UIntBoundCtx) body=some outFrag →
    ∀ (whole : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program kind payable label body))
      (back : Evm.Compiler.Compilation base (Evm.Frag.init UIntBoundCtx) body),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program kind payable label body)=some whole →
      Evm.Compiler.compile base (Evm.Frag.init UIntBoundCtx) body=some back →
      ∀ (machine : Evm.Machine) (word size : Fin Evm.W), machine.mem base=.val word →
      machine.mem (base+1)=.val size →
      Evm.run whole.code machine=if payable || decide (machine.callvalue.val=0) then
        if size.val<36 then .revert else if kind.valid word.val then
          Evm.run back.code (uintBoundMachine base label word machine) else .revert else .revert
  early_rejection : ∀ {C : Contract} {Δ : Ctx} (base : Nat) (kind : Solidity.AbiEntry.Kind) (payable : Bool) (label : Fin Evm.W)
    (body : Prog C UIntBoundCtx Δ) (outFrag : Evm.Frag Δ),
    Evm.inFragP (Evm.Frag.init UIntBoundCtx) body=some outFrag →
    ∀ whole : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program kind payable label body),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program kind payable label body)=some whole →
      ∀ machine : Evm.Machine, (payable || decide (machine.callvalue.val=0))=false →
      Evm.run whole.code machine=.revert

end Solidity.Backend.AbiEntry.Interface
