import Solidity.Backend.AbiEntry.UIntBinding

/-! Validation, uint binding and a typed body through one public compilation.
The body is accepted by the existing core classifier; no target run or body
result is a premise. Source/native adequacy is not asserted by this contract. -/
namespace Solidity.Backend.AbiEntry.Interface
structure UIntBindingBodyCertificate
    (program : {C : Contract} → {Δ : Ctx} → Nat → Fin Evm.W →
      Prog C UIntBoundCtx Δ → Prog C RouteCtx Δ) : Prop where
  selected : ∀ {C : Contract} {Δ : Ctx} (base bits : Nat) (label : Fin Evm.W)
    (body : Prog C UIntBoundCtx Δ) (outFrag : Evm.Frag Δ),
    Evm.inFragP (Evm.Frag.init UIntBoundCtx) body=some outFrag →
    ∃ (whole : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program bits label body))
      (back : Evm.Compiler.Compilation base (Evm.Frag.init UIntBoundCtx) body),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program bits label body)=some whole ∧
      Evm.Compiler.compile base (Evm.Frag.init UIntBoundCtx) body=some back ∧
      whole.code=Evm.compileProg base (UIntBinding.program C bits label)++back.code
  executed : ∀ {C : Contract} {Δ : Ctx} (base bits : Nat) (label : Fin Evm.W)
    (body : Prog C UIntBoundCtx Δ) (outFrag : Evm.Frag Δ),
    Evm.inFragP (Evm.Frag.init UIntBoundCtx) body=some outFrag →
    ∀ (whole : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program bits label body))
      (back : Evm.Compiler.Compilation base (Evm.Frag.init UIntBoundCtx) body),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program bits label body)=some whole →
      Evm.Compiler.compile base (Evm.Frag.init UIntBoundCtx) body=some back →
      ∀ (machine : Evm.Machine) (word size : Fin Evm.W), machine.mem base=.val word →
      machine.mem (base+1)=.val size →
      Evm.run whole.code machine=if size.val<36 then .revert else
        if (Solidity.AbiEntry.Kind.uint bits).valid word.val then
          Evm.run back.code (uintBoundMachine base label word machine) else .revert
end Solidity.Backend.AbiEntry.Interface
