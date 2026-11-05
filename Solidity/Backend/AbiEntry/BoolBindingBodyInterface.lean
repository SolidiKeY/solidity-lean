import Solidity.Backend.AbiEntry.BoolBinding

/-! Validation, bool binding and a typed body through one public compilation.
The body is accepted by the existing core classifier; no target run or body
result is a premise. Source/native adequacy is not asserted by this contract. -/
namespace Solidity.Backend.AbiEntry.Interface
structure BoolBindingBodyCertificate
    (program : {C : Contract} → {Δ : Ctx} → Fin Evm.W →
      Prog C BoolBoundCtx Δ → Prog C RouteCtx Δ) : Prop where
  selected : ∀ {C : Contract} {Δ : Ctx} (base : Nat) (label : Fin Evm.W)
    (body : Prog C BoolBoundCtx Δ) (outFrag : Evm.Frag Δ),
    Evm.inFragP (Evm.Frag.init BoolBoundCtx) body=some outFrag →
    ∃ (whole : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program label body))
      (back : Evm.Compiler.Compilation base (Evm.Frag.init BoolBoundCtx) body),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program label body)=some whole ∧
      Evm.Compiler.compile base (Evm.Frag.init BoolBoundCtx) body=some back ∧
      whole.code=Evm.compileProg base (BoolBinding.program C label)++back.code
  executed : ∀ {C : Contract} {Δ : Ctx} (base : Nat) (label : Fin Evm.W)
    (body : Prog C BoolBoundCtx Δ) (outFrag : Evm.Frag Δ),
    Evm.inFragP (Evm.Frag.init BoolBoundCtx) body=some outFrag →
    ∀ (whole : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program label body))
      (back : Evm.Compiler.Compilation base (Evm.Frag.init BoolBoundCtx) body),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program label body)=some whole →
      Evm.Compiler.compile base (Evm.Frag.init BoolBoundCtx) body=some back →
      ∀ (machine : Evm.Machine) (word size : Fin Evm.W), machine.mem base=.val word →
      machine.mem (base+1)=.val size →
      Evm.run whole.code machine=if size.val<36 then .revert else
        if Solidity.AbiEntry.Kind.bool.valid word.val then
          Evm.run back.code (boolBoundMachine base label word machine) else .revert
end Solidity.Backend.AbiEntry.Interface
