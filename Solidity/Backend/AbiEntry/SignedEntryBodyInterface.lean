import Solidity.Backend.AbiEntry.SignedBinding

/-! One actual compiler program checks value, validates and binds signed input,
then runs an existing core-admitted typed body. Native/Source adequacy is separate. -/
namespace Solidity.Backend.AbiEntry.Interface
structure SignedEntryBodyCertificate
    (program : {C : Contract} → {Δ : Ctx} → Nat → Bool → Fin Evm.W →
      Prog C SignedBoundCtx Δ → Prog C RouteCtx Δ) : Prop where
  selected : ∀ {C : Contract} {Δ : Ctx} (base bits : Nat) (payable : Bool) (label : Fin Evm.W)
    (body : Prog C SignedBoundCtx Δ) (outFrag : Evm.Frag Δ),
    Evm.inFragP (Evm.Frag.init SignedBoundCtx) body=some outFrag →
    ∃ (whole : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program bits payable label body))
      (back : Evm.Compiler.Compilation base (Evm.Frag.init SignedBoundCtx) body),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program bits payable label body)=some whole ∧
      Evm.Compiler.compile base (Evm.Frag.init SignedBoundCtx) body=some back
  executed : ∀ {C : Contract} {Δ : Ctx} (base bits : Nat) (payable : Bool) (label : Fin Evm.W)
    (body : Prog C SignedBoundCtx Δ) (outFrag : Evm.Frag Δ),
    Evm.inFragP (Evm.Frag.init SignedBoundCtx) body=some outFrag →
    ∀ (whole : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program bits payable label body))
      (back : Evm.Compiler.Compilation base (Evm.Frag.init SignedBoundCtx) body),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program bits payable label body)=some whole →
      Evm.Compiler.compile base (Evm.Frag.init SignedBoundCtx) body=some back →
      ∀ (machine : Evm.Machine) (word size : Fin Evm.W), machine.mem base=.val word →
      machine.mem (base+1)=.val size →
      Evm.run whole.code machine=if payable || decide (machine.callvalue.val=0) then
        if size.val<36 then .revert else if (Solidity.AbiEntry.Kind.int bits).valid word.val then
          Evm.run back.code (signedBoundMachine base label word machine) else .revert else .revert
  early_rejection : ∀ {C : Contract} {Δ : Ctx} (base bits : Nat) (payable : Bool) (label : Fin Evm.W)
    (body : Prog C SignedBoundCtx Δ) (outFrag : Evm.Frag Δ),
    Evm.inFragP (Evm.Frag.init SignedBoundCtx) body=some outFrag →
    ∀ whole : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program bits payable label body),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program bits payable label body)=some whole →
      ∀ machine : Evm.Machine, (payable || decide (machine.callvalue.val=0))=false →
      Evm.run whole.code machine=.revert

end Solidity.Backend.AbiEntry.Interface
