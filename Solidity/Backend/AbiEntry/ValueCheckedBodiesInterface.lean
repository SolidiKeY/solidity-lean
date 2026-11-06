import Solidity.Backend.AbiEntry.UIntBindingBody
import Solidity.Backend.AbiEntry.BoolBindingBody

/-! Value checking before primitive decoding/binding/body execution through
one actual public compilation. Source selection and native loading remain open. -/
namespace Solidity.Backend.AbiEntry.Interface

structure ValueCheckedUIntBodyCertificate
    (program : {C : Contract} → {Δ : Ctx} → Nat → Bool → Fin Evm.W →
      Prog C UIntBoundCtx Δ → Prog C RouteCtx Δ) : Prop where
  selected : ∀ {C : Contract} {Δ : Ctx} (base bits : Nat) (payable : Bool) (label : Fin Evm.W)
    (body : Prog C UIntBoundCtx Δ) (outFrag : Evm.Frag Δ),
    Evm.inFragP (Evm.Frag.init UIntBoundCtx) body=some outFrag →
    ∃ (whole : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program bits payable label body))
      (back : Evm.Compiler.Compilation base (Evm.Frag.init UIntBoundCtx) body),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program bits payable label body)=some whole ∧
      Evm.Compiler.compile base (Evm.Frag.init UIntBoundCtx) body=some back
  executed : ∀ {C : Contract} {Δ : Ctx} (base bits : Nat) (payable : Bool) (label : Fin Evm.W)
    (body : Prog C UIntBoundCtx Δ) (outFrag : Evm.Frag Δ),
    Evm.inFragP (Evm.Frag.init UIntBoundCtx) body=some outFrag →
    ∀ (whole : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program bits payable label body))
      (back : Evm.Compiler.Compilation base (Evm.Frag.init UIntBoundCtx) body),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program bits payable label body)=some whole →
      Evm.Compiler.compile base (Evm.Frag.init UIntBoundCtx) body=some back →
      ∀ (machine : Evm.Machine) (word size : Fin Evm.W), machine.mem base=.val word →
      machine.mem (base+1)=.val size →
      Evm.run whole.code machine=if payable || decide (machine.callvalue.val=0) then
        if size.val<36 then .revert else if (Solidity.AbiEntry.Kind.uint bits).valid word.val then
          Evm.run back.code (uintBoundMachine base label word machine) else .revert else .revert
  early_rejection : ∀ {C : Contract} {Δ : Ctx} (base bits : Nat) (payable : Bool) (label : Fin Evm.W)
    (body : Prog C UIntBoundCtx Δ) (outFrag : Evm.Frag Δ),
    Evm.inFragP (Evm.Frag.init UIntBoundCtx) body=some outFrag →
    ∀ whole : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program bits payable label body),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program bits payable label body)=some whole →
      ∀ machine : Evm.Machine, (payable || decide (machine.callvalue.val=0))=false →
      Evm.run whole.code machine=.revert

structure ValueCheckedBoolBodyCertificate
    (program : {C : Contract} → {Δ : Ctx} → Bool → Fin Evm.W →
      Prog C BoolBoundCtx Δ → Prog C RouteCtx Δ) : Prop where
  selected : ∀ {C : Contract} {Δ : Ctx} (base : Nat) (payable : Bool) (label : Fin Evm.W)
    (body : Prog C BoolBoundCtx Δ) (outFrag : Evm.Frag Δ),
    Evm.inFragP (Evm.Frag.init BoolBoundCtx) body=some outFrag →
    ∃ (whole : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program payable label body))
      (back : Evm.Compiler.Compilation base (Evm.Frag.init BoolBoundCtx) body),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program payable label body)=some whole ∧
      Evm.Compiler.compile base (Evm.Frag.init BoolBoundCtx) body=some back
  executed : ∀ {C : Contract} {Δ : Ctx} (base : Nat) (payable : Bool) (label : Fin Evm.W)
    (body : Prog C BoolBoundCtx Δ) (outFrag : Evm.Frag Δ),
    Evm.inFragP (Evm.Frag.init BoolBoundCtx) body=some outFrag →
    ∀ (whole : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program payable label body))
      (back : Evm.Compiler.Compilation base (Evm.Frag.init BoolBoundCtx) body),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program payable label body)=some whole →
      Evm.Compiler.compile base (Evm.Frag.init BoolBoundCtx) body=some back →
      ∀ (machine : Evm.Machine) (word size : Fin Evm.W), machine.mem base=.val word →
      machine.mem (base+1)=.val size →
      Evm.run whole.code machine=if payable || decide (machine.callvalue.val=0) then
        if size.val<36 then .revert else if Solidity.AbiEntry.Kind.bool.valid word.val then
          Evm.run back.code (boolBoundMachine base label word machine) else .revert else .revert
  early_rejection : ∀ {C : Contract} {Δ : Ctx} (base : Nat) (payable : Bool) (label : Fin Evm.W)
    (body : Prog C BoolBoundCtx Δ) (outFrag : Evm.Frag Δ),
    Evm.inFragP (Evm.Frag.init BoolBoundCtx) body=some outFrag →
    ∀ whole : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program payable label body),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program payable label body)=some whole →
      ∀ machine : Evm.Machine, (payable || decide (machine.callvalue.val=0))=false →
      Evm.run whole.code machine=.revert

end Solidity.Backend.AbiEntry.Interface
