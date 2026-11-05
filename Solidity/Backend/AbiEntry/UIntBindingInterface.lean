import Solidity.Backend.AbiEntry.SingleWordGate

/-! A typed uint parameter local after actual singleton ABI validation.
The initial local word/size representation and semantic fuel remain explicit;
this contract supplies no native byte loader or whole Source-body agreement. -/
namespace Solidity.Backend.AbiEntry.Interface
abbrev UIntBoundCtx : Ctx := .val .uint :: RouteCtx

def uintBoundMachine (base : Nat) (label word : Fin Evm.W) (machine : Evm.Machine) : Evm.Machine :=
  {machine with mem := Evm.upd (Evm.upd machine.mem (base+1) (.val label)) (base+2) (.val word)}

def uintBindingOutcome (base bits : Nat) (label word size : Fin Evm.W) (machine : Evm.Machine) : Evm.Out :=
  if size.val<36 then .revert else
  if (Solidity.AbiEntry.Kind.uint bits).valid word.val then .ok (uintBoundMachine base label word machine) 0
  else .revert

structure UIntBindingCertificate
    (program : (C : Contract) → Nat → Fin Evm.W → Prog C RouteCtx UIntBoundCtx) : Prop where
  selected : ∀ (C : Contract) (base bits : Nat) (label : Fin Evm.W),
    ∃ result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program C bits label),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program C bits label)=some result
  executed : ∀ (C : Contract) (base bits : Nat) (label : Fin Evm.W)
    (result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program C bits label)),
    Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program C bits label)=some result →
    ∀ (machine : Evm.Machine) (word size : Fin Evm.W), machine.mem base=.val word →
    machine.mem (base+1)=.val size →
    Evm.run result.code machine=uintBindingOutcome base bits label word size machine
  entry_rejection : ∀ (C : Contract) (base bits : Nat) (label : Fin Evm.W)
    (result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (program C bits label)),
    Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (program C bits label)=some result →
    ∀ (input : Solidity.AbiEntry.Input) (fuel : Nat) (machine : Evm.Machine) (size : Fin Evm.W),
    machine.mem base=.val (rawArgumentWord input) → machine.mem (base+1)=.val size → size.val=input.size →
    (Evm.run result.code machine=.revert ↔
      Solidity.AbiEntry.entry input (fuel+2) (singleWordParams (.uint bits))=.error .revert)
end Solidity.Backend.AbiEntry.Interface
