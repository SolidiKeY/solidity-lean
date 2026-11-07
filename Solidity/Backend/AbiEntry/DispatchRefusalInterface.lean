import Solidity.Backend.AbiEntry.GetterRoutes

/-! Exact routing refusal, distinct from later decoder/body failure. -/
namespace Solidity.Backend.AbiEntry.Interface
def dispatchRefuses {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr) : Bool :=
  match global.pickFn frame frame.cd with
  | some declaration => !((declaration.fnMut == some .payable) || decide (frame.value.val=0))
  | none => match global.pickGetter frame frame.cd with
    | some _ => !decide (frame.value.val=0)
    | none => match sourceSpecial E frame with
      | none => true
      | some declaration => !(declaration.specialPayable || decide (frame.value.val=0))
structure DispatchRefusalCertificate : Prop where
  source : ∀ {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr) (fuel : Nat),
    dispatchRefuses global frame=true →
    Source.dispatch global frame (fuel+1) frame.cd=Source.EM.halt (.revert [])
  compiled : ∀ {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr) (labels : Source.Decl → Fin Evm.W)
    (C : Contract) (base : Nat)
    (result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx)
      (EntryRoutes.route C (GetterRoutes.table global frame.contract labels)
        (SpecialRoutes.receiveRow E frame.contract labels) (SpecialRoutes.fallbackRow E frame.contract labels))),
    Evm.Compiler.compile base (Evm.Frag.init RouteCtx)
      (EntryRoutes.route C (GetterRoutes.table global frame.contract labels)
        (SpecialRoutes.receiveRow E frame.contract labels) (SpecialRoutes.fallbackRow E frame.contract labels))=some result →
    ∀ (machine : Evm.Machine) (size : Fin Evm.W), machine.mem base=.val (rawSelectorWord frame) →
    machine.mem (base+1)=.val size → size.val=frame.cd.length → machine.callvalue.val=frame.value.val →
    (Evm.run result.code machine=.revert ↔ dispatchRefuses global frame=true)
end Solidity.Backend.AbiEntry.Interface
