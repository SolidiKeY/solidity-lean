import Solidity.Backend.AbiEntry.EntryRoutes

/-! Source ordinary/getter/special continuation precedence. A selected getter
label does not execute its storage read, argument decoder or ABI output. -/
namespace Solidity.Backend.AbiEntry.Interface
def getterRow (labels : Source.Decl → Fin Evm.W) (entry : Source.Decl × List Source.STy × Source.STy) : SpecialRow :=
  (labels entry.1,false)
def sourceDispatchRow {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (labels : Source.Decl → Fin Evm.W) : Option SpecialRow :=
  ((global.pickFn frame frame.cd).map (EntryRoutes.ordinaryRow labels)).orElse fun _ =>
    ((global.pickGetter frame frame.cd).map (getterRow labels)).orElse fun _ =>
      (sourceSpecial E frame).map (SpecialRoutes.row labels)
structure GetterRoutesCertificate
    (table : {E : Source.Env} → Source.Glob E → String → (Source.Decl → Fin Evm.W) → PayableRouteTable) : Prop where
  lookup : ∀ {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr) (labels : Source.Decl → Fin Evm.W),
    4≤frame.cd.length → ordinaryResult (table global frame.contract labels) (rawSelectorWord frame)=
      ((global.pickFn frame frame.cd).map (EntryRoutes.ordinaryRow labels)).orElse
        (fun _ => (global.pickGetter frame frame.cd).map (getterRow labels))
  executed : ∀ {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr) (labels : Source.Decl → Fin Evm.W)
    (C : Contract) (base : Nat)
    (result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx)
      (EntryRoutes.route C (table global frame.contract labels)
        (SpecialRoutes.receiveRow E frame.contract labels) (SpecialRoutes.fallbackRow E frame.contract labels))),
    Evm.Compiler.compile base (Evm.Frag.init RouteCtx)
      (EntryRoutes.route C (table global frame.contract labels)
        (SpecialRoutes.receiveRow E frame.contract labels) (SpecialRoutes.fallbackRow E frame.contract labels))=some result →
    ∀ (machine : Evm.Machine) (size : Fin Evm.W), machine.mem base=.val (rawSelectorWord frame) →
    machine.mem (base+1)=.val size → size.val=frame.cd.length →
    Evm.run result.code machine=specialRowOutcome base (sourceDispatchRow global frame labels) machine
end Solidity.Backend.AbiEntry.Interface
