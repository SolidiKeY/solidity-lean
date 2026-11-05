import Solidity.Backend.AbiEntry.PayableRoutes
import Solidity.Backend.AbiEntry.SourceRoutes

/-! Source-declaration payability and first-match label routing. This is not
Source body execution, special-function dispatch or native realization. -/
namespace Solidity.Backend.AbiEntry.Interface

def sourcePayableResult {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (labels : Source.Decl → Fin Evm.W) (fallback : Fin Evm.W) : Fin Evm.W × Bool :=
  ((global.pickFn frame frame.cd).map fun declaration =>
    (labels declaration, declaration.fnMut == some .payable)).getD (fallback,true)

def sourcePayableOutcome {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (labels : Source.Decl → Fin Evm.W) (fallback : Fin Evm.W) (base : Nat)
    (machine : Evm.Machine) : Evm.Out :=
  let row := sourcePayableResult global frame labels fallback
  if row.2 || decide (frame.value.val=0) then
    .ok {machine with mem := Evm.upd machine.mem (base+1) (.val row.1)} 0 else .revert

structure SourcePayableCertificate
    (table : {E : Source.Env} → Source.Glob E → String → (Source.Decl → Fin Evm.W) → PayableRouteTable) : Prop where
  lookup : ∀ {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (labels : Source.Decl → Fin Evm.W) (fallback : Fin Evm.W), 4≤frame.cd.length →
    payableRouteResult (table global frame.contract labels) fallback (rawSelectorWord frame)=
      sourcePayableResult global frame labels fallback
  executed : ∀ {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (labels : Source.Decl → Fin Evm.W) (fallback : Fin Evm.W), 4≤frame.cd.length →
    ∀ (C : Contract) (base : Nat)
    (result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx)
      (PayableRoutes.route C (table global frame.contract labels) fallback)),
    Evm.Compiler.compile base (Evm.Frag.init RouteCtx)
      (PayableRoutes.route C (table global frame.contract labels) fallback)=some result →
    ∀ machine : Evm.Machine, machine.mem base=.val (rawSelectorWord frame) →
    machine.callvalue.val=frame.value.val →
    Evm.run result.code machine=sourcePayableOutcome global frame labels fallback base machine
end Solidity.Backend.AbiEntry.Interface
