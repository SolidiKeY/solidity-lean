import Solidity.Backend.AbiEntry.SelectorRoutes
import Solidity.Backend.AbiEntry.SelectorMatchInterface

/-! Ordinary Source function lookup to actual typed route execution. Labels
remain compile-time observations of declarations, not compiled Source bodies. -/
namespace Solidity.Backend.AbiEntry.Interface

def rawSelectorWord (frame : Source.Fr) : Fin Evm.W :=
  ⟨Solidity.AbiEntry.load frame.cd 0/2^224,
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Solidity.AbiEntry.load_lt _ _)⟩

structure SourceRoutesCertificate
    (table : {E : Source.Env} → Source.Glob E → String → (Source.Decl → Fin Evm.W) → RouteTable) : Prop where
  lookup : ∀ {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (labels : Source.Decl → Fin Evm.W) (fallback : Fin Evm.W), 4≤frame.cd.length →
    routeResult (table global frame.contract labels) fallback (rawSelectorWord frame)=
      ((global.pickFn frame frame.cd).map labels).getD fallback
  executed : ∀ {E : Source.Env} (global : Source.Glob E) (frame : Source.Fr)
    (labels : Source.Decl → Fin Evm.W) (fallback : Fin Evm.W), 4≤frame.cd.length →
    ∀ (C : Contract) (base : Nat)
    (result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx)
      (SelectorRoutes.route C (table global frame.contract labels) fallback)),
    Evm.Compiler.compile base (Evm.Frag.init RouteCtx)
      (SelectorRoutes.route C (table global frame.contract labels) fallback)=some result →
    ∀ machine : Evm.Machine, machine.mem base=.val (rawSelectorWord frame) →
    Evm.run result.code machine=.ok
      {machine with
        mem := Evm.upd machine.mem (base+1) (.val (((global.pickFn frame frame.cd).map labels).getD fallback))} 0
end Solidity.Backend.AbiEntry.Interface
