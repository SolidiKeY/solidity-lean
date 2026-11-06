import Solidity.Backend.AbiEntry.SelectorRoutesInterface

/-! Per-entry payable routing, not a global pre-route value rejection. A match
that rejects value never tries a later row or the no-match label. -/
namespace Solidity.Backend.AbiEntry.Interface
abbrev PayableRouteTable := List (Fin Evm.W × Fin Evm.W × Bool)
def payableRouteResult (table : PayableRouteTable) (fallback selector : Fin Evm.W) : Fin Evm.W × Bool :=
  ((table.find? fun row => decide (row.1.val=selector.val)).map Prod.snd).getD (fallback,true)
def payableRouteOutcome (base : Nat) (table : PayableRouteTable) (fallback selector : Fin Evm.W)
    (machine : Evm.Machine) : Evm.Out :=
  let row := payableRouteResult table fallback selector
  if row.2 || decide (machine.callvalue.val=0) then
    .ok {machine with mem := Evm.upd machine.mem (base+1) (.val row.1)} 0 else .revert
structure PayableRoutesCertificate
    (route : (C : Contract) → PayableRouteTable → Fin Evm.W → Prog C RouteCtx RouteCtx) : Prop where
  selected : ∀ (C : Contract) (base : Nat) (table : PayableRouteTable) (fallback : Fin Evm.W),
    ∃ result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (route C table fallback),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (route C table fallback)=some result
  executed : ∀ (C : Contract) (base : Nat) (table : PayableRouteTable) (fallback : Fin Evm.W)
    (result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (route C table fallback)),
    Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (route C table fallback)=some result →
    ∀ (machine : Evm.Machine) (selector : Fin Evm.W), machine.mem base=.val selector →
    Evm.run result.code machine=payableRouteOutcome base table fallback selector machine
end Solidity.Backend.AbiEntry.Interface
