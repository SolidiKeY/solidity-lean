import Solidity.Evm.Compiler

/-! Typed selector-local routing through the existing public compiler. A route
label is not a compiled ABI body or a Source declaration authentication. -/
namespace Solidity.Backend.AbiEntry.Interface
abbrev RouteCtx : Ctx := [.val .uint,.val .uint]
abbrev RouteTable := List (Fin Evm.W × Fin Evm.W)
def routeResult (table : RouteTable) (fallback selector : Fin Evm.W) : Fin Evm.W :=
  ((table.find? fun entry => decide (entry.1.val=selector.val)).map Prod.snd).getD fallback

structure SelectorRoutesCertificate
    (route : (C : Contract) → RouteTable → Fin Evm.W → Prog C RouteCtx RouteCtx) : Prop where
  selected : ∀ (C : Contract) (base : Nat) (table : RouteTable) (fallback : Fin Evm.W),
    ∃ result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (route C table fallback),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (route C table fallback)=some result
  executed : ∀ (C : Contract) (base : Nat) (table : RouteTable) (fallback : Fin Evm.W)
    (result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (route C table fallback)),
    Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (route C table fallback)=some result →
    ∀ (machine : Evm.Machine) (selector : Fin Evm.W), machine.mem base=.val selector →
    Evm.run result.code machine=.ok
      {machine with mem := Evm.upd machine.mem (base+1) (.val (routeResult table fallback selector))} 0
end Solidity.Backend.AbiEntry.Interface
