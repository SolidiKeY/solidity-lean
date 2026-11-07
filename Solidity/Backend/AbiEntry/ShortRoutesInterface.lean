import Solidity.Backend.AbiEntry.SourcePayable

/-! A length-local branch before ordinary selector dispatch. The short label
is a continuation observation, not an executed fallback/receive body. -/
namespace Solidity.Backend.AbiEntry.Interface
def shortRouteOutcome (base : Nat) (table : PayableRouteTable) (fallback short selector size : Fin Evm.W)
    (machine : Evm.Machine) : Evm.Out :=
  if size.val<4 then .ok {machine with mem := Evm.upd machine.mem (base+1) (.val short)} 0
  else payableRouteOutcome base table fallback selector machine
structure ShortRoutesCertificate
    (route : (C : Contract) → PayableRouteTable → Fin Evm.W → Fin Evm.W → Prog C RouteCtx RouteCtx) : Prop where
  selected : ∀ (C : Contract) (base : Nat) (table : PayableRouteTable) (fallback short : Fin Evm.W),
    ∃ result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (route C table fallback short),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (route C table fallback short)=some result
  executed : ∀ (C : Contract) (base : Nat) (table : PayableRouteTable) (fallback short : Fin Evm.W)
    (result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (route C table fallback short)),
    Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (route C table fallback short)=some result →
    ∀ (machine : Evm.Machine) (selector size : Fin Evm.W), machine.mem base=.val selector →
    machine.mem (base+1)=.val size →
    Evm.run result.code machine=shortRouteOutcome base table fallback short selector size machine
end Solidity.Backend.AbiEntry.Interface
