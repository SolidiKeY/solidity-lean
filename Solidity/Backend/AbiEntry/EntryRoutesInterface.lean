import Solidity.Backend.AbiEntry.SpecialRoutes

/-! Combined ordinary/special continuation routing. Getter precedence and
actual ABI bodies/bindings are not certified by a continuation label. -/
namespace Solidity.Backend.AbiEntry.Interface
def ordinaryResult (table : PayableRouteTable) (selector : Fin Evm.W) : Option SpecialRow :=
  (table.find? fun row => decide (row.1.val=selector.val)).map Prod.snd
def entryRouteOutcome (base : Nat) (table : PayableRouteTable) (receive fallback : Option SpecialRow)
    (selector size : Fin Evm.W) (machine : Evm.Machine) : Evm.Out :=
  if size.val<4 then specialOutcome base receive fallback size machine else
    match ordinaryResult table selector with
    | none => specialOutcome base receive fallback size machine
    | some row => specialRowOutcome base (some row) machine
structure EntryRoutesCertificate
    (route : (C : Contract) → PayableRouteTable → Option SpecialRow → Option SpecialRow → Prog C RouteCtx RouteCtx) : Prop where
  selected : ∀ (C : Contract) (base : Nat) (table : PayableRouteTable) (receive fallback : Option SpecialRow),
    ∃ result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (route C table receive fallback),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (route C table receive fallback)=some result
  executed : ∀ (C : Contract) (base : Nat) (table : PayableRouteTable) (receive fallback : Option SpecialRow)
    (result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (route C table receive fallback)),
    Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (route C table receive fallback)=some result →
    ∀ (machine : Evm.Machine) (selector size : Fin Evm.W), machine.mem base=.val selector →
    machine.mem (base+1)=.val size →
    Evm.run result.code machine=entryRouteOutcome base table receive fallback selector size machine
end Solidity.Backend.AbiEntry.Interface
