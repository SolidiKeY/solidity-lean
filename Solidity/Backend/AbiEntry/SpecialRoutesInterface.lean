import Solidity.Backend.AbiEntry.ShortRoutes

/-! Special-dispatch continuation selection, not execution of special bodies
or fallback input/output binding. Ordinary/getter dispatch precedes this. -/
namespace Solidity.Backend.AbiEntry.Interface
abbrev SpecialRow := Fin Evm.W × Bool
def specialResult (receive fallback : Option SpecialRow) (size : Fin Evm.W) : Option SpecialRow :=
  if size.val=0 then receive.orElse (fun _ => fallback) else fallback
def specialRowOutcome (base : Nat) (row : Option SpecialRow) (machine : Evm.Machine) : Evm.Out :=
  match row with
  | none => .revert
  | some (label,payable) => if payable || decide (machine.callvalue.val=0) then
      .ok {machine with mem := Evm.upd machine.mem (base+1) (.val label)} 0 else .revert
def specialOutcome (base : Nat) (receive fallback : Option SpecialRow) (size : Fin Evm.W)
    (machine : Evm.Machine) : Evm.Out := specialRowOutcome base (specialResult receive fallback size) machine

def sourceSpecial (E : Source.Env) (frame : Source.Fr) : Option Source.Decl :=
  if frame.cd.isEmpty then (E.special frame.contract .receive).orElse
    (fun _ => E.special frame.contract .fallback) else E.special frame.contract .fallback

structure SpecialRoutesCertificate
    (route : (C : Contract) → Option SpecialRow → Option SpecialRow → Prog C RouteCtx RouteCtx) : Prop where
  selected : ∀ (C : Contract) (base : Nat) (receive fallback : Option SpecialRow),
    ∃ result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (route C receive fallback),
      Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (route C receive fallback)=some result
  executed : ∀ (C : Contract) (base : Nat) (receive fallback : Option SpecialRow)
    (result : Evm.Compiler.Compilation base (Evm.Frag.init RouteCtx) (route C receive fallback)),
    Evm.Compiler.compile base (Evm.Frag.init RouteCtx) (route C receive fallback)=some result →
    ∀ (machine : Evm.Machine) (size : Fin Evm.W), machine.mem (base+1)=.val size →
    Evm.run result.code machine=specialOutcome base receive fallback size machine
end Solidity.Backend.AbiEntry.Interface
