import Solidity.Backend.AbiEntry.CoreDispatch

/-! Receive/fallback choice over actual typed core bodies. The payability flag
and incoming locals are explicit data; Source declaration authority and native
parameter binding are not supplied. Empty input prefers receive, otherwise
fallback; absent endpoints reject. No body execution/result is a premise. -/
namespace Solidity.Backend.AbiEntry.Interface
structure SpecialBody (C : Contract) (Γ : Ctx) (frag : Evm.Frag Γ) where
  payable : Bool
  body : DispatchBody C Γ frag

def specialBodyChoice {C : Contract} {Γ : Ctx} {frag : Evm.Frag Γ}
    (receive fallback : Option (SpecialBody C Γ frag)) (size : Fin Evm.W) : Option (SpecialBody C Γ frag) :=
  if size.val=0 then receive.orElse (fun _ => fallback) else fallback

structure CoreSpecialCertificate
    (endpoint : {C : Contract} → {Γ : Ctx} → (frag : Evm.Frag Γ) → Option (SpecialBody C Γ frag) → DispatchBody C Γ frag)
    (route : {C : Contract} → {Γ : Ctx} → (frag : Evm.Frag Γ) → Idx Γ (.val .uint) →
      Option (SpecialBody C Γ frag) → Option (SpecialBody C Γ frag) → Prog C Γ Γ) : Prop where
  endpoint_code : ∀ {C : Contract} {Γ : Ctx} (base : Nat) (frag : Evm.Frag Γ) (row : Option (SpecialBody C Γ frag)),
    Evm.compileProg base (endpoint frag row).program=match row with
      | none => [.revert]
      | some target => Evm.compileProg base (ValueGateBody.guard target.payable target.body.program)
  selected : ∀ {C : Contract} {Γ : Ctx} (base : Nat) (frag : Evm.Frag Γ) (index : Idx Γ (.val .uint))
    (receive fallback : Option (SpecialBody C Γ frag)),
    ∃ result : Evm.Compiler.Compilation base frag (route frag index receive fallback),
      Evm.Compiler.compile base frag (route frag index receive fallback)=some result
  executed : ∀ {C : Contract} {Γ : Ctx} (L base : Nat) (frag : Evm.Frag Γ) (index : Idx Γ (.val .uint))
    (receive fallback : Option (SpecialBody C Γ frag)) (result : Evm.Compiler.Compilation base frag (route frag index receive fallback)),
    Evm.Compiler.compile base frag (route frag index receive fallback)=some result →
    ∀ (state : State C Γ) (machine : Evm.Machine), Evm.Sim C L base frag state machine →
    L+Evm.Prog.pushes (endpoint frag (receive.orElse (fun _ => fallback))).program≤Evm.Lmax →
    ∀ size : Fin Evm.W, machine.mem (Evm.cellOf base index)=.val size →
    Evm.run result.code machine=
      Evm.run (Evm.compileProg base (endpoint frag (specialBodyChoice receive fallback size)).program) machine
end Solidity.Backend.AbiEntry.Interface
