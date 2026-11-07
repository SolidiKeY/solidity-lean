import Solidity.Backend.AbiEntry.CoreJoin

/-! Finite dispatch metadata carries existing intrinsic programs and actual
core-classifier witnesses, not selected artifacts or assumed executions.
Source table/body authenticity, short special routing and native input-frame
construction remain separate. The compiler's existing resource bound is kept. -/
namespace Solidity.Backend.AbiEntry.Interface
structure DispatchBody (C : Contract) (Γ : Ctx) (frag : Evm.Frag Γ) where
  outCtx : Ctx
  program : Prog C Γ outCtx
  outFrag : Evm.Frag outCtx
  admitted : Evm.inFragP frag program=some outFrag

structure DispatchRow (C : Contract) (Γ : Ctx) (frag : Evm.Frag Γ) where
  tag : Fin Evm.W
  target : DispatchBody C Γ frag

def dispatchTarget {C : Contract} {Γ : Ctx} {frag : Evm.Frag Γ}
    (rows : List (DispatchRow C Γ frag)) (fallback : DispatchBody C Γ frag) (selector : Fin Evm.W) :
    DispatchBody C Γ frag :=
  ((rows.find? fun row => decide (row.tag.val=selector.val)).map (·.target)).getD fallback

structure CoreDispatchCertificate
    (route : {C : Contract} → {Γ : Ctx} → (frag : Evm.Frag Γ) → Idx Γ (.val .uint) →
      List (DispatchRow C Γ frag) → DispatchBody C Γ frag → Prog C Γ Γ) : Prop where
  bodies_selected : ∀ {C : Contract} {Γ : Ctx} (base : Nat) (frag : Evm.Frag Γ) (target : DispatchBody C Γ frag),
    ∃ result : Evm.Compiler.Compilation base frag target.program,
      Evm.Compiler.compile base frag target.program=some result ∧ result.code=Evm.compileProg base target.program
  selected : ∀ {C : Contract} {Γ : Ctx} (base : Nat) (frag : Evm.Frag Γ) (index : Idx Γ (.val .uint))
    (rows : List (DispatchRow C Γ frag)) (fallback : DispatchBody C Γ frag),
    ∃ result : Evm.Compiler.Compilation base frag (route frag index rows fallback),
      Evm.Compiler.compile base frag (route frag index rows fallback)=some result
  executed : ∀ {C : Contract} {Γ : Ctx} (L base : Nat) (frag : Evm.Frag Γ) (index : Idx Γ (.val .uint))
    (rows : List (DispatchRow C Γ frag)) (fallback : DispatchBody C Γ frag)
    (result : Evm.Compiler.Compilation base frag (route frag index rows fallback)),
    Evm.Compiler.compile base frag (route frag index rows fallback)=some result →
    ∀ (state : State C Γ) (machine : Evm.Machine), Evm.Sim C L base frag state machine →
    (∀ row ∈ rows, L+Evm.Prog.pushes row.target.program≤Evm.Lmax) →
    ∀ selector : Fin Evm.W, machine.mem (Evm.cellOf base index)=.val selector →
    Evm.run result.code machine=Evm.run (Evm.compileProg base (dispatchTarget rows fallback selector).program) machine
end Solidity.Backend.AbiEntry.Interface
