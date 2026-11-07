import Solidity.Backend.MemoryCopies.FixedReferenceLive
import Solidity.Evm.Expr

/-! Contract only for selecting an actual fixed-reference storage operand with
compiled SPath code and transporting its live representation. This interface
supplies no inhabitant and makes no parent-copy/declaration execution claim. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def FixedReferencePathResult {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count : Nat}
    (L b : Nat) (machine : Machine)
    (path : SPath C Γ (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (value : SVal (.ref (.fixed (.ref (.array (.prim primitive))) count))) : Prop :=
  ∃ source : Slot,
    run (compileSPath b path) machine = .ok (machine.push (.slot source)) 0 ∧
    ReprAt machine.store L (.ref (.fixed (.ref (.array (.prim primitive))) count)) source value ∧
    ReprAt machine.store L (.ref (.fixed (.ref (.array (.prim primitive))) count)) source
      (fixedReferenceLiveCanonical value)

structure FixedReferencePathCertificate : Prop where
  select : ∀ {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count L b : Nat} {frag : Frag Γ}
    (state : State C Γ) (machine : Machine)
    (path : SPath C Γ (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (reference : SRef C (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (value : SVal (.ref (.fixed (.ref (.array (.prim primitive))) count))),
    Sim C L b frag state machine → spathIn frag false path = true →
    path.resolveT state = .ok reference → state.storage.find reference = some value →
    FixedReferencePathResult L b machine path value

end Solidity.Backend.MemoryCopies
