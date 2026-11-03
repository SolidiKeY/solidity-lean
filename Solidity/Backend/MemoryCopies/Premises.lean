import Solidity.Backend.MemoryCopies.Interface
import Solidity.Source.Eval
import Solidity.Source.Hoare

/-! Explicit external obligations. No instance is postulated. A consumer must
supply the producing item's actual theorem at the specified types. These are
local boundaries; they are not substitutes for the producers' frozen APIs. -/
namespace Solidity.Backend.MemoryCopies

/-- S03-PANIC41: a supplied actual
Source allocation operation, at an actual state, fails with alloc panic.
The producer must also establish which size predicate selects this branch. -/
structure Panic41Premise {E : Source.Env} {Γ : Source.RCtx} {α : Type}
    (operation : Source.EM E Γ α) (before after : Source.EMState E Γ) : Prop where
  failure : operation.run before = (Source.panic .alloc, after)

/-- V11 G34: the compiled alias branch has the existing typed identity and
heap. The actual path-resolution and rebinding certificates must be supplied. -/
structure AliasPremise {H : HTy} {R : RefTy} (hp : Heap H)
    (input output : HRef H R) (after : Heap H) : Prop where
  agreement : AliasCertificate hp input output after

/-- V10 G27.05, V11 G35.02/.03: reached machines at a composition boundary.
These are exact execution equations, not an assumed universal compiler theorem.
Each use must name its producing item, resolved operands and observations. -/
structure LocationStepPremise (code : List Evm.Instr)
    (before after : Evm.Machine) : Prop where
  execution : Evm.run code before = .ok after 0

end Solidity.Backend.MemoryCopies
