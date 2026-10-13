import Solidity.Calculus.Surface
import Solidity.Calculus.Callback
import Solidity.Tools.Inspect

/-!
# The flip switch, pinned

`open scoped Solidity.Scoped` (`Calculus/Surface.lean`): today's
text read scoped, `dl!{ … }` a `Fml C []`, `⊨` scoped validity, `⊢`
the scoped sequent, and the commands on it.  Outside the scope a formula
with a modality reads scoped too (W8.2).  The callback taclets print as today's
(`Calculus/Callback.lean`).
-/

namespace Solidity.Examples.Tactics.Surface

open Solidity

local instance : InContract := ⟨StandardExample⟩

-- A formula with a modality reads scoped outside the scope too (decision 11),
-- its parameters bound by hidden binders, as today's `dl!` leaves them free;
-- the scope's `cdl!` binds a value parameter by `∀`.
/-- info: dl{ a = 1 → ⟨ uint x = a; ⟩ x = 1 } : Fml StandardExample [] -/
#guard_msgs in #check dl!{ a == 1 → ⟨ uint x = a; ⟩ x == 1 }

section Scoped

open scoped Scoped

/-- info: dl{ ∀ uint a; a = 1 → ⟨ uint x = a; ⟩ x = 1 } : Fml StandardExample [] -/
#guard_msgs in #check dl!{ a == 1 → ⟨ uint x = a; ⟩ x == 1 }

/-- info: ⊨ dl{ ∀ uint a; a = 1 → ⟨ uint x = a; ⟩ x = 1 } : Prop -/
#guard_msgs in #check ⊨ dl!{ a == 1 → ⟨ uint x = a; ⟩ x == 1 }

/-- info: dl{ ⟹ ∀ uint a; a = 1 → ⟨ uint x = a; ⟩ x = 1 } : Prop -/
#guard_msgs in #check ⊢ dl!{ a == 1 → ⟨ uint x = a; ⟩ x == 1 }

/-- info: dl{ ∀ uint x; true → [ x = 1; ] x = 1 } : Fml StandardExample [] -/
#guard_msgs in #check dl!{ true ⟹ [ x = 1; ] x == 1 }

/--
info: symbolic execution leaves:
    dl{ ∀ uint a; a = 1 → { x := a } x = 1 }
update-free:
    ∀ uint a; a = 1 → ∀ uint x; true = true ∧ a = 1
-/
#guard_msgs in #wp dl!{ a == 1 → ⟨ uint x = a; ⟩ x == 1 }

/--
info: 0: allRight
1: sendNoCallbackBox
  [send succeeded]
    2: Closed goal
  [send failed]
    3: Closed goal
closed: 0 open goal(s), 4 node(s), 2 branch(es)
-/
#guard_msgs in #proof_tree dl!{ [ ok = to.send(5); ] true }

end Scoped

/-! ## The callback taclets -/

/--
info: @CallbackTaclet.transferWithCallbackBox : ∀ {C : Contract} {k : Nat} {Γ : Ctx} {sadr se : Simple C Γ PrimTy.uint},
  dl[CallbackTaclet C k]{ [ sadr .transfer(se); ] ⇝
    { net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se) } ⟨[ ]⟩ }
-/
#guard_msgs in #check @CallbackTaclet.transferWithCallbackBox

end Solidity.Examples.Tactics.Surface
