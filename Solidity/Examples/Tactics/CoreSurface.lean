import Solidity.Calculus.Core.Surface
import Solidity.Calculus.Core.Callback
import Solidity.Tools.Inspect

/-!
# The flip switch, pinned

`open scoped Solidity.Core.Scoped` (`Calculus/Core/Surface.lean`): today's
text read scoped, `dl!{ … }` a `Core.Fml C []`, `⊨` scoped validity, `⊢`
the scoped sequent, and the commands on it.  Outside the scope the same text
is today's.  The callback taclets print as today's
(`Calculus/Core/Callback.lean`).
-/

namespace Solidity.Examples.Tactics.CoreSurface

open Solidity

local instance : InContract := ⟨StandardExample⟩

/-- info: dl{ a = 1 → ⟨ uint x = a; ⟩ x = 1 } : Surface.Fml StandardExample -/
#guard_msgs in #check dl!{ a == 1 → ⟨ uint x = a; ⟩ x == 1 }

section Scoped

open scoped Core.Scoped

/-- info: dl{ ∀ uint a; a = 1 → ⟨ uint x = a; ⟩ x = 1 } : Core.Fml StandardExample [] -/
#guard_msgs in #check dl!{ a == 1 → ⟨ uint x = a; ⟩ x == 1 }

/-- info: ⊨ dl{ ∀ uint a; a = 1 → ⟨ uint x = a; ⟩ x = 1 } : Prop -/
#guard_msgs in #check ⊨ dl!{ a == 1 → ⟨ uint x = a; ⟩ x == 1 }

/-- info: dl{ ⟹ ∀ uint a; a = 1 → ⟨ uint x = a; ⟩ x = 1 } : Prop -/
#guard_msgs in #check ⊢ dl!{ a == 1 → ⟨ uint x = a; ⟩ x == 1 }

/-- info: dl{ ∀ uint x; true → [ x = 1; ] x = 1 } : Core.Fml StandardExample [] -/
#guard_msgs in #check dl!{ true ⟹ [ x = 1; ] x == 1 }

/--
info: symbolic execution leaves:
    dl{ ∀ uint a; a = 1 → { x := a } x = 1 }
update-free:
    ∀ uint a; a = 1 → a = a ∧ a = 1
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
info: @Core.CallbackTaclet.transferWithCallbackBox : ∀ {C : Contract} {k : Nat} {Γ : Core.Ctx}
  {sadr se : Core.Simple C Γ PrimTy.uint},
  dl[Core.CallbackTaclet C k]{ [ sadr .transfer(se); ] ⇝
    { net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se) } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Core.CallbackTaclet.transferWithCallbackBox

end Solidity.Examples.Tactics.CoreSurface
