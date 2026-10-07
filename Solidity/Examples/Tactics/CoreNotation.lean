import Solidity.Calculus.Core.Notation
import Solidity.Calculus.Core.Delab
import Solidity.Tools.CoreInspect

/-!
# Concrete formulas read scoped: `cdl!{ … }`

`Calculus/Core/Notation.lean`'s reader pinned: the context each name is read
in (a parameter bound outermost by `∀`, an update's target declared, a
branch's local out of scope after it), and `#wp`/`#step` on the result
(`Tools/CoreInspect.lean`).
-/

namespace Solidity.Examples.Tactics.CoreNotation

open Solidity

local instance : InContract := ⟨StandardExample⟩

/-- info: dl{ ⟨ uint x = 10; ⟩ x = 10 } : Core.Fml StandardExample [] -/
#guard_msgs in #check cdl!{ ⟨ uint x = 10; ⟩ x == 10 }

/-- info: dl{ [ alice.age = 10; uint y = alice.age; ] y = 10 } : Core.Fml StandardExample [] -/
#guard_msgs in #check cdl!{ [ alice.age = 10; uint y = alice.age; ] y == 10 }

/-! A name nothing declares is a parameter, bound outermost by `∀`. -/

/-- info: dl{ ∀ uint x; ∀ uint a; a = 1 → ⟨ x = a; ⟩ x = 1 } : Core.Fml StandardExample [] -/
#guard_msgs in #check cdl!{ a == 1 → ⟨ x = a; ⟩ x == 1 }

/-- info: dl{ ∀ uint a; ∀ uint y; y = a } : Core.Fml StandardExample [] -/
#guard_msgs in #check cdl!{ ∀ uint y; y == a }

/-! An update declares what it binds; an alias is bound by a hidden binder. -/

/--
info: dl{ { x := 10 ‖ storage := save(storage, alice.age, 10) } find(storage, alice.age) = x } : Core.Fml StandardExample []
-/
#guard_msgs in
#check cdl!{ { x := 10 ‖ storage := save(storage, alice.age, 10) } find(storage, alice.age) = x }

/-- info: dl{ { p := alice } ⟨ p.age = 3; ⟩ find(storage, p.age) = 3 } : Core.Fml StandardExample [] -/
#guard_msgs in #check cdl!{ { p := alice } ⟨ p.age = 3; ⟩ p.age == 3 }

/-- info: dl{ ⟨ p = alice; p.age = 3; ⟩ find(storage, p.age) = 3 } : Core.Fml StandardExample [] -/
#guard_msgs in #check cdl!{ ⟨ p = alice; p.age = 3; ⟩ find(storage, p.age) = 3 }

/--
info: dl{
  { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
    ⟨ carolAcc = carol.account; carolAcc.balance = 1; ⟩ true } : Core.Fml StandardExample []
-/
#guard_msgs in
#check cdl!{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
       ⟨ carolAcc = carol.account; carolAcc.balance = 1; ⟩ true }

/-! A local of a branch is out of scope after it; one of the program is in
scope in its postcondition only. -/

/--
info: dl{
  ⟨ if (alice.age == 4) {uint z = 1;total = z;} else {total = 2;}; ⟩
    find(storage, total) = 1 } : Core.Fml StandardExample []
-/
#guard_msgs in
#check cdl!{ ⟨ if (alice.age == 4) { uint z = 1; total = z; } else { total = 2; }; ⟩ total == 1 }

/-- info: dl{ ⟨ uint y = 1; ⟩ (true ∧ y = 1) } : Core.Fml StandardExample [] -/
#guard_msgs in #check cdl!{ ⟨ uint y = 1; ⟩ (true ∧ y == 1) }

/-- error: Solidity elaboration failed: unknown name y -/
#guard_msgs in #check cdl!{ ⟨ uint y = 1; ⟩ true ∧ y == 1 }

/-- error: a name where a formula stands is a Lean formula (φ : Core.Post C Γ): unknown `φ` -/
#guard_msgs in #check cdl!{ φ where Person memory carol }

/-! `#wp` and `#step` on a scoped formula. -/

/--
info: symbolic execution leaves:
    dl{ { x := 10 } x = 10 }
update-free:
    10 = 10 ∧ 10 = 10
-/
#guard_msgs in #wp cdl!{ ⟨ uint x = 10; ⟩ x == 10 }

/--
info:   ~[storageFieldWriteSave]~>
    dl{ { storage := save(storage, alice.age, 10) } [ uint y = alice.age; ] y = 10 }
-/
#guard_msgs in #step cdl!{ [ alice.age = 10; uint y = alice.age; ] y == 10 }

end Solidity.Examples.Tactics.CoreNotation
