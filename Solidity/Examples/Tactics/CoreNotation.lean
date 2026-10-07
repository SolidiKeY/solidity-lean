import Solidity.Calculus.Core.Notation
import Solidity.Calculus.Core.Delab

namespace Solidity.Examples.Tactics.CoreNotation

open Solidity

local instance : InContract := ⟨StandardExample⟩

#check cdl!{ ⟨ uint x = 10; ⟩ x == 10 }
#check cdl!{ [ alice.age = 10; uint y = alice.age; ] y == 10 }
#check cdl!{ a == 1 → ⟨ x = a; ⟩ x == 1 }
#check cdl!{ { x := 10 ‖ storage := save(storage, alice.age, 10) } find(storage, alice.age) = x }
#check cdl!{ { p := alice } ⟨ p.age = 3; ⟩ p.age == 3 }
#check cdl!{ ⟨ p = alice; p.age = 3; ⟩ find(storage, p.age) = 3 }
#check cdl!{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
       ⟨ carolAcc = carol.account; carolAcc.balance = 1; ⟩ true }
#check cdl!{ ∀ uint y; y == a }
#check cdl!{ ⟨ if (alice.age == 4) { uint z = 1; total = z; } else { total = 2; } ⟩ total == 1 }
#check cdl!{ ⟨ uint y = 1; ⟩ true ∧ y == 1 }

end Solidity.Examples.Tactics.CoreNotation
