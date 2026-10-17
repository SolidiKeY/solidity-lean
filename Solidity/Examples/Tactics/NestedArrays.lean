import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.Close

/-!
# Nested storage arrays

The shapes of solkey's `contracts/ArrayMatrix*.sol` (`uint[][]`): a
history that starts by deleting the array, then pushes rows and writes
them at literal indices.  solkey closes each index's `inBounds` branch at
its statement; the reduction does the same (`foldAt`,
`Calculus/DecideScoped.lean`), so a path no longer carries the storage it
was checked in (`aliasSharesWrites`: twelve storage updates, a tree
of 900,000 nodes before).  Such a history is concrete (`LTm.known?`,
`Calculus/ReadBounds.lean`): every live length is known, and the closer
takes it past `normalizationDepth` storage updates, up to `concreteDepth`
(`deleteRowKeepsOuterLength`).  A `pop` leaves it unknown (`Op2.exposes`;
`Examples/Tactics/Dangling.lean` keeps those rounds refused).
-/

namespace Solidity.Examples.Tactics.NestedArrays

local instance : InContract := ⟨StandardExample⟩

open scoped Scoped

/-- Writes through a row alias reach the array: twelve storage updates. -/
theorem aliasSharesWrites : ⊨ dl!{ defined(wt(storage)) → ⟨
    delete matrix; matrix.push(); matrix.push();
    matrix[0].push(); matrix[0].push(); matrix[0][0] = 11; matrix[0][1] = 12;
    matrix[1].push(); matrix[1].push(); matrix[1][0] = 21; matrix[1][1] = 22;
    uint[] storage row = matrix[0]; row[0] = 41; ⟩ matrix[0][0] == 41 } := by
  sol_prove

/-- Deleting a row keeps the outer length and empties the row: thirteen
storage updates and more, past `normalizationDepth`. -/
theorem deleteRowKeepsOuterLength : ⊨ dl!{ defined(wt(storage)) → ⟨
    delete matrix; matrix.push(); matrix.push();
    matrix[0].push(); matrix[0].push(); matrix[0][0] = 11; matrix[0][1] = 12;
    matrix[1].push(); matrix[1].push(); matrix[1][0] = 21; matrix[1][1] = 22;
    delete matrix[0]; matrix[0].push(); ⟩
    matrix.length == 2 && matrix[0].length == 1 && matrix[0][0] == 0 &&
      matrix[1][1] == 22 } := by
  sol_prove

end Solidity.Examples.Tactics.NestedArrays
