import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.Close

/-!
# Nested storage arrays

The shapes of solkey's `contracts/Array*.sol`.  solkey closes each index's
`inBounds` branch at its statement; the reduction does the same (`foldAt`,
`Calculus/DecideScoped.lean`), so a path no longer carries the storage it
was checked in (`gridAliasSharesWrites`; such a `uint[][]` leaf was a tree
of 900,000 nodes before).  A history of updates at literal paths below
roots it deleted is concrete (`LTm.known?`, `Calculus/ReadBounds.lean`):
every live length is known, and the closer takes it past
`normalizationDepth` storage updates, up to `concreteDepth`
(`valuesPastDepth`).  An empty push of a reference element exposes the
old slot as it is (solkey's `storagePushLengthSave`), and a `pop` a
dangling one: either leaves the history unknown (`Op2.exposes`).
-/

namespace Solidity.Examples.Tactics.NestedArrays

private def Grid : Contract := contract!{ uint[2][2] grid; uint[] values; }

local instance : InContract := ⟨Grid⟩

open scoped Scoped

/-- Writes through a row alias reach the fixed matrix. -/
theorem gridAliasSharesWrites : ⊨ᶠ dl!{ wt(storage) → ⟨
    delete grid; grid[0][0] = 11; grid[0][1] = 12; grid[1][0] = 21; grid[1][1] = 22;
    uint[2] storage row = grid[0]; row[0] = 41; ⟩ grid[0][0] == 41 && grid[1][1] == 22 } := by
  sol_prove

/-- Thirteen pushes after a delete: fourteen storage updates, past
`normalizationDepth`. -/
theorem valuesPastDepth : ⊨ᶠ dl!{ wt(storage) → ⟨
    delete values; values.push(1); values.push(2); values.push(3); values.push(4);
    values.push(5); values.push(6); values.push(7); values.push(8); values.push(9);
    values.push(10); values.push(11); values.push(12); values.push(13); ⟩
    values.length == 13 && values[0] == 1 && values[12] == 13 } := by
  sol_prove

end Solidity.Examples.Tactics.NestedArrays
