import Solidity.Frontend.Testing

/-! Atomic memory-to-storage push, copy independence, recycled slots and
a receiver whose selector changes when the append happens. -/

solc_import "../../../tests/solc/MemoryPush.ast.json" hash 0x0477c52e82f8eb49
  as Solkey.Migration.MemoryPush testing

namespace Solidity.Examples.Tactics.MemoryPush

/-- All nine compiled functions remain available to the proof runner. -/
example : Solkey.Migration.MemoryPush.report.length = 9 := rfl

/-- Each source case elaborates into the typed model. -/
example : (Solkey.Migration.MemoryPush.report.all fun r =>
    decide (r.status = .elaborated)) = true := by decide +kernel

/-- A pushed memory array is copied, with its length. -/
example : (Prog.run (State.init Solkey.Migration.MemoryPush)
    Solkey.Migration.MemoryPush.arrayCopy).isOk = true := by decide +kernel

/-- Mutating the memory source does not mutate the storage copy. -/
example : (Prog.run (State.init Solkey.Migration.MemoryPush)
    Solkey.Migration.MemoryPush.arrayFalse).halt? = some .panic := by decide +kernel

/-- A memory struct is copied independently too. -/
example : (Prog.run (State.init Solkey.Migration.MemoryPush)
    Solkey.Migration.MemoryPush.structCopy).isOk = true := by decide +kernel

/-- A recycled slot takes the copied array's new length and contents. -/
example : (Prog.run (State.init Solkey.Migration.MemoryPush)
    Solkey.Migration.MemoryPush.recycledSlot).isOk = true := by decide +kernel

/-- The receiver `cube[cube[0].length]` is resolved before its length changes. -/
example : (Prog.run (State.init Solkey.Migration.MemoryPush)
    Solkey.Migration.MemoryPush.receiverUsesLength).isOk = true := by decide +kernel

/-- The false receiver assertion panics after the append instead of reverting early. -/
example : (Prog.run (State.init Solkey.Migration.MemoryPush)
    Solkey.Migration.MemoryPush.receiverFalse).halt? = some .panic := by decide +kernel

/-- A complex memory source is copied before its original is mutated. -/
example : (Prog.run (State.init Solkey.Migration.MemoryPush)
    Solkey.Migration.MemoryPush.complexMemorySource).isOk = true := by decide +kernel

/-- Aliasing the complex memory source is refuted. -/
example : (Prog.run (State.init Solkey.Migration.MemoryPush)
    Solkey.Migration.MemoryPush.complexMemoryFalse).halt? = some .panic := by decide +kernel

/-- An invalid memory source index reverts at the capture. -/
example : (Prog.run (State.init Solkey.Migration.MemoryPush)
    Solkey.Migration.MemoryPush.badMemorySource).halt? = some .revert := by decide +kernel

local instance : InContract := ⟨Solkey.Migration.MemoryPush⟩

/-- The former append/assignment expansion incorrectly resolves the receiver twice. -/
def duplicatedReceiver := sol{
  delete cube;
  cube.push(); cube.push();
  uint[] memory row = new uint[](1);
  row[0] = 29;
  cube[cube[0].length].push();
  cube[cube[0].length][cube[cube[0].length].length - 1] = row;
}

/-- Its second lookup selects the empty second row and reverts. -/
example : (Prog.run (State.init Solkey.Migration.MemoryPush)
    duplicatedReceiver).halt? = some .revert := by decide +kernel

end Solidity.Examples.Tactics.MemoryPush
