import Solidity.Frontend.Testing

/-!
# Fresh arrays and allocation-size captures

Primitive reads close through the fresh-array memory clauses. Nested copies
remain open to the closer; their initial-state executions check the interpreter
separately. The effectful target checks that the size is captured before its
receiver increments the same local.
-/

solc_import "../../../tests/solc/NewArrays.ast.json" hash 0x969196cb36bff2f7
  as Solkey.Migration.NewArrays testing

namespace Solidity.Examples.Tactics.NewArrays

theorem storageRoot_initial :
    (Prog.run (State.init Solkey.Migration.NewArrays)
      Solkey.Migration.NewArrays.storageRoot).isOk = true := by
  decide +kernel

theorem nestedDefaults_initial :
    (Prog.run (State.init Solkey.Migration.NewArrays)
      Solkey.Migration.NewArrays.nestedDefaults).isOk = true := by
  decide +kernel

theorem sizeOnce_initial :
    (Prog.run (State.init Solkey.Migration.NewArrays)
      Solkey.Migration.NewArrays.sizeOnce).isOk = true := by
  decide +kernel

theorem memorySizeOnce_initial :
    (Prog.run (State.init Solkey.Migration.NewArrays)
      Solkey.Migration.NewArrays.memorySizeOnce).isOk = true := by
  decide +kernel

theorem receiverAfterSize_initial :
    (Prog.run (State.init Solkey.Migration.NewArrays)
      Solkey.Migration.NewArrays.receiverAfterSize).isOk = true := by
  decide +kernel

theorem falsePost_initial :
    (Prog.run (State.init Solkey.Migration.NewArrays)
      Solkey.Migration.NewArrays.falsePost).isOk = false := by
  decide +kernel

theorem emptyRead_initial :
    (Prog.run (State.init Solkey.Migration.NewArrays)
      Solkey.Migration.NewArrays.emptyRead).isOk = false := by
  decide +kernel

end Solidity.Examples.Tactics.NewArrays
