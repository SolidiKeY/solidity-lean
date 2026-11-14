import Solidity.Goals.Hash

namespace Solidity.Goals

/--
info: open Solidity.Goals.compilerCorrectCollisionFree ← Solidity.Hash.compiler_correct_collisionFree plan e4-hash-bridge
-/
#guard_msgs in
#roadmap_goal compilerCorrectCollisionFree

open HashContract Solidity.Evm

/-- Skipping a KECCAK instruction does not invent a runtime hash query. -/
example (m : Numeric) : queriesAt (.running [.keccakArr] 1 [] m) = [] := rfl

/-- The exact write event retains its numeric address and value. -/
example (m : Numeric) (a v : Fin W) :
    numericAccessAt (.running [.sstore] 0 [] { m with stack := [a, v] }) =
      [.write a v] := rfl

/-- A loop body's pending jump faults instead of escaping to its continuation. -/
example (F : Roadmap.Fixed) (m : Numeric) (c b rest : List Instr) :
    tick (numericAtom F) numericTest (.running [] 1 [.body c b rest] m) =
      .halted .fault := rfl

/-- A finished prefix cannot emit another query through terminal stuttering. -/
example (F : Roadmap.Fixed) (r : Result Numeric) :
    queriesAt (tick (numericAtom F) numericTest (.halted r)) = [] := rfl

/-- Collision freedom cannot erase the independent one-query root-hit event. -/
example :
    (Hash.tuples 2 1).countP
      (Hash.CollisionBridge.eagerPremiseFails (fun _ => (0 : Nat)) [0] 2 1 [0] 1) = 1 :=
  Hash.CollisionBridge.one_query_root_hit

end Solidity.Goals
