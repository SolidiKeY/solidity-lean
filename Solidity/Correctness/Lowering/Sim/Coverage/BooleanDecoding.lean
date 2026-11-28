import Solidity.Correctness.Lowering.Sim.Coverage.BooleanStatements

/-! Completeness of the existing decoder on the approved Boolean input
boundary, toward `Solidity.Goals.loweringBySimulation`. No decoder is added. -/
namespace Solidity.Correctness.Lowering.Sim.Coverage.BooleanDomain

open Solidity.Goals.Shrink.Lowering

/-- Every approved input decodes to the singleton resolution of an actual
Source statement derivation. Production and acceptance are not assumed here. -/
theorem Input.decoded_stmt {b u} (h : Input b u) :
    ∃ (C : Source.Ctx) (L : List (String × Source.STy)) (s : Source.Syn (.stmt .body))
      (d : Source.StmtD C L s L),
      Total.Decode.decode (request b u) = some (Total.SourceProgram.ofStmt d.toR) := by
  exact (BooleanStatements.of_while h).decoded_stmt

end Solidity.Correctness.Lowering.Sim.Coverage.BooleanDomain
