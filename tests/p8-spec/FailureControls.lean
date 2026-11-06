import Solidity.Lowering.P8.FailureProjection
open Solidity.Lowering.P8.SpecFailures
-- Independently fixed plan-level controls, not Source execution or native comparisons.
#guard requestCutWitness.horizon = 3
#guard (points requestCutWitness).tx 7 = .runs 257 (some 0)
#guard (points requestCutWitness).tx 6 = .runs 7 none
#guard (points requestCutWitness).frame 0 = none
#guard (frameDiagonal (fun _ => Solidity.Source.FailureResources.noFailures (fun _ => 9))).frame 42 = some 0
#guard (frameDiagonal (fun _ => {tx := fun _ => .runs 9 none, frame := fun _ => some 17})).frame 42 = none
#guard (frameDiagonal (fun _ => Solidity.Source.FailureResources.noFailures (fun _ => 9))).tx 42 = .runs 0 none
