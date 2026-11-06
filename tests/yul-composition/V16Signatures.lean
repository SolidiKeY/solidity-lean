import Solidity.Roadmap.V16.Relational
import Solidity.Yul.World.Observations

/-! Actual V16 signatures are inspected, not assumed as an assembly certificate.
The general observation parameter can retain full Yul/log+emit observations;
concrete Lang/pass/certificate and guards still must be produced by owners. -/
#check @Solidity.Roadmap.V16.completion_at_need
#check @Solidity.Roadmap.V16.composed_completion
#check @Solidity.Roadmap.V16.composed_observation
#check Solidity.Yul.World.Observation
#print axioms Solidity.Roadmap.V16.composed_completion
