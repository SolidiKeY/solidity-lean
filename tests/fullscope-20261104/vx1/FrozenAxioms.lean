import Solidity.Language.EnvironmentFields.FrozenControls

/-! Kernel dependencies of the frozen D1–D6 contracts (V1) and their controls.
An inventory, not a pin: every line must print only standard axioms. -/

#print axioms Solidity.Roadmap.FullScope.V1.D1.forward_oracle
#print axioms Solidity.Roadmap.FullScope.V1.D1.backward_oracle
#print axioms Solidity.Roadmap.FullScope.V1.d5_of_certificate
#print axioms Solidity.Roadmap.FullScope.V1.Mode.observe_le
#print axioms Solidity.Roadmap.FullScope.V1.Mode.observe_optimizer
#print axioms Solidity.Roadmap.FullScope.V1.D1.toD6
#print axioms Solidity.Roadmap.FullScope.V1.Contract.compiles
#print axioms Solidity.Roadmap.FullScope.V1.rejecting_refused
#print axioms Solidity.Roadmap.FullScope.V1.forward_completes
#print axioms Solidity.Roadmap.FullScope.V1.Controls.witness
#print axioms Solidity.Roadmap.FullScope.V1.Controls.optimizerWitness
#print axioms Solidity.Roadmap.FullScope.V1.Controls.witness_live
#print axioms Solidity.Roadmap.FullScope.V1.Controls.oracle_live
#print axioms Solidity.Roadmap.FullScope.V1.Controls.d3_live
#print axioms Solidity.Roadmap.FullScope.V1.Controls.creation_at_limits
#print axioms Solidity.Roadmap.FullScope.V1.Controls.rejecting_refused
#print axioms Solidity.Roadmap.FullScope.V1.Controls.reverting_refused
#print axioms Solidity.Roadmap.FullScope.V1.Controls.empty_relation_refused
#print axioms Solidity.Roadmap.FullScope.V1.Controls.shifted_relation_refused
#print axioms Solidity.Roadmap.FullScope.V1.Controls.overlap_refused
#print axioms Solidity.Roadmap.FullScope.V1.Controls.rewriting_optimizer_refused
#print axioms Solidity.Roadmap.FullScope.V1.Controls.extra_event_refused
#print axioms Solidity.Roadmap.FullScope.V1.Controls.always_failing_refused
#print axioms Solidity.Roadmap.FullScope.V1.Controls.nothing_admitted_refused
