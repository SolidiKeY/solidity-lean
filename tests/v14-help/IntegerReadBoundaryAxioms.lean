import Solidity.Backend.Aggregates.IntegerReadBoundaryWitness

/-- info: 'Solidity.Backend.Aggregates.IntegerReadBoundaryWitness.geometry' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Aggregates.IntegerReadBoundaryWitness.geometry

/-- info: 'Solidity.Backend.Aggregates.IntegerReadBoundaryWitness.selected_decodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Aggregates.IntegerReadBoundaryWitness.selected_decodes

/-- info: 'Solidity.Backend.Aggregates.IntegerReadBoundaryWitness.traversal_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Aggregates.IntegerReadBoundaryWitness.traversal_fails

/-- info: 'Solidity.Backend.Aggregates.IntegerReadBoundaryWitness.inhabited_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Aggregates.IntegerReadBoundaryWitness.inhabited_boundary
