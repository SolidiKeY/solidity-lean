import Solidity.Backend.Passes.AllocatedReferenceReadControls

namespace Solidity.Backend.Passes.AllocatedReferenceRead
/-- info: 'Solidity.Backend.Passes.AllocatedReferenceRead.reader_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reader_source
/-- info: 'Solidity.Backend.Passes.AllocatedReferenceRead.wrong_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_source
/-- info: 'Solidity.Backend.Passes.AllocatedReferenceRead.source_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_success
/-- info: 'Solidity.Backend.Passes.AllocatedReferenceRead.source_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_failure
/-- info: 'Solidity.Backend.Passes.AllocatedReferenceRead.execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms execution
/-- info: 'Solidity.Backend.Passes.AllocatedReferenceRead.Controls.runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.runs
/-- info: 'Solidity.Backend.Passes.AllocatedReferenceRead.Controls.complete_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.complete_memory
/-- info: 'Solidity.Backend.Passes.AllocatedReferenceRead.Controls.corrupted_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.corrupted_tail
end Solidity.Backend.Passes.AllocatedReferenceRead
