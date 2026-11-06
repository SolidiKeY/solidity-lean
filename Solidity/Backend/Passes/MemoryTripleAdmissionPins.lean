import Solidity.Backend.Passes.MemoryTripleAdmissionControls

namespace Solidity.Backend.Passes.MemoryTripleAdmission
/-- info: 'Solidity.Backend.Passes.MemoryTripleAdmission.links' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms links
/-- info: 'Solidity.Backend.Passes.MemoryTripleAdmission.public_admission' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms public_admission
/-- info: 'Solidity.Backend.Passes.MemoryTripleAdmission.Controls.source_both' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.source_both
/-- info: 'Solidity.Backend.Passes.MemoryTripleAdmission.Controls.shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.shared
/-- info: 'Solidity.Backend.Passes.MemoryTripleAdmission.Controls.complete_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.complete_result
/-- info: 'Solidity.Backend.Passes.MemoryTripleAdmission.Controls.third_frame_required' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.third_frame_required
/-- info: 'Solidity.Backend.Passes.MemoryTripleAdmission.Controls.reached_third_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Controls.reached_third_failure
end Solidity.Backend.Passes.MemoryTripleAdmission
