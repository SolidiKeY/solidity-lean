import Solidity.Backend.Passes.RelatedMemoryCaptureControls

/-- info: 'Solidity.Backend.Passes.RelatedMemoryCapture.execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.RelatedMemoryCapture.execution

/-- info: 'Solidity.Backend.Passes.RelatedMemoryCapture.Controls.aligned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.RelatedMemoryCapture.Controls.aligned

/-- info: 'Solidity.Backend.Passes.RelatedMemoryCapture.Controls.input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.RelatedMemoryCapture.Controls.input

/-- info: 'Solidity.Backend.Passes.RelatedMemoryCapture.Controls.source_heap_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.RelatedMemoryCapture.Controls.source_heap_live

/-- info: 'Solidity.Backend.Passes.RelatedMemoryCapture.Controls.initial_vector' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.RelatedMemoryCapture.Controls.initial_vector

/-- info: 'Solidity.Backend.Passes.RelatedMemoryCapture.Controls.complete_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.RelatedMemoryCapture.Controls.complete_vector

/-- info: 'Solidity.Backend.Passes.RelatedMemoryCapture.Controls.wrong_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.RelatedMemoryCapture.Controls.wrong_vector

/-- info: 'Solidity.Backend.Passes.RelatedMemoryCapture.Controls.wrong_reference_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.RelatedMemoryCapture.Controls.wrong_reference_refused

/-- info: 'Solidity.Backend.Passes.RelatedMemoryCapture.Controls.skipped_capture_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.RelatedMemoryCapture.Controls.skipped_capture_refused

/-- info: 'Solidity.Backend.Passes.RelatedMemoryCapture.Controls.wrong_relation_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.RelatedMemoryCapture.Controls.wrong_relation_refused

/-- info: 'Solidity.Backend.Passes.RelatedMemoryCapture.Controls.corrupted_tail_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.RelatedMemoryCapture.Controls.corrupted_tail_refused

/-- info: 'Solidity.Backend.Passes.RelatedMemoryCapture.Controls.application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.Passes.RelatedMemoryCapture.Controls.application

