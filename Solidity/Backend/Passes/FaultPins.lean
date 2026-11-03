import Solidity.Backend.Passes.FaultControls

/-! Exact standard-only pins for typed reached-fault transport. -/
/-- info: 'Solidity.Backend.Passes.compilation_mapped_fault_reached_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.compilation_mapped_fault_reached_iff
/-- info: 'Solidity.Backend.Passes.compilation_triple_fault_reached_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.compilation_triple_fault_reached_iff
/-- info: 'Solidity.Backend.Passes.compilation_triple_fault_reached_left_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.compilation_triple_fault_reached_left_iff
/-- info: 'Solidity.Backend.Passes.compilation_third_fault_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.compilation_third_fault_shared
/-- info: 'Solidity.Backend.Passes.FaultControls.immediate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FaultControls.immediate
/-- info: 'Solidity.Backend.Passes.FaultControls.middle_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FaultControls.middle_witness
/-- info: 'Solidity.Backend.Passes.FaultControls.third_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FaultControls.third_witness
/-- info: 'Solidity.Backend.Passes.FaultControls.shared_third' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FaultControls.shared_third
/-- info: 'Solidity.Backend.Passes.FaultControls.distinct_terminals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FaultControls.distinct_terminals
/-- info: 'Solidity.Backend.Passes.FaultControls.wrong_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FaultControls.wrong_stage
/-- info: 'Solidity.Backend.Passes.FaultControls.middle_reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FaultControls.middle_reached
/-- info: 'Solidity.Backend.Passes.FaultControls.third_reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.FaultControls.third_reached
