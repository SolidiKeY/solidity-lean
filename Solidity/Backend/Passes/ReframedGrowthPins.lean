import Solidity.Backend.Passes.ReframedGrowth

/-- info: 'Solidity.Backend.Passes.allocator_growth_reservation_shrink' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.allocator_growth_reservation_shrink
/-- info: 'Solidity.Backend.Passes.allocator_growth_reframed_comp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.allocator_growth_reframed_comp
/-- info: 'Solidity.Backend.Passes.ReframedGrowthControls.reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReframedGrowthControls.reached
/-- info: 'Solidity.Backend.Passes.ReframedGrowthControls.skipped_allocation_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReframedGrowthControls.skipped_allocation_cost
