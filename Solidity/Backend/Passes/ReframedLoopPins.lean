import Solidity.Backend.Passes.ReframedLoops

/-! Exact observed standard-only loop-frame headline guards. -/
/-- info: 'Solidity.Backend.Passes.loops_shrinking_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.loops_shrinking_link
/-- info: 'Solidity.Backend.Passes.loop_scopes_shrinking_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.loop_scopes_shrinking_link
/-- info: 'Solidity.Backend.Passes.ReframedLoopControls.bounds' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReframedLoopControls.bounds
/-- info: 'Solidity.Backend.Passes.ReframedLoopControls.reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ReframedLoopControls.reached
