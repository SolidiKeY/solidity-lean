import Solidity.Yul.Static

/-! Exact axiom reports for the foundational exported contracts. -/
/-- info: 'Solidity.Yul.powBits_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Yul.powBits_correct
/-- info: 'Solidity.Yul.powWord_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Yul.powWord_correct
/-- info: 'Solidity.Yul.div_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Yul.div_zero
/-- info: 'Solidity.Yul.mod_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Yul.mod_zero
/-- info: 'Solidity.Yul.checkAccess_iff' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Yul.checkAccess_iff
/-- info: 'Solidity.Yul.resolve_sound' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Yul.resolve_sound
/-- info: 'Solidity.Yul.resolve_complete' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Yul.resolve_complete
/-- info: 'Solidity.Yul.fresh_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Yul.fresh_iff
/-- info: 'Solidity.Yul.checkLiteral_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Yul.checkLiteral_iff
/-- info: 'Solidity.Yul.checkLiteral_value' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Yul.checkLiteral_value
