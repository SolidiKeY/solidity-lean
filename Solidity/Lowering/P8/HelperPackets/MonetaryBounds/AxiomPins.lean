import Solidity.Lowering.P8.HelperPackets.MonetaryBounds.Controls

/-! Exact transitive axiom pins for every helper law and kernel control. -/

/-- info: 'Solidity.Source.Monetary.credit_debit_roundtrip' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.credit_debit_roundtrip

/-- info: 'Solidity.Source.Monetary.debit_credit_roundtrip' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.debit_credit_roundtrip

/-- info: 'Solidity.Source.Monetary.checkedWord_iff' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.checkedWord_iff

/-- info: 'Solidity.Source.Monetary.debit_eq_some_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.debit_eq_some_iff

/-- info: 'Solidity.Source.Monetary.credit_eq_some_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.credit_eq_some_iff

/-- info: 'Solidity.Source.Monetary.reverse_roundtrip_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.reverse_roundtrip_iff

/-- info: 'Solidity.Source.Monetary.boundary_zero_fits' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.boundary_zero_fits

/-- info: 'Solidity.Source.Monetary.boundary_zero_checked' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.boundary_zero_checked

/-- info: 'Solidity.Source.Monetary.boundary_zero_debit_zero' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.boundary_zero_debit_zero

/-- info: 'Solidity.Source.Monetary.boundary_zero_credit_zero' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.boundary_zero_credit_zero

/-- info: 'Solidity.Source.Monetary.boundary_zero_view' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.boundary_zero_view

/-- info: 'Solidity.Source.Monetary.boundary_max_fits' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.boundary_max_fits

/-- info: 'Solidity.Source.Monetary.boundary_max_checked' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.boundary_max_checked

/-- info: 'Solidity.Source.Monetary.boundary_max_debit_zero' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.boundary_max_debit_zero

/-- info: 'Solidity.Source.Monetary.boundary_max_credit_zero' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.boundary_max_credit_zero

/-- info: 'Solidity.Source.Monetary.boundary_max_view' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.boundary_max_view

/-- info: 'Solidity.Source.Monetary.boundary_limit_fits' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.boundary_limit_fits

/-- info: 'Solidity.Source.Monetary.boundary_limit_checked' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.boundary_limit_checked

/-- info: 'Solidity.Source.Monetary.boundary_limit_debit_zero' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.boundary_limit_debit_zero

/-- info: 'Solidity.Source.Monetary.boundary_limit_credit_zero' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.boundary_limit_credit_zero

/-- info: 'Solidity.Source.Monetary.boundary_limit_view' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.boundary_limit_view

/-- info: 'Solidity.Source.Monetary.boundary_above_fits' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.boundary_above_fits

/-- info: 'Solidity.Source.Monetary.boundary_above_checked' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.boundary_above_checked

/-- info: 'Solidity.Source.Monetary.boundary_above_debit_zero' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.boundary_above_debit_zero

/-- info: 'Solidity.Source.Monetary.boundary_above_credit_zero' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.boundary_above_credit_zero

/-- info: 'Solidity.Source.Monetary.boundary_above_view' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.boundary_above_view

/-- info: 'Solidity.Source.Monetary.zero_unaffordable' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.zero_unaffordable

/-- info: 'Solidity.Source.Monetary.max_affordable' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.max_affordable

/-- info: 'Solidity.Source.Monetary.limit_affordable' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.limit_affordable

/-- info: 'Solidity.Source.Monetary.above_affordable' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.above_affordable

/-- info: 'Solidity.Source.Monetary.zero_credit_max' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.zero_credit_max

/-- info: 'Solidity.Source.Monetary.max_credit_refused' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.max_credit_refused

/-- info: 'Solidity.Source.Monetary.limit_credit_refused' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.limit_credit_refused

/-- info: 'Solidity.Source.Monetary.above_credit_refused' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.above_credit_refused

/-- info: 'Solidity.Source.Monetary.max_forward_roundtrip' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.max_forward_roundtrip

/-- info: 'Solidity.Source.Monetary.max_reverse_roundtrip' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.max_reverse_roundtrip

/-- info: 'Solidity.Source.Monetary.reverse_without_fits_counterexample' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.reverse_without_fits_counterexample

/-- info: 'Solidity.Source.Monetary.above_reverse_counterexample' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.above_reverse_counterexample

/-- info: 'Solidity.Source.Monetary.checked_rejects_wrong_word' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.checked_rejects_wrong_word

/-- info: 'Solidity.Source.Monetary.max_unaffordable' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.max_unaffordable
