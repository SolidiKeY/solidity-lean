import tests.h62.item2.«audit-language».WitnessAccounting

/-!
Guarded regression: a mismatched tuple, constructor or data declaration must
never be accepted as a kernel theorem association. These are expected failures,
not positive witness or input-feasibility credit.
-/
/-- error: hypothesis telescope mismatch -/
#guard_msgs in
#audit_witness Solidity.H62.AuditLanguage.feature_exclusion_full for Solidity.KeySort.le_trans

/-- error: witness is not a kernel theorem -/
#guard_msgs in
#audit_witness Solidity.KeySort.bool for Solidity.KeySort.le_any

/-- error: target is not a kernel theorem -/
#guard_msgs in
#audit_witness Solidity.H62.AuditLanguage.sort_name_full for Solidity.KeySort.bool
