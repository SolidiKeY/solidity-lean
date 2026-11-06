import tests.h62.item2.«audit-calculus».JoinWalkWitnesses

/-! Negative verifier control kept separate from audited source coverage.
The rejected command creates no failed theorem or proof placeholder. -/
/-- error: witness does not match the exact unchanged joint telescope -/
#guard_msgs in
#verify_joint_dag Nat.succ_ne_zero with H62.AuditCalculus.JoinWalk.closed_input
