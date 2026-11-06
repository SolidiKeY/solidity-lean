import tests.h62.item2.«audit-typing».DeclarationCensus
import tests.h62.item2.«audit-typing».ValuesHeredWitnesses

#audit_full_inputs Solidity.SVal.all_mono via H62.AuditTyping.ValuesHeredWitnesses.val_mono
#audit_full_inputs Solidity.SFields.all_mono via H62.AuditTyping.ValuesHeredWitnesses.fields_mono
#audit_full_inputs Solidity.SList.all_mono via H62.AuditTyping.ValuesHeredWitnesses.list_mono
#audit_full_inputs Solidity.SVec.all_mono via H62.AuditTyping.ValuesHeredWitnesses.vec_mono
#audit_full_inputs Solidity.SMap.all_mono via H62.AuditTyping.ValuesHeredWitnesses.map_mono
#audit_full_inputs Solidity.SVal.allB_iff via H62.AuditTyping.ValuesHeredWitnesses.val_decides
#audit_full_inputs Solidity.SFields.allB_iff via H62.AuditTyping.ValuesHeredWitnesses.fields_decides
#audit_full_inputs Solidity.SList.allB_iff via H62.AuditTyping.ValuesHeredWitnesses.list_decides
#audit_full_inputs Solidity.SVec.allB_iff via H62.AuditTyping.ValuesHeredWitnesses.vec_decides
#audit_full_inputs Solidity.SMap.allB_iff via H62.AuditTyping.ValuesHeredWitnesses.map_decides
#print axioms H62.AuditTyping.ValuesHeredWitnesses.val_mono
#print axioms H62.AuditTyping.ValuesHeredWitnesses.fields_mono
#print axioms H62.AuditTyping.ValuesHeredWitnesses.list_mono
#print axioms H62.AuditTyping.ValuesHeredWitnesses.vec_mono
#print axioms H62.AuditTyping.ValuesHeredWitnesses.map_mono
#print axioms H62.AuditTyping.ValuesHeredWitnesses.val_decides
#print axioms H62.AuditTyping.ValuesHeredWitnesses.fields_decides
#print axioms H62.AuditTyping.ValuesHeredWitnesses.list_decides
#print axioms H62.AuditTyping.ValuesHeredWitnesses.vec_decides
#print axioms H62.AuditTyping.ValuesHeredWitnesses.map_decides
#print axioms H62.AuditTyping.ValuesHeredWitnesses.reject_node_test_not_decides

-- A decision bundle cannot replace the monotonicity bundle's global and
-- correlated per-input hypotheses.
/-- error: full-input mismatch for Solidity.SVal.all_mono -/
#guard_msgs in
#audit_full_inputs Solidity.SVal.all_mono via H62.AuditTyping.ValuesHeredWitnesses.val_decides

#print axioms H62.AuditTyping.ValuesHeredWitnesses.capability_without_feasible_input

#print axioms H62.AuditTyping.ValuesHeredWitnesses.empty_fields_feasible
