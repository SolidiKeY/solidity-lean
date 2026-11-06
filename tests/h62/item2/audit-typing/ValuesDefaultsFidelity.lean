import tests.h62.item2.«audit-typing».DeclarationCensus
import tests.h62.item2.«audit-typing».ValuesDefaultsWitnesses

#audit_full_inputs Solidity.SVal.dfltBelow_irrel via H62.AuditTyping.ValuesDefaultsWitnesses.below_irrel
#audit_full_inputs Solidity.SVal.dfltBelow_dflt via H62.AuditTyping.ValuesDefaultsWitnesses.below_default
#audit_full_inputs Solidity.SFields.dfltBelow_eq via H62.AuditTyping.ValuesDefaultsWitnesses.fields_below
#audit_full_inputs Solidity.SVal.dflt_all via H62.AuditTyping.ValuesDefaultsWitnesses.default_value
#audit_full_inputs Solidity.SFields.dflt_all via H62.AuditTyping.ValuesDefaultsWitnesses.default_fields
#audit_full_inputs Solidity.SVal.dfltBelow_all via H62.AuditTyping.ValuesDefaultsWitnesses.default_below
#print axioms H62.AuditTyping.ValuesDefaultsWitnesses.below_irrel
#print axioms H62.AuditTyping.ValuesDefaultsWitnesses.below_default
#print axioms H62.AuditTyping.ValuesDefaultsWitnesses.fields_below
#print axioms H62.AuditTyping.ValuesDefaultsWitnesses.default_value
#print axioms H62.AuditTyping.ValuesDefaultsWitnesses.default_fields
#print axioms H62.AuditTyping.ValuesDefaultsWitnesses.default_below
#print axioms H62.AuditTyping.ValuesDefaultsWitnesses.zero_rank_rejected

-- Omitting the shared predicate's three hypotheses must be rejected.
/-- error: full-input mismatch for Solidity.SVal.dfltBelow_all -/
#guard_msgs in
#audit_full_inputs Solidity.SVal.dfltBelow_all via H62.AuditTyping.ValuesDefaultsWitnesses.below_default
