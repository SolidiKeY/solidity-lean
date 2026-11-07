import Solidity.Frontend.Static.Closure
import tests.h62.item2.«audit-typing».DeclarationCensus
import tests.h62.item2.«audit-typing».ValuesListsWitnesses

#audit_module Solidity.Typing.Values

#audit_witness Solidity.lookupBy_isSome_of_mem' via H62.AuditTyping.ValuesListsWitnesses.lookup_mem
#audit_witness Solidity.lookupBy_of_nodup via H62.AuditTyping.ValuesListsWitnesses.lookup_nodup
#audit_witness Solidity.mem_setBy via H62.AuditTyping.ValuesListsWitnesses.mem_set
#audit_witness Solidity.lookupBy_none_setBy via H62.AuditTyping.ValuesListsWitnesses.none_set
#audit_witness Solidity.nodupKeysB_setBy' via H62.AuditTyping.ValuesListsWitnesses.nodup_set
#audit_witness Solidity.setBy_of_lookupBy via H62.AuditTyping.ValuesListsWitnesses.set_lookup
#audit_witness Solidity.lookupBy_append_none via H62.AuditTyping.ValuesListsWitnesses.lookup_append
#audit_witness Solidity.setBy_append_none via H62.AuditTyping.ValuesListsWitnesses.set_append
#audit_witness Solidity.nodupKeysB_mid via H62.AuditTyping.ValuesListsWitnesses.nodup_mid

#print axioms H62.AuditTyping.ValuesListsWitnesses.lookup_mem
#print axioms H62.AuditTyping.ValuesListsWitnesses.lookup_nodup
#print axioms H62.AuditTyping.ValuesListsWitnesses.mem_set
#print axioms H62.AuditTyping.ValuesListsWitnesses.none_set
#print axioms H62.AuditTyping.ValuesListsWitnesses.nodup_set
#print axioms H62.AuditTyping.ValuesListsWitnesses.set_lookup
#print axioms H62.AuditTyping.ValuesListsWitnesses.lookup_append
#print axioms H62.AuditTyping.ValuesListsWitnesses.set_append
#print axioms H62.AuditTyping.ValuesListsWitnesses.nodup_mid

-- Refuse a witness that drops the nodup premise while keeping membership.
/-- error: premise mismatch for Solidity.lookupBy_of_nodup -/
#guard_msgs in
#audit_witness Solidity.lookupBy_of_nodup via H62.AuditTyping.ValuesListsWitnesses.lookup_mem
