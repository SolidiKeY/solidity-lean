import tests.h62.item2.«audit-typing».DeclarationCensus
import tests.h62.item2.«audit-typing».ValuesOpsWitnesses

#audit_full_inputs Solidity.SVal.strip_all via H62.AuditTyping.ValuesOpsWitnesses.val_strip
#audit_full_inputs Solidity.SFields.strip_all via H62.AuditTyping.ValuesOpsWitnesses.fields_strip
#audit_full_inputs Solidity.SVec.strip_all via H62.AuditTyping.ValuesOpsWitnesses.vec_strip
#audit_full_inputs Solidity.SVal.defaultOf_all via H62.AuditTyping.ValuesOpsWitnesses.val_delete
#audit_full_inputs Solidity.SFields.defaultOf_all via H62.AuditTyping.ValuesOpsWitnesses.fields_delete
#audit_full_inputs Solidity.SVec.defaultOf_all via H62.AuditTyping.ValuesOpsWitnesses.vec_delete
#audit_full_inputs Solidity.SVal.overlay_all via H62.AuditTyping.ValuesOpsWitnesses.val_overlay
#audit_full_inputs Solidity.SFields.overlay_all via H62.AuditTyping.ValuesOpsWitnesses.fields_overlay
#audit_full_inputs Solidity.SVec.overlayOn_all via H62.AuditTyping.ValuesOpsWitnesses.vec_overlay
#print axioms H62.AuditTyping.ValuesOpsWitnesses.val_strip
#print axioms H62.AuditTyping.ValuesOpsWitnesses.fields_strip
#print axioms H62.AuditTyping.ValuesOpsWitnesses.vec_strip
#print axioms H62.AuditTyping.ValuesOpsWitnesses.val_delete
#print axioms H62.AuditTyping.ValuesOpsWitnesses.fields_delete
#print axioms H62.AuditTyping.ValuesOpsWitnesses.vec_delete
#print axioms H62.AuditTyping.ValuesOpsWitnesses.val_overlay
#print axioms H62.AuditTyping.ValuesOpsWitnesses.fields_overlay
#print axioms H62.AuditTyping.ValuesOpsWitnesses.vec_overlay
#print axioms H62.AuditTyping.ValuesOpsWitnesses.reject_array_not_all

/-- error: full-input mismatch for Solidity.SVal.overlay_all -/
#guard_msgs in
#audit_full_inputs Solidity.SVal.overlay_all via H62.AuditTyping.ValuesOpsWitnesses.val_strip
