import tests.h62.item2.«audit-typing».DeclarationCensus
import tests.h62.item2.«audit-typing».ClosureWitnesses

#audit_witness Solidity.Frontend.Static.Reach.trans via H62.AuditTyping.ClosureWitnesses.reach_trans
#audit_witness Solidity.Frontend.Static.foldl_insertNew_superset via H62.AuditTyping.ClosureWitnesses.foldl_superset
#audit_witness Solidity.Frontend.Static.foldl_insertNew_mem via H62.AuditTyping.ClosureWitnesses.foldl_mem
#audit_witness Solidity.Frontend.Static.foldl_insertNew_sub via H62.AuditTyping.ClosureWitnesses.foldl_sub
#audit_witness Solidity.Frontend.Static.foldl_insertNew_nodup via H62.AuditTyping.ClosureWitnesses.foldl_nodup
#audit_witness Solidity.Frontend.Static.foldl_insertNew_grows via H62.AuditTyping.ClosureWitnesses.foldl_grows
#audit_witness Solidity.Frontend.Static.foldl_insertNew_same via H62.AuditTyping.ClosureWitnesses.foldl_same
#audit_witness Solidity.Frontend.Static.grow_superset via H62.AuditTyping.ClosureWitnesses.grow_superset
#audit_witness Solidity.Frontend.Static.grow_closed via H62.AuditTyping.ClosureWitnesses.grow_closed
#audit_witness Solidity.Frontend.Static.grow_grows via H62.AuditTyping.ClosureWitnesses.grow_grows
#audit_witness Solidity.Frontend.Static.grow_nodup via H62.AuditTyping.ClosureWitnesses.grow_nodup
#audit_witness Solidity.Frontend.Static.grow_sub via H62.AuditTyping.ClosureWitnesses.grow_sub
#audit_witness Solidity.Frontend.Static.iter_closed via H62.AuditTyping.ClosureWitnesses.iter_closed
#audit_witness Solidity.Frontend.Static.iter_superset via H62.AuditTyping.ClosureWitnesses.iter_superset
#audit_witness Solidity.Frontend.Static.iter_nodup via H62.AuditTyping.ClosureWitnesses.iter_nodup
#audit_witness Solidity.Frontend.Static.iter_sub via H62.AuditTyping.ClosureWitnesses.iter_sub
#audit_witness Solidity.Frontend.Static.Nodup.length_le_of_subset via H62.AuditTyping.ClosureWitnesses.nodup_subset
#audit_witness Solidity.Frontend.Static.Closed.reach via H62.AuditTyping.ClosureWitnesses.closed_reach
#audit_witness Solidity.Frontend.Static.iter_sound via H62.AuditTyping.ClosureWitnesses.iter_sound
#audit_witness Solidity.Frontend.Static.iter_complete via H62.AuditTyping.ClosureWitnesses.iter_complete
#audit_witness Solidity.Frontend.Static.mem_reachable via H62.AuditTyping.ClosureWitnesses.mem_reachable

-- Kernel dependency reports for every simultaneous witness.
#print axioms H62.AuditTyping.ClosureWitnesses.reach_trans
#print axioms H62.AuditTyping.ClosureWitnesses.foldl_superset
#print axioms H62.AuditTyping.ClosureWitnesses.foldl_mem
#print axioms H62.AuditTyping.ClosureWitnesses.foldl_sub
#print axioms H62.AuditTyping.ClosureWitnesses.foldl_nodup
#print axioms H62.AuditTyping.ClosureWitnesses.foldl_grows
#print axioms H62.AuditTyping.ClosureWitnesses.foldl_same
#print axioms H62.AuditTyping.ClosureWitnesses.grow_superset
#print axioms H62.AuditTyping.ClosureWitnesses.grow_closed
#print axioms H62.AuditTyping.ClosureWitnesses.grow_grows
#print axioms H62.AuditTyping.ClosureWitnesses.grow_nodup
#print axioms H62.AuditTyping.ClosureWitnesses.grow_sub
#print axioms H62.AuditTyping.ClosureWitnesses.iter_closed
#print axioms H62.AuditTyping.ClosureWitnesses.iter_superset
#print axioms H62.AuditTyping.ClosureWitnesses.iter_nodup
#print axioms H62.AuditTyping.ClosureWitnesses.iter_sub
#print axioms H62.AuditTyping.ClosureWitnesses.nodup_subset
#print axioms H62.AuditTyping.ClosureWitnesses.closed_reach
#print axioms H62.AuditTyping.ClosureWitnesses.iter_sound
#print axioms H62.AuditTyping.ClosureWitnesses.iter_complete
#print axioms H62.AuditTyping.ClosureWitnesses.mem_reachable

#audit_witness Solidity.Frontend.Static.foldl_insertNew_length via H62.AuditTyping.ClosureWitnesses.foldl_length
#audit_witness Solidity.Frontend.Static.iter_closed_or_long via H62.AuditTyping.ClosureWitnesses.iter_closed_or_long
#print axioms H62.AuditTyping.ClosureWitnesses.foldl_length
#print axioms H62.AuditTyping.ClosureWitnesses.iter_closed_or_long

-- Negative fidelity control: omit the growth theorem's two simultaneous
-- membership premises and try to supply only the Nodup bundle instead.
/-- error: premise mismatch for Solidity.Frontend.Static.foldl_insertNew_grows -/
#guard_msgs in
#audit_witness Solidity.Frontend.Static.foldl_insertNew_grows via H62.AuditTyping.ClosureWitnesses.foldl_nodup
