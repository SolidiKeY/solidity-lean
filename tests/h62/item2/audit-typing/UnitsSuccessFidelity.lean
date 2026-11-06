import tests.h62.item2.«audit-typing».DeclarationCensus
import tests.h62.item2.«audit-typing».UnitsSuccess

#audit_full_inputs Solidity.Frontend.Static.unitsChecker_complete via H62.AuditTyping.UnitsSuccess.complete_inputs
#print axioms H62.AuditTyping.UnitsSuccess.units_success
#print axioms H62.AuditTyping.UnitsSuccess.overload_program_accepted
#print axioms H62.AuditTyping.UnitsSuccess.reject_all_fails_success
#print axioms H62.AuditTyping.UnitsSuccess.missing_import_rejected
#print axioms H62.AuditTyping.UnitsSuccess.complete_inputs
