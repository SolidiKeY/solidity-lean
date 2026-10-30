import Solidity.Lowering.V08.NestedControls
import Solidity.Lowering.V08.InheritedControls
import Solidity.Lowering.V08.PayableControls
import Solidity.Lowering.V08.RoleControls
import Solidity.Lowering.V08.CryptoControls
import Solidity.Lowering.V08.EmitControls
import Solidity.Lowering.V08.SelectorControls
import Solidity.Lowering.V08.ProjectionControls
import Solidity.Lowering.V08.MetadataControls
import Solidity.Lowering.V08.Controls
import Solidity.Lowering.V08.AbiControls
import Solidity.Lowering.V08.LibraryCreation
import Solidity.Lowering.V08.LibraryControls
import Solidity.Lowering.V08.CallbackControls

/-! Lane-local headline axiom output, pinned by the lane control inventory. -/
#print axioms Solidity.Lowering.V08.beBytes_layout
#print axioms Solidity.Lowering.V08.wordBytes_transport
#print axioms Solidity.Lowering.V08.panicData_transport
#print axioms Solidity.Lowering.V08.errorData_transport
#print axioms Solidity.Lowering.V08.catch_error_transport
#print axioms Solidity.Lowering.V08.panic_payload_injective
#print axioms Solidity.Lowering.V08.wordSequence_transport
#print axioms Solidity.Lowering.V08.callFrame_observeEntry
#print axioms Solidity.Lowering.V08.call_observeEntry
#print axioms Solidity.Lowering.V08.call_observeEntry_error_iff
#print axioms Solidity.Lowering.V08.call_observeEntry_comp
#print axioms Solidity.Lowering.V08.resetTransient_idem
#print axioms Solidity.Lowering.V08.transact_congr
#print axioms Solidity.Lowering.V08.transact_observe
#print axioms Solidity.Lowering.V08.transact_descendant_failure
#print axioms Solidity.Lowering.V08.transact_repeat
#print axioms Solidity.Lowering.V08.transact_wrong_halt
#print axioms Solidity.Lowering.V08.libraryCall_observe
#print axioms Solidity.Lowering.V08.tryCreate_observe
#print axioms Solidity.Lowering.V08.tryCreate_success_continuation_failure
#print axioms Solidity.Lowering.V08.AbiControls.reason_roundtrip
#print axioms Solidity.Lowering.V08.AbiControls.malformed_reason
#print axioms Solidity.Lowering.V08.AbiControls.panic_catch
#print axioms Solidity.Lowering.V08.AbiControls.wrong_panic

#print axioms Solidity.Lowering.V08.transact_atomic_descendant
#print axioms Solidity.Lowering.V08.rollback_observation

#print axioms Solidity.Lowering.V08.pad32_transport

#print axioms Solidity.Lowering.V08.beBytes_mod
#print axioms Solidity.Lowering.V08.natWordBytes_transport
#print axioms Solidity.Lowering.V08.errorData_transport_total
#print axioms Solidity.Lowering.V08.catch_error_transport_total
