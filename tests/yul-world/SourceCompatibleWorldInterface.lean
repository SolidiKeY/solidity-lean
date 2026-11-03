import Solidity.Yul.World.Callback
import Solidity.Yul.World.CallbackChecks
import Solidity.Yul.World.CallbackSuccess
import Solidity.Yul.World.CallbackSuccessChecks
import Solidity.Yul.World.CallerFrame
import Solidity.Yul.World.CallerFrameChecks
import Solidity.Yul.World.CreditEnvironment
import Solidity.Yul.World.FailureFuel
import Solidity.Yul.World.GeneralFailure
import Solidity.Yul.World.InstanceBoundary
import Solidity.Yul.World.KnownCall
import Solidity.Yul.World.KnownCallChecks
import Solidity.Yul.World.KnownStatic
import Solidity.Yul.World.PhysicalEnvironmentAnswer
import Solidity.Yul.World.PhysicalHeapPort
import Solidity.Yul.World.PhysicalPortChecks
import Solidity.Yul.World.PhysicalSlotPort
import Solidity.Yul.World.ReturningCall
import Solidity.Yul.World.ReturningFailure
import Solidity.Yul.World.ReturningStatic
import Solidity.Yul.World.ReturningStaticControls
import Solidity.Yul.World.ReturningTimeout
import Solidity.Yul.World.ScalarEmitPort
import Solidity.Yul.World.StateCall
import Solidity.Yul.World.StateCallRuntime
import tests.«yul-world».PhysicalFrameCalldataChecks

/-! Generated scoped signatures and actual kernel axiom reports. -/
#check Solidity.Yul.World.Callback.callbackGlob
#check Solidity.Yul.World.Callback.codeless_succeeds
#check Solidity.Yul.World.Callback.precompile_no_code
#check Solidity.Yul.World.Callback.invokeAt
#check Solidity.Yul.World.Callback.invoke
#check Solidity.Yul.World.Callback.prefixInvoke
#check Solidity.Yul.World.Callback.callerInvoke
#check Solidity.Yul.World.Callback.precompile_refusal
#check Solidity.Yul.World.CallbackChecks.suffix
#check Solidity.Yul.World.CallbackChecks.events
#check Solidity.Yul.World.CallbackChecks.after
#check Solidity.Yul.World.CallbackChecks.result
#check Solidity.Yul.World.CallbackChecks.actual_callback_dispatch
#check Solidity.Yul.World.CallbackChecks.actual_source_run
#check Solidity.Yul.World.CallbackChecks.invoke_actual
#check Solidity.Yul.World.CallbackChecks.completion_actual
#check Solidity.Yul.World.CallbackChecks.call_actual
#check Solidity.Yul.World.CallbackChecks.frame_and_trace
#check Solidity.Yul.World.CallbackSuccess.fallbackDecl
#check Solidity.Yul.World.CallbackSuccess.modifierDecl
#check Solidity.Yul.World.CallbackSuccess.env
#check Solidity.Yul.World.CallbackSuccess.modifierBody
#check Solidity.Yul.World.CallbackSuccess.fallbackBody
#check Solidity.Yul.World.CallbackSuccess.initial
#check Solidity.Yul.World.CallbackSuccess.callerExecution
#check Solidity.Yul.World.CallbackSuccess.credited
#check Solidity.Yul.World.CallbackSuccess.caller
#check Solidity.Yul.World.CallbackSuccess.observed
#check Solidity.Yul.World.CallbackSuccess.parent
#check Solidity.Yul.World.CallbackSuccess.callbackGlob
#check Solidity.Yul.World.CallbackSuccess.modifier_resolves
#check Solidity.Yul.World.CallbackSuccess.modifier_frame
#check Solidity.Yul.World.CallbackSuccess.invokeAt
#check Solidity.Yul.World.CallbackSuccess.invoke
#check Solidity.Yul.World.CallbackSuccess.prefixInvoke
#check Solidity.Yul.World.CallbackSuccess.suffix
#check Solidity.Yul.World.CallbackSuccess.events
#check Solidity.Yul.World.CallbackSuccess.after
#check Solidity.Yul.World.CallbackSuccess.result
#check Solidity.Yul.World.CallbackSuccess.source_run
#check Solidity.Yul.World.CallbackSuccess.invoke_actual
#check Solidity.Yul.World.CallbackSuccess.completion
#check Solidity.Yul.World.CallbackSuccess.call_actual
#check Solidity.Yul.World.CallbackSuccess.frame
#check Solidity.Yul.World.CallbackSuccess.receiver_balance
#check Solidity.Yul.World.CallbackSuccess.partialSuffix
#check Solidity.Yul.World.CallbackSuccess.partialState
#check Solidity.Yul.World.CallbackSuccess.partialResult
#check Solidity.Yul.World.CallbackSuccess.source_timeout
#check Solidity.Yul.World.CallbackSuccess.prefix_invoke
#check Solidity.Yul.World.CallbackSuccess.prefix_call
#check Solidity.Yul.World.CallbackSuccess.dirty_prefix_frame
#check Solidity.Yul.World.CallbackSuccess.output_copy
#check Solidity.Yul.World.CallbackSuccess.nonempty_caller
#check Solidity.Yul.World.CallbackSuccess.static_refusal
#check Solidity.Yul.World.CallbackSuccess.ordered_success_not_timeout
#check Solidity.Yul.World.CallbackSuccess.ordered_success_not_failure
#check Solidity.Yul.World.CallbackSuccess.no_fresh_timeout_buffer
#check Solidity.Yul.World.CallbackSuccess.unregistered
#check Solidity.Yul.World.CallbackSuccess.overflow
#check Solidity.Yul.World.CallbackSuccess.registration_refusal
#check Solidity.Yul.World.CallbackSuccess.range_refusal
#check Solidity.Yul.World.CallbackSuccess.context_refusal
#check Solidity.Yul.World.CallbackSuccess.precompile_refusal
#check Solidity.Yul.World.CallbackSuccess.missing_modifier
#check Solidity.Yul.World.CallbackSuccess.copiedState
#check Solidity.Yul.World.CallbackSuccess.owner_MemOK
#check Solidity.Yul.World.CallbackSuccess.exact_state_copy
#check Solidity.Yul.World.CallbackSuccess.copied_owner_MemOK
#check Solidity.Yul.World.CallbackSuccess.copied_aliases
#check Solidity.Yul.World.CallerFrame.sourceBoundary
#check Solidity.Yul.World.CallerFrame.sourceBoundary_exact
#check Solidity.Yul.World.CallerFrame.liftInvoke
#check Solidity.Yul.World.CallerFrame.liftInvoke_exact
#check Solidity.Yul.World.CallerFrame.liftInvoke_state
#check Solidity.Yul.World.CallerFrame.enterInstance_heap
#check Solidity.Yul.World.CallerFrame.runInstance
#check Solidity.Yul.World.CallerFrame.runInstance_frame
#check Solidity.Yul.World.CallerFrameChecks.receiver
#check Solidity.Yul.World.CallerFrameChecks.owner
#check Solidity.Yul.World.CallerFrameChecks.sender
#check Solidity.Yul.World.CallerFrameChecks.target
#check Solidity.Yul.World.CallerFrameChecks.locals
#check Solidity.Yul.World.CallerFrameChecks.caller
#check Solidity.Yul.World.CallerFrameChecks.residual
#check Solidity.Yul.World.CallerFrameChecks.encoding
#check Solidity.Yul.World.CallerFrameChecks.log
#check Solidity.Yul.World.CallerFrameChecks.callerTrace
#check Solidity.Yul.World.CallerFrameChecks.observed
#check Solidity.Yul.World.CallerFrameChecks.parent
#check Solidity.Yul.World.CallerFrameChecks.suffix
#check Solidity.Yul.World.CallerFrameChecks.events
#check Solidity.Yul.World.CallerFrameChecks.credited
#check Solidity.Yul.World.CallerFrameChecks.after
#check Solidity.Yul.World.CallerFrameChecks.result
#check Solidity.Yul.World.CallerFrameChecks.nontrivial_entry
#check Solidity.Yul.World.CallerFrameChecks.caller_memOK
#check Solidity.Yul.World.CallerFrameChecks.actual_source_run
#check Solidity.Yul.World.CallerFrameChecks.actual_invoke
#check Solidity.Yul.World.CallerFrameChecks.actual_call
#check Solidity.Yul.World.CallerFrameChecks.actual_completion
#check Solidity.Yul.World.CallerFrameChecks.source_composition
#check Solidity.Yul.World.CallerFrameChecks.caller_frame
#check Solidity.Yul.World.CallerFrameChecks.success_credit
#check Solidity.Yul.World.CallerFrameChecks.revert_credit
#check Solidity.Yul.World.CallerFrameChecks.owner_MemOK
#check Solidity.Yul.World.CallerFrameChecks.output_copy
#check Solidity.Yul.World.CallerFrameChecks.nonempty_function_frame
#check Solidity.Yul.World.CallerFrameChecks.alias_read
#check Solidity.Yul.World.CallerFrameChecks.persistent_word_unchanged
#check Solidity.Yul.World.CallerFrameChecks.account_metadata
#check Solidity.Yul.World.CallerFrameChecks.bad_source_zero
#check Solidity.Yul.World.CallerFrameChecks.exact_buffer_and_tail
#check Solidity.Yul.World.CallerFrameChecks.instancePrefix
#check Solidity.Yul.World.CallerFrameChecks.actual_instance_timeout
#check Solidity.Yul.World.CallerFrameChecks.timeout_pending_full
#check Solidity.Yul.World.CallerFrameChecks.enclosing_revert
#check Solidity.Yul.World.CallerFrameChecks.static_refused
#check Solidity.Yul.World.CallerFrameChecks.precompile_refused
#check Solidity.Yul.World.CallerFrameChecks.receiver_registered
#check Solidity.Yul.World.CallerFrameChecks.unregistered
#check Solidity.Yul.World.CallerFrameChecks.overflow
#check Solidity.Yul.World.CallerFrameChecks.withExecution
#check Solidity.Yul.World.CallerFrameChecks.registration_refusal
#check Solidity.Yul.World.CallerFrameChecks.range_refusal
#check Solidity.Yul.World.CallerFrameChecks.wrong_context_refusal
#check Solidity.Yul.World.CallerFrameChecks.partialSuffix
#check Solidity.Yul.World.CallerFrameChecks.partialState
#check Solidity.Yul.World.CallerFrameChecks.partialResult
#check Solidity.Yul.World.CallerFrameChecks.source_credit_timeout
#check Solidity.Yul.World.CallerFrameChecks.prefix_invoke_actual
#check Solidity.Yul.World.CallerFrameChecks.prefix_call_actual
#check Solidity.Yul.World.CallerFrameChecks.dirty_timeout_full
#check Solidity.Yul.World.CallerFrameChecks.completed_extends_pending
#check Solidity.Yul.World.CallerFrameChecks.copiedState
#check Solidity.Yul.World.CallerFrameChecks.exact_state_copy
#check Solidity.Yul.World.CallerFrameChecks.copied_owner_MemOK
#check Solidity.Yul.World.CallerFrameChecks.copied_aliases
#check Solidity.Yul.World.CreditEnvironment.creditGlob
#check Solidity.Yul.World.CreditEnvironment.codeless_succeeds
#check Solidity.Yul.World.CreditEnvironment.zero_no_code
#check Solidity.Yul.World.CreditEnvironment.precompile_no_code
#check Solidity.Yul.World.CreditEnvironment.invokeAt
#check Solidity.Yul.World.CreditEnvironment.invoke
#check Solidity.Yul.World.CreditEnvironment.prefixInvoke
#check Solidity.Yul.World.CreditEnvironment.callerInvoke
#check Solidity.Yul.World.CreditEnvironment.precompile_refusal
#check Solidity.Yul.World.CreditEnvironment.static_kind_refusal
#check Solidity.Yul.World.FailureFuel.internal_timeout
#check Solidity.Yul.World.FailureFuel.dispatch_timeout
#check Solidity.Yul.World.FailureFuel.enter_timeout
#check Solidity.Yul.World.FailureFuel.invoke_run
#check Solidity.Yul.World.FailureFuel.source_timeout
#check Solidity.Yul.World.FailureFuel.timeout_invoke
#check Solidity.Yul.World.FailureFuel.call_timeout
#check Solidity.Yul.World.FailureFuel.prefixed_timeout
#check Solidity.Yul.World.FailureFuel.pending_controls
#check Solidity.Yul.World.GeneralFailure.selected
#check Solidity.Yul.World.GeneralFailure.source_run
#check Solidity.Yul.World.GeneralFailure.result
#check Solidity.Yul.World.GeneralFailure.invoke_empty
#check Solidity.Yul.World.GeneralFailure.invoke_actual
#check Solidity.Yul.World.GeneralFailure.finish_actual
#check Solidity.Yul.World.GeneralFailure.call_actual
#check Solidity.Yul.World.GeneralFailure.static_internal
#check Solidity.Yul.World.GeneralFailure.static_dispatch
#check Solidity.Yul.World.GeneralFailure.static_enter
#check Solidity.Yul.World.GeneralFailure.static_source
#check Solidity.Yul.World.GeneralFailure.staticInvoke
#check Solidity.Yul.World.GeneralFailure.static_invoke_empty
#check Solidity.Yul.World.GeneralFailure.static_invoke_actual
#check Solidity.Yul.World.GeneralFailure.static_finish
#check Solidity.Yul.World.GeneralFailure.static_call
#check Solidity.Yul.World.GeneralFailure.size_exact
#check Solidity.Yul.World.GeneralFailure.nonempty
#check Solidity.Yul.World.GeneralFailure.payload_window
#check Solidity.Yul.World.GeneralFailure.exact_reraise
#check Solidity.Yul.World.GeneralFailure.prefix_control
#check Solidity.Yul.World.GeneralFailure.static_prefix_control
#check Solidity.Yul.World.GeneralFailure.static_wrong_kind
#check Solidity.Yul.World.GeneralFailure.static_delegate_refused
#check Solidity.Yul.World.GeneralFailure.static_nonstatic_refused
#check Solidity.Yul.World.GeneralFailure.copied_payload
#check Solidity.Yul.World.GeneralFailure.wrong_truncated
#check Solidity.Yul.World.GeneralFailure.static_wrong_sender
#check Solidity.Yul.World.GeneralFailure.static_wrong_value
#check Solidity.Yul.World.GeneralFailure.static_unregistered
#check Solidity.Yul.World.GeneralFailure.source_zero_horizon
#check Solidity.Yul.World.GeneralFailure.invalid_zero_copy
#check Solidity.Yul.World.GeneralFailure.exact_end_window
#check Solidity.Yul.World.InstanceBoundary.dispatch_exact
#check Solidity.Yul.World.InstanceBoundary.instance_exact
#check Solidity.Yul.World.InstanceBoundary.full_carrier
#check Solidity.Yul.World.InstanceBoundary.instance_timeout_exact
#check Solidity.Yul.World.InstanceBoundary.completed
#check Solidity.Yul.World.InstanceBoundary.nonempty_instance
#check Solidity.Yul.World.KnownCall.glob
#check Solidity.Yul.World.KnownCall.entryExecution
#check Solidity.Yul.World.KnownCall.parentFrame
#check Solidity.Yul.World.KnownCall.input
#check Solidity.Yul.World.KnownCall.moved
#check Solidity.Yul.World.KnownCall.after
#check Solidity.Yul.World.KnownCall.transfer_actual
#check Solidity.Yul.World.KnownCall.selected
#check Solidity.Yul.World.KnownCall.source_run
#check Solidity.Yul.World.KnownCall.source_timeout
#check Solidity.Yul.World.KnownCall.entry_exact
#check Solidity.Yul.World.KnownCall.other_account
#check Solidity.Yul.World.KnownCall.transient_unchanged
#check Solidity.Yul.World.KnownCall.enclosing_rollback
#check Solidity.Yul.World.KnownCall.invokeAt
#check Solidity.Yul.World.KnownCall.invoke
#check Solidity.Yul.World.KnownCall.prefixInvoke
#check Solidity.Yul.World.KnownCall.empty_output
#check Solidity.Yul.World.KnownCall.caller
#check Solidity.Yul.World.KnownCall.observed
#check Solidity.Yul.World.KnownCall.parent
#check Solidity.Yul.World.KnownCall.invoke_empty
#check Solidity.Yul.World.KnownCall.invoke_actual
#check Solidity.Yul.World.KnownCall.result
#check Solidity.Yul.World.KnownCall.call_actual
#check Solidity.Yul.World.KnownCall.balances_and_eligibility
#check Solidity.Yul.World.KnownCall.concrete
#check Solidity.Yul.World.KnownCall.whole_frame
#check Solidity.Yul.World.KnownCall.source_insufficient
#check Solidity.Yul.World.KnownCall.source_static_value
#check Solidity.Yul.World.KnownCall.source_depth
#check Solidity.Yul.World.KnownCall.source_zero_horizon
#check Solidity.Yul.World.KnownCall.child_context
#check Solidity.Yul.World.KnownCall.prefix_empty
#check Solidity.Yul.World.KnownCall.prefix_call
#check Solidity.Yul.World.KnownCall.poorExecution
#check Solidity.Yul.World.KnownCall.poorCaller
#check Solidity.Yul.World.KnownCall.poorObserved
#check Solidity.Yul.World.KnownCall.poor_source
#check Solidity.Yul.World.KnownCall.poor_invoke
#check Solidity.Yul.World.KnownCall.poor_call
#check Solidity.Yul.World.KnownCall.unregisteredExecution
#check Solidity.Yul.World.KnownCall.unregistered
#check Solidity.Yul.World.KnownCall.debited
#check Solidity.Yul.World.KnownCall.unregistered_source
#check Solidity.Yul.World.KnownCall.unregistered_refusal
#check Solidity.Yul.World.KnownCall.static_refusal
#check Solidity.Yul.World.KnownCall.wrong_context
#check Solidity.Yul.World.KnownCall.caller_eligible
#check Solidity.Yul.World.KnownCall.output_empty
#check Solidity.Yul.World.KnownCall.invalid_zero_source
#check Solidity.Yul.World.KnownCall.owner_memOK
#check Solidity.Yul.World.KnownCall.source_input_aliases
#check Solidity.Yul.World.KnownCall.full_prefix_control
#check Solidity.Yul.World.KnownCall.dirty_timeout_buffer
#check Solidity.Yul.World.KnownStatic.zeroMoved
#check Solidity.Yul.World.KnownStatic.after
#check Solidity.Yul.World.KnownStatic.source_run
#check Solidity.Yul.World.KnownStatic.invokeAt
#check Solidity.Yul.World.KnownStatic.invoke
#check Solidity.Yul.World.KnownStatic.invoke_empty
#check Solidity.Yul.World.KnownStatic.invoke_actual
#check Solidity.Yul.World.KnownStatic.result
#check Solidity.Yul.World.KnownStatic.call_actual
#check Solidity.Yul.World.KnownStatic.world_unchanged
#check Solidity.Yul.World.KnownStatic.journal_not_unchanged
#check Solidity.Yul.World.KnownStatic.child_context
#check Solidity.Yul.World.KnownStatic.nested_static_source
#check Solidity.Yul.World.KnownStatic.concrete
#check Solidity.Yul.World.KnownStatic.whole_frame
#check Solidity.Yul.World.KnownStatic.wrong_context_refusal
#check Solidity.Yul.World.KnownStatic.nonstatic_frame_refusal
#check Solidity.Yul.World.KnownStatic.unregistered_refusal
#check Solidity.Yul.World.PhysicalCompletion.answerStrategy
#check Solidity.Yul.World.PhysicalCompletion.actual_answer_run
#check Solidity.Yul.World.PhysicalCompletion.environmentAnswer
#check Solidity.Yul.World.PhysicalCompletion.environmentAnswer_actual
#check Solidity.Yul.World.PhysicalCompletion.environmentInvoke
#check Solidity.Yul.World.PhysicalCompletion.environmentInvoke_actual
#check Solidity.Yul.World.PhysicalCompletion.externalAnswerGlob
#check Solidity.Yul.World.PhysicalCompletion.external_zero_no_code
#check Solidity.Yul.World.PhysicalCompletion.external_precompile_no_code
#check Solidity.Yul.World.PhysicalCompletion.external_codeless_succeeds
#check Solidity.Yul.World.PhysicalCompletion.staticEnvironmentInvoke
#check Solidity.Yul.World.PhysicalCompletion.static_precompile_refusal
#check Solidity.Yul.World.PhysicalCompletion.static_external_code_refusal
#check Solidity.Yul.World.PhysicalHeapPort.port
#check Solidity.Yul.World.PhysicalHeapPort.load_view
#check Solidity.Yul.World.PhysicalHeapPort.payload_end
#check Solidity.Yul.World.PhysicalHeapPort.payloadOffset
#check Solidity.Yul.World.PhysicalHeapPort.load_encoded
#check Solidity.Yul.World.PhysicalHeapPort.copyWriteback
#check Solidity.Yul.World.PhysicalHeapPort.copyWriteback_exact
#check Solidity.Yul.World.PhysicalHeapPort.copyWriteback_bounds
#check Solidity.Yul.World.PhysicalHeapPort.copyWriteback_frame
#check Solidity.Yul.World.PhysicalHeapPort.copyStateWriteback
#check Solidity.Yul.World.PhysicalHeapPort.copyStateWriteback_memOK
#check Solidity.Yul.World.PhysicalHeapPort.copyStateWriteback_prefix
#check Solidity.Yul.World.PhysicalHeapPort.copyWriteback_reserved
#check Solidity.Yul.World.PhysicalHeapPort.raw_copy_rule
#check Solidity.Yul.World.PhysicalHeapPort.copyWriteback_other_image
#check Solidity.Yul.World.PhysicalPortChecks.callerState
#check Solidity.Yul.World.PhysicalPortChecks.caller_memOK
#check Solidity.Yul.World.PhysicalPortChecks.returnEntry
#check Solidity.Yul.World.PhysicalPortChecks.caller_nonempty
#check Solidity.Yul.World.PhysicalPortChecks.realized_load
#check Solidity.Yul.World.PhysicalPortChecks.actual_copy
#check Solidity.Yul.World.PhysicalPortChecks.physical_and_heap_frame
#check Solidity.Yul.World.PhysicalPortChecks.copied_alias
#check Solidity.Yul.World.PhysicalPortChecks.exact_end_zero
#check Solidity.Yul.World.PhysicalPortChecks.out_of_bounds_zero
#check Solidity.Yul.World.PhysicalPortChecks.wrong_region_and_stale
#check Solidity.Yul.World.PhysicalPortChecks.stateResult
#check Solidity.Yul.World.PhysicalPortChecks.actual_state_copy
#check Solidity.Yul.World.PhysicalPortChecks.real_memOK
#check Solidity.Yul.World.PhysicalPortChecks.real_prefix
#check Solidity.Yul.World.PhysicalPortChecks.slotEntry
#check Solidity.Yul.World.PhysicalPortChecks.slotResult
#check Solidity.Yul.World.PhysicalPortChecks.slot_raw_and_prefix
#check Solidity.Yul.World.PhysicalPortChecks.caller_journals_retained
#check Solidity.Yul.World.PhysicalPortChecks.coupled_child_rollback
#check Solidity.Yul.World.PhysicalPortChecks.static_coupled
#check Solidity.Yul.World.PhysicalPortChecks.wrong_owner_rejected
#check Solidity.Yul.World.PhysicalPortChecks.reserved_after_copy
#check Solidity.Yul.World.PhysicalPortChecks.actual_copy_rule
#check Solidity.Yul.World.PhysicalPortChecks.thirdRequest
#check Solidity.Yul.World.PhysicalPortChecks.thirdPrepared
#check Solidity.Yul.World.PhysicalPortChecks.third_prepares
#check Solidity.Yul.World.PhysicalPortChecks.thirdPlan
#check Solidity.Yul.World.PhysicalPortChecks.slotSecond
#check Solidity.Yul.World.PhysicalPortChecks.full_outer_rollback
#check Solidity.Yul.World.PhysicalPortChecks.slot_actual_memOK
#check Solidity.Yul.World.PhysicalPortChecks.mismatched_world_rejected
#check Solidity.Yul.World.PhysicalPortChecks.callEntry
#check Solidity.Yul.World.PhysicalPortChecks.callParent
#check Solidity.Yul.World.PhysicalPortChecks.callAnswer
#check Solidity.Yul.World.PhysicalPortChecks.callProducer
#check Solidity.Yul.World.PhysicalPortChecks.physical_delegate_call
#check Solidity.Yul.World.PhysicalPortChecks.actual_source_alias_read
#check Solidity.Yul.World.PhysicalPortChecks.stringEntry
#check Solidity.Yul.World.PhysicalPortChecks.actual_string_copy
#check Solidity.Yul.World.PhysicalPortChecks.transientRequest
#check Solidity.Yul.World.PhysicalPortChecks.transientPrepared
#check Solidity.Yul.World.PhysicalPortChecks.transient_prepares
#check Solidity.Yul.World.PhysicalPortChecks.transientPlan
#check Solidity.Yul.World.PhysicalPortChecks.transientResult
#check Solidity.Yul.World.PhysicalPortChecks.transient_exact
#check Solidity.Yul.World.PhysicalPortChecks.transient_coupled_rollback
#check Solidity.Yul.World.PhysicalPortChecks.delegatedFrame
#check Solidity.Yul.World.PhysicalPortChecks.actual_delegated_slot
#check Solidity.Yul.World.PhysicalPortChecks.nested_static_delegate
#check Solidity.Yul.World.PhysicalPortChecks.delegatedResult
#check Solidity.Yul.World.PhysicalPortChecks.delegated_public_result
#check Solidity.Yul.World.PhysicalPortChecks.delegated_changed_word_and_code_frame
#check Solidity.Yul.World.PhysicalPortChecks.physical_log
#check Solidity.Yul.World.PhysicalPortChecks.physical_log_rule
#check Solidity.Yul.World.PhysicalPortChecks.physical_log_full_trace
#check Solidity.Yul.World.PhysicalPortChecks.other_string_image_preserved
#check Solidity.Yul.World.PhysicalSlotPort.step
#check Solidity.Yul.World.PhysicalSlotPort.frameWrite?
#check Solidity.Yul.World.PhysicalSlotPort.frameWrite_physical
#check Solidity.Yul.World.PhysicalSlotPort.persistent_word
#check Solidity.Yul.World.PhysicalSlotPort.rollback
#check Solidity.Yul.World.PhysicalSlotPort.memOK
#check Solidity.Yul.World.PhysicalSlotPort.static_result
#check Solidity.Yul.World.PhysicalSlotPort.sourceFrame
#check Solidity.Yul.World.PhysicalSlotPort.sourceFrame_owner
#check Solidity.Yul.World.PhysicalSlotPort.two_outer_rollback
#check Solidity.Yul.World.PhysicalSlotPort.transient_word
#check Solidity.Yul.World.ReturningCall.uint
#check Solidity.Yul.World.ReturningCall.answerDecl
#check Solidity.Yul.World.ReturningCall.errorDecl
#check Solidity.Yul.World.ReturningCall.env
#check Solidity.Yul.World.ReturningCall.value
#check Solidity.Yul.World.ReturningCall.body
#check Solidity.Yul.World.ReturningCall.glob
#check Solidity.Yul.World.ReturningCall.input
#check Solidity.Yul.World.ReturningCall.output
#check Solidity.Yul.World.ReturningCall.child
#check Solidity.Yul.World.ReturningCall.input_length
#check Solidity.Yul.World.ReturningCall.input_nonempty
#check Solidity.Yul.World.ReturningCall.exposed
#check Solidity.Yul.World.ReturningCall.resolved
#check Solidity.Yul.World.ReturningCall.signature
#check Solidity.Yul.World.ReturningCall.found
#check Solidity.Yul.World.ReturningCall.picked
#check Solidity.Yul.World.ReturningCall.internal_run
#check Solidity.Yul.World.ReturningCall.dispatch_run
#check Solidity.Yul.World.ReturningCall.enter_run
#check Solidity.Yul.World.ReturningCall.initial
#check Solidity.Yul.World.ReturningCall.entryExecution
#check Solidity.Yul.World.ReturningCall.moved
#check Solidity.Yul.World.ReturningCall.parentFrame
#check Solidity.Yul.World.ReturningCall.after
#check Solidity.Yul.World.ReturningCall.run_pure
#check Solidity.Yul.World.ReturningCall.run_st
#check Solidity.Yul.World.ReturningCall.run_modSt
#check Solidity.Yul.World.ReturningCall.run_mark
#check Solidity.Yul.World.ReturningCall.selected
#check Solidity.Yul.World.ReturningCall.transfer_actual
#check Solidity.Yul.World.ReturningCall.source_run
#check Solidity.Yul.World.ReturningCall.output_exact
#check Solidity.Yul.World.ReturningCall.assertBody
#check Solidity.Yul.World.ReturningCall.failureBody
#check Solidity.Yul.World.ReturningCall.errorData
#check Solidity.Yul.World.ReturningCall.failingGlob
#check Solidity.Yul.World.ReturningCall.failure_resolved
#check Solidity.Yul.World.ReturningCall.failure_picked
#check Solidity.Yul.World.ReturningCall.failure_internal
#check Solidity.Yul.World.ReturningCall.failure_dispatch
#check Solidity.Yul.World.ReturningCall.failure_enter
#check Solidity.Yul.World.ReturningCall.failure_selected
#check Solidity.Yul.World.ReturningCall.failure_source
#check Solidity.Yul.World.ReturningCall.assert_timeout
#check Solidity.Yul.World.ReturningStatic.child
#check Solidity.Yul.World.ReturningStatic.picked
#check Solidity.Yul.World.ReturningStatic.internal_run
#check Solidity.Yul.World.ReturningStatic.dispatch_run
#check Solidity.Yul.World.ReturningStatic.enter_run
#check Solidity.Yul.World.ReturningStatic.zeroMoved
#check Solidity.Yul.World.ReturningStatic.after
#check Solidity.Yul.World.ReturningStatic.transfer_zero
#check Solidity.Yul.World.ReturningStatic.source_run
#check Solidity.Yul.World.ReturningStatic.invokeAt
#check Solidity.Yul.World.ReturningStatic.invoke
#check Solidity.Yul.World.ReturningStatic.invoke_empty
#check Solidity.Yul.World.ReturningStatic.invoke_actual
#check Solidity.Yul.World.ReturningStatic.result
#check Solidity.Yul.World.ReturningStatic.call_actual
#check Solidity.Yul.World.ReturningStatic.world_unchanged
#check Solidity.Yul.World.ReturningStatic.journal_not_unchanged
#check Solidity.Yul.World.ReturningStatic.full_frame
#check Solidity.Yul.World.ReturningStatic.child_context_at
#check Solidity.Yul.World.ReturningStatic.child_context
#check Solidity.Yul.World.ReturningStatic.copiedState
#check Solidity.Yul.World.ReturningStatic.copy_output
#check Solidity.Yul.World.ReturningStatic.copied_full_frame
#check Solidity.Yul.World.ReturningStatic.copied_aliases
#check Solidity.Yul.World.ReturningStatic.wrong_extent
#check Solidity.Yul.World.ReturningStatic.invalid_zero
#check Solidity.Yul.World.ReturningStatic.nonstatic_frame_refusal
#check Solidity.Yul.World.ReturningStatic.owner_memOK
#check Solidity.Yul.World.ReturningStatic.copy_state
#check Solidity.Yul.World.ReturningStatic.copied_memOK
#check Solidity.Yul.World.ReturningStatic.no_stale_buffer
#check Solidity.Yul.World.ReturningStatic.end_zero_copy
#check Solidity.Yul.World.ReturningStatic.wrong_context_refusal
#check Solidity.Yul.World.ReturningStatic.wrong_value_refusal
#check Solidity.Yul.World.ReturningStatic.wrong_kind_refusal
#check Solidity.Yul.World.ReturningStatic.precompile_refusal
#check Solidity.Yul.World.ReturningStatic.unregistered_refusal
#check Solidity.Yul.World.ReturningStatic.static_entry_zero
#check Solidity.Yul.World.ReturningStatic.enclosing_revert
#check Solidity.Yul.World.ReturningCall.internal_timeout
#check Solidity.Yul.World.ReturningCall.dispatch_timeout
#check Solidity.Yul.World.ReturningCall.enter_timeout
#check Solidity.Yul.World.ReturningCall.source_timeout
#check Solidity.Yul.World.ReturningCall.timeout_invoke
#check Solidity.Yul.World.ReturningCall.timeout_call
#check Solidity.Yul.World.ScalarEmitPort.eventDecl
#check Solidity.Yul.World.ScalarEmitPort.env
#check Solidity.Yul.World.ScalarEmitPort.statement
#check Solidity.Yul.World.ScalarEmitPort.frame
#check Solidity.Yul.World.ScalarEmitPort.signature
#check Solidity.Yul.World.ScalarEmitPort.legacy
#check Solidity.Yul.World.ScalarEmitPort.encoding
#check Solidity.Yul.World.ScalarEmitPort.after
#check Solidity.Yul.World.ScalarEmitPort.registered
#check Solidity.Yul.World.ScalarEmitPort.statement_run
#check Solidity.Yul.World.ScalarEmitPort.statement_static
#check Solidity.Yul.World.ScalarEmitPort.source
#check Solidity.Yul.World.ScalarEmitPort.source_run
#check Solidity.Yul.World.ScalarEmitPort.source_static
#check Solidity.Yul.World.ScalarEmitPort.execute
#check Solidity.Yul.World.ScalarEmitPort.execute_run
#check Solidity.Yul.World.ScalarEmitPort.execute_static
#check Solidity.Yul.World.ScalarEmitPort.execute_shared
#check Solidity.Yul.World.ScalarEmitPort.after_memOK
#check Solidity.Yul.World.ScalarEmitPort.rollback_legacy
#check Solidity.Yul.World.ScalarEmitPort.enclosing_revert
#check Solidity.Yul.World.ScalarEmitPort.data_bound
#check Solidity.Yul.World.ScalarEmitPort.memory
#check Solidity.Yul.World.ScalarEmitPort.size
#check Solidity.Yul.World.ScalarEmitPort.raw_loaded
#check Solidity.Yul.World.ScalarEmitPort.raw_agreement
#check Solidity.Yul.World.ScalarEmitPort.source_raw_observations
#check Solidity.Yul.World.ScalarEmitPort.legacy_length
#check Solidity.Yul.World.ScalarEmitPort.legacy_not_data
#check Solidity.Yul.World.ScalarEmitPort.full_signature_topic
#check Solidity.Yul.World.ScalarEmitPort.indexed_topics
#check Solidity.Yul.World.ScalarEmitPort.anonymous_topics
#check Solidity.Yul.World.StateCall.flagDecl
#check Solidity.Yul.World.StateCall.env
#check Solidity.Yul.World.StateCall.flagPath
#check Solidity.Yul.World.StateCall.writeOp
#check Solidity.Yul.World.StateCall.changed
#check Solidity.Yul.World.StateCall.assignment
#check Solidity.Yul.World.StateCall.readReturn
#check Solidity.Yul.World.StateCall.readBody
#check Solidity.Yul.World.StateCall.body
#check Solidity.Yul.World.StateCall.glob
#check Solidity.Yul.World.StateCall.input
#check Solidity.Yul.World.StateCall.errorData
#check Solidity.Yul.World.StateCall.assignment_run
#check Solidity.Yul.World.StateCall.read_after_write
#check Solidity.Yul.World.StateCall.return_after_write
#check Solidity.Yul.World.StateCall.resolved
#check Solidity.Yul.World.StateCall.mods_success
#check Solidity.Yul.World.StateCall.internal_success
#check Solidity.Yul.World.StateCall.internal_revert
#check Solidity.Yul.World.StateCall.read_body_timeout
#check Solidity.Yul.World.StateCall.input_length
#check Solidity.Yul.World.StateCall.input_nonempty
#check Solidity.Yul.World.StateCall.exposed
#check Solidity.Yul.World.StateCall.signature
#check Solidity.Yul.World.StateCall.found
#check Solidity.Yul.World.StateCall.picked
#check Solidity.Yul.World.StateCall.dispatch_success
#check Solidity.Yul.World.StateCall.enter_success
#check Solidity.Yul.World.StateCall.dispatch_revert
#check Solidity.Yul.World.StateCall.enter_revert
#check Solidity.Yul.World.StateCall.transferred
#check Solidity.Yul.World.StateCall.selected
#check Solidity.Yul.World.StateCall.source_success
#check Solidity.Yul.World.StateCall.transfer_length
#check Solidity.Yul.World.StateCall.rollback_write_transfer
#check Solidity.Yul.World.StateCall.source_revert
#check Solidity.Yul.World.PhysicalFrameCalldataChecks.full_carrier_read
#check Solidity.Yul.World.PhysicalFrameCalldataChecks.delegate_frame
#check Solidity.Yul.World.PhysicalFrameCalldataChecks.delegate_read
#check Solidity.Yul.World.PhysicalFrameCalldataChecks.stale_buffer
#print axioms Solidity.Yul.World.Callback.codeless_succeeds
#print axioms Solidity.Yul.World.Callback.precompile_no_code
#print axioms Solidity.Yul.World.Callback.precompile_refusal
#print axioms Solidity.Yul.World.CallbackChecks.actual_callback_dispatch
#print axioms Solidity.Yul.World.CallbackChecks.actual_source_run
#print axioms Solidity.Yul.World.CallbackChecks.invoke_actual
#print axioms Solidity.Yul.World.CallbackChecks.completion_actual
#print axioms Solidity.Yul.World.CallbackChecks.call_actual
#print axioms Solidity.Yul.World.CallbackChecks.frame_and_trace
#print axioms Solidity.Yul.World.CallbackSuccess.modifier_resolves
#print axioms Solidity.Yul.World.CallbackSuccess.modifier_frame
#print axioms Solidity.Yul.World.CallbackSuccess.source_run
#print axioms Solidity.Yul.World.CallbackSuccess.invoke_actual
#print axioms Solidity.Yul.World.CallbackSuccess.completion
#print axioms Solidity.Yul.World.CallbackSuccess.call_actual
#print axioms Solidity.Yul.World.CallbackSuccess.frame
#print axioms Solidity.Yul.World.CallbackSuccess.receiver_balance
#print axioms Solidity.Yul.World.CallbackSuccess.source_timeout
#print axioms Solidity.Yul.World.CallbackSuccess.prefix_invoke
#print axioms Solidity.Yul.World.CallbackSuccess.prefix_call
#print axioms Solidity.Yul.World.CallbackSuccess.dirty_prefix_frame
#print axioms Solidity.Yul.World.CallbackSuccess.output_copy
#print axioms Solidity.Yul.World.CallbackSuccess.nonempty_caller
#print axioms Solidity.Yul.World.CallbackSuccess.static_refusal
#print axioms Solidity.Yul.World.CallbackSuccess.ordered_success_not_timeout
#print axioms Solidity.Yul.World.CallbackSuccess.ordered_success_not_failure
#print axioms Solidity.Yul.World.CallbackSuccess.no_fresh_timeout_buffer
#print axioms Solidity.Yul.World.CallbackSuccess.registration_refusal
#print axioms Solidity.Yul.World.CallbackSuccess.range_refusal
#print axioms Solidity.Yul.World.CallbackSuccess.context_refusal
#print axioms Solidity.Yul.World.CallbackSuccess.precompile_refusal
#print axioms Solidity.Yul.World.CallbackSuccess.missing_modifier
#print axioms Solidity.Yul.World.CallbackSuccess.owner_MemOK
#print axioms Solidity.Yul.World.CallbackSuccess.exact_state_copy
#print axioms Solidity.Yul.World.CallbackSuccess.copied_owner_MemOK
#print axioms Solidity.Yul.World.CallbackSuccess.copied_aliases
#print axioms Solidity.Yul.World.CallerFrame.sourceBoundary_exact
#print axioms Solidity.Yul.World.CallerFrame.liftInvoke_exact
#print axioms Solidity.Yul.World.CallerFrame.liftInvoke_state
#print axioms Solidity.Yul.World.CallerFrame.enterInstance_heap
#print axioms Solidity.Yul.World.CallerFrame.runInstance_frame
#print axioms Solidity.Yul.World.CallerFrameChecks.nontrivial_entry
#print axioms Solidity.Yul.World.CallerFrameChecks.caller_memOK
#print axioms Solidity.Yul.World.CallerFrameChecks.actual_source_run
#print axioms Solidity.Yul.World.CallerFrameChecks.actual_invoke
#print axioms Solidity.Yul.World.CallerFrameChecks.actual_call
#print axioms Solidity.Yul.World.CallerFrameChecks.actual_completion
#print axioms Solidity.Yul.World.CallerFrameChecks.source_composition
#print axioms Solidity.Yul.World.CallerFrameChecks.caller_frame
#print axioms Solidity.Yul.World.CallerFrameChecks.success_credit
#print axioms Solidity.Yul.World.CallerFrameChecks.revert_credit
#print axioms Solidity.Yul.World.CallerFrameChecks.owner_MemOK
#print axioms Solidity.Yul.World.CallerFrameChecks.output_copy
#print axioms Solidity.Yul.World.CallerFrameChecks.nonempty_function_frame
#print axioms Solidity.Yul.World.CallerFrameChecks.alias_read
#print axioms Solidity.Yul.World.CallerFrameChecks.persistent_word_unchanged
#print axioms Solidity.Yul.World.CallerFrameChecks.account_metadata
#print axioms Solidity.Yul.World.CallerFrameChecks.bad_source_zero
#print axioms Solidity.Yul.World.CallerFrameChecks.exact_buffer_and_tail
#print axioms Solidity.Yul.World.CallerFrameChecks.actual_instance_timeout
#print axioms Solidity.Yul.World.CallerFrameChecks.timeout_pending_full
#print axioms Solidity.Yul.World.CallerFrameChecks.enclosing_revert
#print axioms Solidity.Yul.World.CallerFrameChecks.static_refused
#print axioms Solidity.Yul.World.CallerFrameChecks.precompile_refused
#print axioms Solidity.Yul.World.CallerFrameChecks.receiver_registered
#print axioms Solidity.Yul.World.CallerFrameChecks.registration_refusal
#print axioms Solidity.Yul.World.CallerFrameChecks.range_refusal
#print axioms Solidity.Yul.World.CallerFrameChecks.wrong_context_refusal
#print axioms Solidity.Yul.World.CallerFrameChecks.source_credit_timeout
#print axioms Solidity.Yul.World.CallerFrameChecks.prefix_invoke_actual
#print axioms Solidity.Yul.World.CallerFrameChecks.prefix_call_actual
#print axioms Solidity.Yul.World.CallerFrameChecks.dirty_timeout_full
#print axioms Solidity.Yul.World.CallerFrameChecks.completed_extends_pending
#print axioms Solidity.Yul.World.CallerFrameChecks.exact_state_copy
#print axioms Solidity.Yul.World.CallerFrameChecks.copied_owner_MemOK
#print axioms Solidity.Yul.World.CallerFrameChecks.copied_aliases
#print axioms Solidity.Yul.World.CreditEnvironment.codeless_succeeds
#print axioms Solidity.Yul.World.CreditEnvironment.zero_no_code
#print axioms Solidity.Yul.World.CreditEnvironment.precompile_no_code
#print axioms Solidity.Yul.World.CreditEnvironment.precompile_refusal
#print axioms Solidity.Yul.World.CreditEnvironment.static_kind_refusal
#print axioms Solidity.Yul.World.FailureFuel.internal_timeout
#print axioms Solidity.Yul.World.FailureFuel.dispatch_timeout
#print axioms Solidity.Yul.World.FailureFuel.enter_timeout
#print axioms Solidity.Yul.World.FailureFuel.invoke_run
#print axioms Solidity.Yul.World.FailureFuel.source_timeout
#print axioms Solidity.Yul.World.FailureFuel.timeout_invoke
#print axioms Solidity.Yul.World.FailureFuel.call_timeout
#print axioms Solidity.Yul.World.FailureFuel.prefixed_timeout
#print axioms Solidity.Yul.World.FailureFuel.pending_controls
#print axioms Solidity.Yul.World.GeneralFailure.selected
#print axioms Solidity.Yul.World.GeneralFailure.source_run
#print axioms Solidity.Yul.World.GeneralFailure.invoke_empty
#print axioms Solidity.Yul.World.GeneralFailure.invoke_actual
#print axioms Solidity.Yul.World.GeneralFailure.finish_actual
#print axioms Solidity.Yul.World.GeneralFailure.call_actual
#print axioms Solidity.Yul.World.GeneralFailure.static_internal
#print axioms Solidity.Yul.World.GeneralFailure.static_dispatch
#print axioms Solidity.Yul.World.GeneralFailure.static_enter
#print axioms Solidity.Yul.World.GeneralFailure.static_source
#print axioms Solidity.Yul.World.GeneralFailure.static_invoke_empty
#print axioms Solidity.Yul.World.GeneralFailure.static_invoke_actual
#print axioms Solidity.Yul.World.GeneralFailure.static_finish
#print axioms Solidity.Yul.World.GeneralFailure.static_call
#print axioms Solidity.Yul.World.GeneralFailure.size_exact
#print axioms Solidity.Yul.World.GeneralFailure.nonempty
#print axioms Solidity.Yul.World.GeneralFailure.payload_window
#print axioms Solidity.Yul.World.GeneralFailure.exact_reraise
#print axioms Solidity.Yul.World.GeneralFailure.prefix_control
#print axioms Solidity.Yul.World.GeneralFailure.static_prefix_control
#print axioms Solidity.Yul.World.GeneralFailure.static_wrong_kind
#print axioms Solidity.Yul.World.GeneralFailure.static_delegate_refused
#print axioms Solidity.Yul.World.GeneralFailure.static_nonstatic_refused
#print axioms Solidity.Yul.World.GeneralFailure.copied_payload
#print axioms Solidity.Yul.World.GeneralFailure.wrong_truncated
#print axioms Solidity.Yul.World.GeneralFailure.static_wrong_sender
#print axioms Solidity.Yul.World.GeneralFailure.static_wrong_value
#print axioms Solidity.Yul.World.GeneralFailure.static_unregistered
#print axioms Solidity.Yul.World.GeneralFailure.source_zero_horizon
#print axioms Solidity.Yul.World.GeneralFailure.invalid_zero_copy
#print axioms Solidity.Yul.World.GeneralFailure.exact_end_window
#print axioms Solidity.Yul.World.InstanceBoundary.dispatch_exact
#print axioms Solidity.Yul.World.InstanceBoundary.instance_exact
#print axioms Solidity.Yul.World.InstanceBoundary.full_carrier
#print axioms Solidity.Yul.World.InstanceBoundary.instance_timeout_exact
#print axioms Solidity.Yul.World.InstanceBoundary.completed
#print axioms Solidity.Yul.World.InstanceBoundary.nonempty_instance
#print axioms Solidity.Yul.World.KnownCall.transfer_actual
#print axioms Solidity.Yul.World.KnownCall.selected
#print axioms Solidity.Yul.World.KnownCall.source_run
#print axioms Solidity.Yul.World.KnownCall.source_timeout
#print axioms Solidity.Yul.World.KnownCall.entry_exact
#print axioms Solidity.Yul.World.KnownCall.other_account
#print axioms Solidity.Yul.World.KnownCall.transient_unchanged
#print axioms Solidity.Yul.World.KnownCall.enclosing_rollback
#print axioms Solidity.Yul.World.KnownCall.empty_output
#print axioms Solidity.Yul.World.KnownCall.invoke_empty
#print axioms Solidity.Yul.World.KnownCall.invoke_actual
#print axioms Solidity.Yul.World.KnownCall.call_actual
#print axioms Solidity.Yul.World.KnownCall.balances_and_eligibility
#print axioms Solidity.Yul.World.KnownCall.concrete
#print axioms Solidity.Yul.World.KnownCall.whole_frame
#print axioms Solidity.Yul.World.KnownCall.source_insufficient
#print axioms Solidity.Yul.World.KnownCall.source_static_value
#print axioms Solidity.Yul.World.KnownCall.source_depth
#print axioms Solidity.Yul.World.KnownCall.source_zero_horizon
#print axioms Solidity.Yul.World.KnownCall.child_context
#print axioms Solidity.Yul.World.KnownCall.prefix_empty
#print axioms Solidity.Yul.World.KnownCall.prefix_call
#print axioms Solidity.Yul.World.KnownCall.poor_source
#print axioms Solidity.Yul.World.KnownCall.poor_invoke
#print axioms Solidity.Yul.World.KnownCall.poor_call
#print axioms Solidity.Yul.World.KnownCall.unregistered_source
#print axioms Solidity.Yul.World.KnownCall.unregistered_refusal
#print axioms Solidity.Yul.World.KnownCall.static_refusal
#print axioms Solidity.Yul.World.KnownCall.wrong_context
#print axioms Solidity.Yul.World.KnownCall.caller_eligible
#print axioms Solidity.Yul.World.KnownCall.output_empty
#print axioms Solidity.Yul.World.KnownCall.invalid_zero_source
#print axioms Solidity.Yul.World.KnownCall.owner_memOK
#print axioms Solidity.Yul.World.KnownCall.source_input_aliases
#print axioms Solidity.Yul.World.KnownCall.full_prefix_control
#print axioms Solidity.Yul.World.KnownCall.dirty_timeout_buffer
#print axioms Solidity.Yul.World.KnownStatic.source_run
#print axioms Solidity.Yul.World.KnownStatic.invoke_empty
#print axioms Solidity.Yul.World.KnownStatic.invoke_actual
#print axioms Solidity.Yul.World.KnownStatic.call_actual
#print axioms Solidity.Yul.World.KnownStatic.world_unchanged
#print axioms Solidity.Yul.World.KnownStatic.journal_not_unchanged
#print axioms Solidity.Yul.World.KnownStatic.child_context
#print axioms Solidity.Yul.World.KnownStatic.nested_static_source
#print axioms Solidity.Yul.World.KnownStatic.concrete
#print axioms Solidity.Yul.World.KnownStatic.whole_frame
#print axioms Solidity.Yul.World.KnownStatic.wrong_context_refusal
#print axioms Solidity.Yul.World.KnownStatic.nonstatic_frame_refusal
#print axioms Solidity.Yul.World.KnownStatic.unregistered_refusal
#print axioms Solidity.Yul.World.PhysicalCompletion.actual_answer_run
#print axioms Solidity.Yul.World.PhysicalCompletion.environmentAnswer_actual
#print axioms Solidity.Yul.World.PhysicalCompletion.environmentInvoke_actual
#print axioms Solidity.Yul.World.PhysicalCompletion.external_zero_no_code
#print axioms Solidity.Yul.World.PhysicalCompletion.external_precompile_no_code
#print axioms Solidity.Yul.World.PhysicalCompletion.external_codeless_succeeds
#print axioms Solidity.Yul.World.PhysicalCompletion.static_precompile_refusal
#print axioms Solidity.Yul.World.PhysicalCompletion.static_external_code_refusal
#print axioms Solidity.Yul.World.PhysicalHeapPort.load_view
#print axioms Solidity.Yul.World.PhysicalHeapPort.payload_end
#print axioms Solidity.Yul.World.PhysicalHeapPort.load_encoded
#print axioms Solidity.Yul.World.PhysicalHeapPort.copyWriteback_exact
#print axioms Solidity.Yul.World.PhysicalHeapPort.copyWriteback_bounds
#print axioms Solidity.Yul.World.PhysicalHeapPort.copyWriteback_frame
#print axioms Solidity.Yul.World.PhysicalHeapPort.copyStateWriteback_memOK
#print axioms Solidity.Yul.World.PhysicalHeapPort.copyStateWriteback_prefix
#print axioms Solidity.Yul.World.PhysicalHeapPort.copyWriteback_reserved
#print axioms Solidity.Yul.World.PhysicalHeapPort.raw_copy_rule
#print axioms Solidity.Yul.World.PhysicalHeapPort.copyWriteback_other_image
#print axioms Solidity.Yul.World.PhysicalPortChecks.caller_memOK
#print axioms Solidity.Yul.World.PhysicalPortChecks.caller_nonempty
#print axioms Solidity.Yul.World.PhysicalPortChecks.realized_load
#print axioms Solidity.Yul.World.PhysicalPortChecks.actual_copy
#print axioms Solidity.Yul.World.PhysicalPortChecks.physical_and_heap_frame
#print axioms Solidity.Yul.World.PhysicalPortChecks.copied_alias
#print axioms Solidity.Yul.World.PhysicalPortChecks.exact_end_zero
#print axioms Solidity.Yul.World.PhysicalPortChecks.out_of_bounds_zero
#print axioms Solidity.Yul.World.PhysicalPortChecks.wrong_region_and_stale
#print axioms Solidity.Yul.World.PhysicalPortChecks.actual_state_copy
#print axioms Solidity.Yul.World.PhysicalPortChecks.real_memOK
#print axioms Solidity.Yul.World.PhysicalPortChecks.real_prefix
#print axioms Solidity.Yul.World.PhysicalPortChecks.slot_raw_and_prefix
#print axioms Solidity.Yul.World.PhysicalPortChecks.caller_journals_retained
#print axioms Solidity.Yul.World.PhysicalPortChecks.coupled_child_rollback
#print axioms Solidity.Yul.World.PhysicalPortChecks.static_coupled
#print axioms Solidity.Yul.World.PhysicalPortChecks.wrong_owner_rejected
#print axioms Solidity.Yul.World.PhysicalPortChecks.reserved_after_copy
#print axioms Solidity.Yul.World.PhysicalPortChecks.actual_copy_rule
#print axioms Solidity.Yul.World.PhysicalPortChecks.third_prepares
#print axioms Solidity.Yul.World.PhysicalPortChecks.full_outer_rollback
#print axioms Solidity.Yul.World.PhysicalPortChecks.slot_actual_memOK
#print axioms Solidity.Yul.World.PhysicalPortChecks.mismatched_world_rejected
#print axioms Solidity.Yul.World.PhysicalPortChecks.physical_delegate_call
#print axioms Solidity.Yul.World.PhysicalPortChecks.actual_source_alias_read
#print axioms Solidity.Yul.World.PhysicalPortChecks.actual_string_copy
#print axioms Solidity.Yul.World.PhysicalPortChecks.transient_prepares
#print axioms Solidity.Yul.World.PhysicalPortChecks.transient_exact
#print axioms Solidity.Yul.World.PhysicalPortChecks.transient_coupled_rollback
#print axioms Solidity.Yul.World.PhysicalPortChecks.actual_delegated_slot
#print axioms Solidity.Yul.World.PhysicalPortChecks.nested_static_delegate
#print axioms Solidity.Yul.World.PhysicalPortChecks.delegated_public_result
#print axioms Solidity.Yul.World.PhysicalPortChecks.delegated_changed_word_and_code_frame
#print axioms Solidity.Yul.World.PhysicalPortChecks.physical_log
#print axioms Solidity.Yul.World.PhysicalPortChecks.physical_log_rule
#print axioms Solidity.Yul.World.PhysicalPortChecks.physical_log_full_trace
#print axioms Solidity.Yul.World.PhysicalPortChecks.other_string_image_preserved
#print axioms Solidity.Yul.World.PhysicalSlotPort.frameWrite_physical
#print axioms Solidity.Yul.World.PhysicalSlotPort.persistent_word
#print axioms Solidity.Yul.World.PhysicalSlotPort.rollback
#print axioms Solidity.Yul.World.PhysicalSlotPort.memOK
#print axioms Solidity.Yul.World.PhysicalSlotPort.static_result
#print axioms Solidity.Yul.World.PhysicalSlotPort.sourceFrame_owner
#print axioms Solidity.Yul.World.PhysicalSlotPort.two_outer_rollback
#print axioms Solidity.Yul.World.PhysicalSlotPort.transient_word
#print axioms Solidity.Yul.World.ReturningCall.input_length
#print axioms Solidity.Yul.World.ReturningCall.input_nonempty
#print axioms Solidity.Yul.World.ReturningCall.exposed
#print axioms Solidity.Yul.World.ReturningCall.resolved
#print axioms Solidity.Yul.World.ReturningCall.signature
#print axioms Solidity.Yul.World.ReturningCall.found
#print axioms Solidity.Yul.World.ReturningCall.picked
#print axioms Solidity.Yul.World.ReturningCall.internal_run
#print axioms Solidity.Yul.World.ReturningCall.dispatch_run
#print axioms Solidity.Yul.World.ReturningCall.enter_run
#print axioms Solidity.Yul.World.ReturningCall.run_pure
#print axioms Solidity.Yul.World.ReturningCall.run_st
#print axioms Solidity.Yul.World.ReturningCall.run_modSt
#print axioms Solidity.Yul.World.ReturningCall.run_mark
#print axioms Solidity.Yul.World.ReturningCall.selected
#print axioms Solidity.Yul.World.ReturningCall.transfer_actual
#print axioms Solidity.Yul.World.ReturningCall.source_run
#print axioms Solidity.Yul.World.ReturningCall.output_exact
#print axioms Solidity.Yul.World.ReturningCall.failure_resolved
#print axioms Solidity.Yul.World.ReturningCall.failure_picked
#print axioms Solidity.Yul.World.ReturningCall.failure_internal
#print axioms Solidity.Yul.World.ReturningCall.failure_dispatch
#print axioms Solidity.Yul.World.ReturningCall.failure_enter
#print axioms Solidity.Yul.World.ReturningCall.failure_selected
#print axioms Solidity.Yul.World.ReturningCall.failure_source
#print axioms Solidity.Yul.World.ReturningCall.assert_timeout
#print axioms Solidity.Yul.World.ReturningStatic.picked
#print axioms Solidity.Yul.World.ReturningStatic.internal_run
#print axioms Solidity.Yul.World.ReturningStatic.dispatch_run
#print axioms Solidity.Yul.World.ReturningStatic.enter_run
#print axioms Solidity.Yul.World.ReturningStatic.transfer_zero
#print axioms Solidity.Yul.World.ReturningStatic.source_run
#print axioms Solidity.Yul.World.ReturningStatic.invoke_empty
#print axioms Solidity.Yul.World.ReturningStatic.invoke_actual
#print axioms Solidity.Yul.World.ReturningStatic.call_actual
#print axioms Solidity.Yul.World.ReturningStatic.world_unchanged
#print axioms Solidity.Yul.World.ReturningStatic.journal_not_unchanged
#print axioms Solidity.Yul.World.ReturningStatic.full_frame
#print axioms Solidity.Yul.World.ReturningStatic.child_context_at
#print axioms Solidity.Yul.World.ReturningStatic.child_context
#print axioms Solidity.Yul.World.ReturningStatic.copy_output
#print axioms Solidity.Yul.World.ReturningStatic.copied_full_frame
#print axioms Solidity.Yul.World.ReturningStatic.copied_aliases
#print axioms Solidity.Yul.World.ReturningStatic.wrong_extent
#print axioms Solidity.Yul.World.ReturningStatic.invalid_zero
#print axioms Solidity.Yul.World.ReturningStatic.nonstatic_frame_refusal
#print axioms Solidity.Yul.World.ReturningStatic.owner_memOK
#print axioms Solidity.Yul.World.ReturningStatic.copy_state
#print axioms Solidity.Yul.World.ReturningStatic.copied_memOK
#print axioms Solidity.Yul.World.ReturningStatic.no_stale_buffer
#print axioms Solidity.Yul.World.ReturningStatic.end_zero_copy
#print axioms Solidity.Yul.World.ReturningStatic.wrong_context_refusal
#print axioms Solidity.Yul.World.ReturningStatic.wrong_value_refusal
#print axioms Solidity.Yul.World.ReturningStatic.wrong_kind_refusal
#print axioms Solidity.Yul.World.ReturningStatic.precompile_refusal
#print axioms Solidity.Yul.World.ReturningStatic.unregistered_refusal
#print axioms Solidity.Yul.World.ReturningStatic.static_entry_zero
#print axioms Solidity.Yul.World.ReturningStatic.enclosing_revert
#print axioms Solidity.Yul.World.ReturningCall.internal_timeout
#print axioms Solidity.Yul.World.ReturningCall.dispatch_timeout
#print axioms Solidity.Yul.World.ReturningCall.enter_timeout
#print axioms Solidity.Yul.World.ReturningCall.source_timeout
#print axioms Solidity.Yul.World.ReturningCall.timeout_invoke
#print axioms Solidity.Yul.World.ReturningCall.timeout_call
#print axioms Solidity.Yul.World.ScalarEmitPort.registered
#print axioms Solidity.Yul.World.ScalarEmitPort.statement_run
#print axioms Solidity.Yul.World.ScalarEmitPort.statement_static
#print axioms Solidity.Yul.World.ScalarEmitPort.source_run
#print axioms Solidity.Yul.World.ScalarEmitPort.source_static
#print axioms Solidity.Yul.World.ScalarEmitPort.execute_run
#print axioms Solidity.Yul.World.ScalarEmitPort.execute_static
#print axioms Solidity.Yul.World.ScalarEmitPort.execute_shared
#print axioms Solidity.Yul.World.ScalarEmitPort.after_memOK
#print axioms Solidity.Yul.World.ScalarEmitPort.rollback_legacy
#print axioms Solidity.Yul.World.ScalarEmitPort.enclosing_revert
#print axioms Solidity.Yul.World.ScalarEmitPort.data_bound
#print axioms Solidity.Yul.World.ScalarEmitPort.raw_loaded
#print axioms Solidity.Yul.World.ScalarEmitPort.raw_agreement
#print axioms Solidity.Yul.World.ScalarEmitPort.source_raw_observations
#print axioms Solidity.Yul.World.ScalarEmitPort.legacy_length
#print axioms Solidity.Yul.World.ScalarEmitPort.legacy_not_data
#print axioms Solidity.Yul.World.ScalarEmitPort.full_signature_topic
#print axioms Solidity.Yul.World.ScalarEmitPort.indexed_topics
#print axioms Solidity.Yul.World.ScalarEmitPort.anonymous_topics
#print axioms Solidity.Yul.World.StateCall.assignment_run
#print axioms Solidity.Yul.World.StateCall.read_after_write
#print axioms Solidity.Yul.World.StateCall.return_after_write
#print axioms Solidity.Yul.World.StateCall.resolved
#print axioms Solidity.Yul.World.StateCall.mods_success
#print axioms Solidity.Yul.World.StateCall.internal_success
#print axioms Solidity.Yul.World.StateCall.internal_revert
#print axioms Solidity.Yul.World.StateCall.read_body_timeout
#print axioms Solidity.Yul.World.StateCall.input_length
#print axioms Solidity.Yul.World.StateCall.input_nonempty
#print axioms Solidity.Yul.World.StateCall.exposed
#print axioms Solidity.Yul.World.StateCall.signature
#print axioms Solidity.Yul.World.StateCall.found
#print axioms Solidity.Yul.World.StateCall.picked
#print axioms Solidity.Yul.World.StateCall.dispatch_success
#print axioms Solidity.Yul.World.StateCall.enter_success
#print axioms Solidity.Yul.World.StateCall.dispatch_revert
#print axioms Solidity.Yul.World.StateCall.enter_revert
#print axioms Solidity.Yul.World.StateCall.selected
#print axioms Solidity.Yul.World.StateCall.source_success
#print axioms Solidity.Yul.World.StateCall.transfer_length
#print axioms Solidity.Yul.World.StateCall.rollback_write_transfer
#print axioms Solidity.Yul.World.StateCall.source_revert
#print axioms Solidity.Yul.World.PhysicalFrameCalldataChecks.full_carrier_read
#print axioms Solidity.Yul.World.PhysicalFrameCalldataChecks.delegate_frame
#print axioms Solidity.Yul.World.PhysicalFrameCalldataChecks.delegate_read
#print axioms Solidity.Yul.World.PhysicalFrameCalldataChecks.stale_buffer
