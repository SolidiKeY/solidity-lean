import Solidity.Yul.World.DelegateBody
import Solidity.Yul.World.StateCallRules
import Solidity.Yul.World.StateCallExtra
import Solidity.Yul.World.StateCallChecks
import Solidity.Yul.World.StateCallStatic
import Solidity.Yul.World.StateCallPort
import Solidity.Yul.World.StateCallHalts
import Solidity.Yul.World.DelegateChecks
import Solidity.Yul.World.DelegateCompletion
import Solidity.Yul.World.DelegatePort
import Solidity.Yul.World.DelegateStatic
import Solidity.Yul.World.DelegatePhysical
import Solidity.Yul.World.DelegateEntry
import Solidity.Yul.World.DelegateExtra
import Solidity.Yul.World.DelegateRules
import Solidity.Yul.World.DelegatePending
import Solidity.Yul.World.DelegateOutput
import Solidity.Yul.World.HeapOutputTransport
import Solidity.Yul.World.DelegateOutputChecks
import Solidity.Yul.World.DelegateOutputFailure
import Solidity.Yul.World.DelegateOutputPort
import Solidity.Yul.World.DelegateOutputRules
import Solidity.Yul.World.DelegateRevertBoundary
import Solidity.Yul.World.DelegateRevertControls
import Solidity.Yul.World.DelegateRevertHeap
import Solidity.Yul.World.DelegateRevertPort
import Solidity.Yul.World.DelegateRevertOutput
import Solidity.Yul.World.DelegateRevertWitness
import Solidity.Yul.World.DelegateSuccessBoundary
import Solidity.Yul.World.DelegateSuccessPreparation
import Solidity.Yul.World.DelegateSuccessFraming
import Solidity.Yul.World.DelegateSuccessWitness
import Solidity.Yul.World.DelegateSuccessOutput
import Solidity.Yul.World.DelegateSuccessPort
import Solidity.Yul.World.DelegateSuccessSlot

#check Solidity.Yul.World.DelegateBody.frame
#check Solidity.Yul.World.DelegateBody.internal_success
#check Solidity.Yul.World.DelegateBody.internal_revert
#check Solidity.Yul.World.DelegateBody.picked
#check Solidity.Yul.World.DelegateBody.dispatch_success
#check Solidity.Yul.World.DelegateBody.enter_success
#check Solidity.Yul.World.DelegateBody.dispatch_revert
#check Solidity.Yul.World.DelegateBody.enter_revert
#check Solidity.Yul.World.DelegateBody.internal_timeout
#check Solidity.Yul.World.DelegateBody.dispatch_timeout
#check Solidity.Yul.World.DelegateBody.enter_timeout
#check Solidity.Yul.World.DelegateBody.read_body_timeout
#check Solidity.Yul.World.StateCallRules.Configuration
#check Solidity.Yul.World.StateCallRules.Step
#check Solidity.Yul.World.StateCallRules.success_sound
#check Solidity.Yul.World.StateCallRules.revert_sound
#check Solidity.Yul.World.StateCallRules.inhabited_success
#check Solidity.Yul.World.StateCallRules.inhabited_revert
#check Solidity.Yul.World.StateCallExtra.lowInvoke
#check Solidity.Yul.World.StateCallExtra.low_empty
#check Solidity.Yul.World.StateCallExtra.low_actual
#check Solidity.Yul.World.StateCallExtra.low_call
#check Solidity.Yul.World.StateCallExtra.low_witness
#check Solidity.Yul.World.StateCallExtra.error_length
#check Solidity.Yul.World.StateCallExtra.error_window
#check Solidity.Yul.World.StateCallExtra.source_prefix_journals
#check Solidity.Yul.World.StateCallExtra.success_full_word
#check Solidity.Yul.World.StateCallExtra.trueEntry
#check Solidity.Yul.World.StateCallExtra.trueMoved
#check Solidity.Yul.World.StateCallExtra.trueCaller
#check Solidity.Yul.World.StateCallExtra.trueObserved
#check Solidity.Yul.World.StateCallExtra.dirty_true_input
#check Solidity.Yul.World.StateCallExtra.dirty_true_success
#check Solidity.Yul.World.StateCallExtra.dirty_true_output
#check Solidity.Yul.World.StateCallExtra.pending_controls
#check Solidity.Yul.World.StateCallExtra.success_size
#check Solidity.Yul.World.StateCallExtra.revert_size
#check Solidity.Yul.World.StateCallChecks.initial
#check Solidity.Yul.World.StateCallChecks.entry
#check Solidity.Yul.World.StateCallChecks.moved
#check Solidity.Yul.World.StateCallChecks.zeroMoved
#check Solidity.Yul.World.StateCallChecks.heap
#check Solidity.Yul.World.StateCallChecks.placement
#check Solidity.Yul.World.StateCallChecks.byteEntry
#check Solidity.Yul.World.StateCallChecks.memory
#check Solidity.Yul.World.StateCallChecks.locals
#check Solidity.Yul.World.StateCallChecks.caller
#check Solidity.Yul.World.StateCallChecks.observed
#check Solidity.Yul.World.StateCallChecks.residual
#check Solidity.Yul.World.StateCallChecks.loaded
#check Solidity.Yul.World.StateCallChecks.success
#check Solidity.Yul.World.StateCallChecks.reverted
#check Solidity.Yul.World.StateCallChecks.outer_after_success
#check Solidity.Yul.World.StateCallChecks.static_reverted
#check Solidity.Yul.World.StateCallChecks.written_value
#check Solidity.Yul.World.StateCallChecks.caller_storage
#check Solidity.Yul.World.StateCallChecks.full_prefix
#check Solidity.Yul.World.StateCallChecks.initial_full_word
#check Solidity.Yul.World.StateCallChecks.initial_bool
#check Solidity.Yul.World.StateCallChecks.padding_unchanged
#check Solidity.Yul.World.StateCallChecks.aliases
#check Solidity.Yul.World.StateCallChecks.wrongResidual
#check Solidity.Yul.World.StateCallChecks.padding_refused
#check Solidity.Yul.World.StateCallChecks.wrong_padding_refused
#check Solidity.Yul.World.StateCallChecks.wrong_owner_refused
#check Solidity.Yul.World.StateCallChecks.wrongCode
#check Solidity.Yul.World.StateCallChecks.wrong_code_refused
#check Solidity.Yul.World.StateCallChecks.caller_memOK
#check Solidity.Yul.World.StateCall.static_internal
#check Solidity.Yul.World.StateCall.static_dispatch
#check Solidity.Yul.World.StateCall.static_enter
#check Solidity.Yul.World.StateCall.static_source
#check Solidity.Yul.World.StateCall.static_physical
#check Solidity.Yul.World.StateCallPort.staticResult
#check Solidity.Yul.World.StateCallPort.staticPack
#check Solidity.Yul.World.StateCallPort.staticInvoke
#check Solidity.Yul.World.StateCallPort.static_invoke_empty
#check Solidity.Yul.World.StateCallPort.static_invoke_actual
#check Solidity.Yul.World.StateCallPort.static_finish
#check Solidity.Yul.World.StateCallPort.static_call
#check Solidity.Yul.World.StateCallPort.parent
#check Solidity.Yul.World.StateCallPort.invoke
#check Solidity.Yul.World.StateCallPort.sourceCarrier
#check Solidity.Yul.World.StateCallPort.invoke_success_empty
#check Solidity.Yul.World.StateCallPort.invoke_revert_empty
#check Solidity.Yul.World.StateCallPort.successResult
#check Solidity.Yul.World.StateCallPort.revertResult
#check Solidity.Yul.World.StateCallPort.invoke_success_actual
#check Solidity.Yul.World.StateCallPort.invoke_revert_actual
#check Solidity.Yul.World.StateCallPort.call_success
#check Solidity.Yul.World.StateCallPort.call_revert
#check Solidity.Yul.World.StateCallPort.outer_revert
#check Solidity.Yul.World.StateCall.internal_timeout
#check Solidity.Yul.World.StateCall.dispatch_timeout
#check Solidity.Yul.World.StateCall.enter_timeout
#check Solidity.Yul.World.StateCall.source_timeout
#check Solidity.Yul.World.StateCall.empty_dispatch
#check Solidity.Yul.World.DelegateChecks.sender
#check Solidity.Yul.World.DelegateChecks.target
#check Solidity.Yul.World.DelegateChecks.value
#check Solidity.Yul.World.DelegateChecks.distinct
#check Solidity.Yul.World.DelegateChecks.success
#check Solidity.Yul.World.DelegateChecks.reverted_call
#check Solidity.Yul.World.DelegateChecks.static_refusal
#check Solidity.Yul.World.DelegateChecks.enclosing
#check Solidity.Yul.World.DelegateChecks.full_state
#check Solidity.Yul.World.DelegateChecks.inherited_context
#check Solidity.Yul.World.DelegateChecks.input_view
#check Solidity.Yul.World.DelegateChecks.output_view
#check Solidity.Yul.World.DelegateChecks.precompile_control
#check Solidity.Yul.World.DelegatePort.successful
#check Solidity.Yul.World.DelegatePort.reverted
#check Solidity.Yul.World.DelegatePort.success_actual
#check Solidity.Yul.World.DelegatePort.revert_actual
#check Solidity.Yul.World.DelegatePort.call_success
#check Solidity.Yul.World.DelegatePort.call_revert
#check Solidity.Yul.World.DelegatePort.enclosing_revert
#check Solidity.Yul.World.DelegatePort.static_actual
#check Solidity.Yul.World.DelegatePort.call_static
#check Solidity.Yul.World.DelegatePort.parent
#check Solidity.Yul.World.DelegatePort.carrier
#check Solidity.Yul.World.DelegatePort.invoke
#check Solidity.Yul.World.DelegatePort.success_empty
#check Solidity.Yul.World.DelegatePort.revert_empty
#check Solidity.Yul.World.DelegatePort.static_empty
#check Solidity.Yul.World.DelegatePort.precompile_refused
#check Solidity.Yul.World.DelegatePort.depth_refused
#check Solidity.Yul.World.DelegatePort.zero_refused
#check Solidity.Yul.World.DelegatePort.owner_refused
#check Solidity.Yul.World.DelegatePort.payload_refused
#check Solidity.Yul.World.DelegatePort.padding_refused
#check Solidity.Yul.World.DelegateStatic.staticFrame
#check Solidity.Yul.World.DelegateStatic.static_internal
#check Solidity.Yul.World.DelegateStatic.static_dispatch
#check Solidity.Yul.World.DelegateStatic.static_enter
#check Solidity.Yul.World.DelegateStatic.execute
#check Solidity.Yul.World.DelegateStatic.execute_revert
#check Solidity.Yul.World.DelegatePhysical.account
#check Solidity.Yul.World.DelegatePhysical.request
#check Solidity.Yul.World.DelegatePhysical.before
#check Solidity.Yul.World.DelegatePhysical.prepared
#check Solidity.Yul.World.DelegatePhysical.ready
#check Solidity.Yul.World.DelegatePhysical.plan
#check Solidity.Yul.World.DelegatePhysical.source_op
#check Solidity.Yul.World.DelegatePhysical.complement
#check Solidity.Yul.World.DelegatePhysical.step_exact
#check Solidity.Yul.World.DelegatePhysical.full_word
#check Solidity.Yul.World.DelegatePhysical.target_unchanged
#check Solidity.Yul.World.DelegatePhysical.no_transfer
#check Solidity.Yul.World.DelegatePhysical.outer_rollback
#check Solidity.Yul.World.DelegateEntry.execute
#check Solidity.Yul.World.DelegateEntry.selection
#check Solidity.Yul.World.DelegateEntry.success
#check Solidity.Yul.World.DelegateEntry.rollback_write
#check Solidity.Yul.World.DelegateEntry.revert_exact
#check Solidity.Yul.World.DelegateEntry.timeout
#check Solidity.Yul.World.DelegateEntry.success_frame
#check Solidity.Yul.World.DelegateExtra.trueCaller
#check Solidity.Yul.World.DelegateExtra.trueObserved
#check Solidity.Yul.World.DelegateExtra.dirty_true_input
#check Solidity.Yul.World.DelegateExtra.dirty_true_call
#check Solidity.Yul.World.DelegateExtra.dirty_true_output
#check Solidity.Yul.World.DelegateExtra.wrong_code
#check Solidity.Yul.World.DelegateExtra.wrong_owner
#check Solidity.Yul.World.DelegateExtra.wrong_payload
#check Solidity.Yul.World.DelegateExtra.wrongResidual
#check Solidity.Yul.World.DelegateExtra.wrong_padding
#check Solidity.Yul.World.DelegateExtra.full_return_window
#check Solidity.Yul.World.DelegateExtra.full_error_size
#check Solidity.Yul.World.DelegateExtra.error_window
#check Solidity.Yul.World.DelegateExtra.output_prefix
#check Solidity.Yul.World.DelegateRules.Configuration
#check Solidity.Yul.World.DelegateRules.Step
#check Solidity.Yul.World.DelegateRules.success_sound
#check Solidity.Yul.World.DelegateRules.revert_sound
#check Solidity.Yul.World.DelegateRules.inhabited_success
#check Solidity.Yul.World.DelegatePending.invoke
#check Solidity.Yul.World.DelegatePending.empty_actual
#check Solidity.Yul.World.DelegatePending.actual
#check Solidity.Yul.World.DelegatePending.call_pending
#check Solidity.Yul.World.DelegatePending.witnessed
#check Solidity.Yul.World.DelegateOutput.completed
#check Solidity.Yul.World.DelegateOutput.heap_eq
#check Solidity.Yul.World.DelegateOutput.shared
#check Solidity.Yul.World.DelegateOutput.reads
#check Solidity.Yul.World.DelegateOutput.data
#check Solidity.Yul.World.DelegateOutput.inside
#check Solidity.Yul.World.DelegateOutput.copy
#check Solidity.Yul.World.DelegateOutput.expected
#check Solidity.Yul.World.DelegateOutput.copy_exact
#check Solidity.Yul.World.DelegateOutput.called
#check Solidity.Yul.World.DelegateOutput.called_exact
#check Solidity.Yul.World.DelegateOutput.runAndCopy
#check Solidity.Yul.World.DelegateOutput.runAndCopy_exact
#check Solidity.Yul.World.DelegateOutput.exact_destination
#check Solidity.Yul.World.DelegateOutput.untouched_tail
#check Solidity.Yul.World.HeapOutputTransport.placement
#check Solidity.Yul.World.HeapOutputTransport.found
#check Solidity.Yul.World.HeapOutputTransport.copy
#check Solidity.Yul.World.HeapOutputTransport.image
#check Solidity.Yul.World.HeapOutputTransport.exact_copy
#check Solidity.Yul.World.HeapOutputTransport.CopyResult
#check Solidity.Yul.World.HeapOutputTransport.sequence
#check Solidity.Yul.World.HeapOutputTransport.sequence_exact
#check Solidity.Yul.World.HeapOutputTransport.window
#check Solidity.Yul.World.HeapOutputTransport.window_exact
#check Solidity.Yul.World.HeapOutputTransport.window_bad_source
#check Solidity.Yul.World.HeapOutputTransport.sequenceWindow
#check Solidity.Yul.World.HeapOutputTransport.sequenceWindow_exact
#check Solidity.Yul.World.HeapOutputTransport.destination_refused
#check Solidity.Yul.World.HeapOutputTransport.image_frame
#check Solidity.Yul.World.HeapOutputTransport.image_memOK
#check Solidity.Yul.World.DelegateOutputChecks.outside_bytes
#check Solidity.Yul.World.DelegateOutputChecks.header_preserved
#check Solidity.Yul.World.DelegateOutputChecks.full_state
#check Solidity.Yul.World.DelegateOutputChecks.destination_refusal
#check Solidity.Yul.World.DelegateOutputChecks.stale_refusal
#check Solidity.Yul.World.DelegateOutputChecks.actual_buffer
#check Solidity.Yul.World.DelegateOutputChecks.full_prefix
#check Solidity.Yul.World.DelegateOutputChecks.completed_memOK
#check Solidity.Yul.World.DelegateOutputChecks.copied_memOK
#check Solidity.Yul.World.DelegateOutputFailure.completed
#check Solidity.Yul.World.DelegateOutputFailure.heap_eq
#check Solidity.Yul.World.DelegateOutputFailure.shared
#check Solidity.Yul.World.DelegateOutputFailure.called
#check Solidity.Yul.World.DelegateOutputFailure.called_exact
#check Solidity.Yul.World.DelegateOutputFailure.runWindow
#check Solidity.Yul.World.DelegateOutputFailure.expected
#check Solidity.Yul.World.DelegateOutputFailure.inside
#check Solidity.Yul.World.DelegateOutputFailure.argument_copy
#check Solidity.Yul.World.DelegateOutputFailure.exact_end_window
#check Solidity.Yul.World.DelegateOutputFailure.zero_inside
#check Solidity.Yul.World.DelegateOutputFailure.exact_end_zero
#check Solidity.Yul.World.DelegateOutputFailure.out_of_source_zero
#check Solidity.Yul.World.DelegateOutputPort.heap_eq
#check Solidity.Yul.World.DelegateOutputPort.run
#check Solidity.Yul.World.DelegateOutputPort.run_exact
#check Solidity.Yul.World.DelegateOutputRules.Configuration
#check Solidity.Yul.World.DelegateOutputRules.initial
#check Solidity.Yul.World.DelegateOutputRules.Step
#check Solidity.Yul.World.DelegateOutputRules.normal_sound
#check Solidity.Yul.World.DelegateOutputRules.inhabited
#check Solidity.Yul.World.DelegateRevertBoundary.invoke_empty
#check Solidity.Yul.World.DelegateRevertBoundary.invoke_actual
#check Solidity.Yul.World.DelegateRevertBoundary.call_revert
#check Solidity.Yul.World.DelegateRevertControls.extraLog
#check Solidity.Yul.World.DelegateRevertControls.tracePrefix
#check Solidity.Yul.World.DelegateRevertControls.locals
#check Solidity.Yul.World.DelegateRevertControls.functionLocals
#check Solidity.Yul.World.DelegateRevertControls.entry
#check Solidity.Yul.World.DelegateRevertControls.source
#check Solidity.Yul.World.DelegateRevertControls.observer
#check Solidity.Yul.World.DelegateRevertControls.residue
#check Solidity.Yul.World.DelegateRevertControls.encoding
#check Solidity.Yul.World.DelegateRevertControls.prepare
#check Solidity.Yul.World.DelegateRevertControls.ready
#check Solidity.Yul.World.DelegateRevertControls.plan
#check Solidity.Yul.World.DelegateRevertControls.run
#check Solidity.Yul.World.DelegateRevertControls.expected
#check Solidity.Yul.World.DelegateRevertControls.argument
#check Solidity.Yul.World.DelegateRevertControls.exact_end
#check Solidity.Yul.World.DelegateRevertControls.invalid_zero
#check Solidity.Yul.World.DelegateRevertControls.dirty_prefixes
#check Solidity.Yul.World.DelegateRevertControls.mutation_then_rollback
#check Solidity.Yul.World.DelegateRevertControls.not_old_caller
#check Solidity.Yul.World.DelegateRevertControls.false_caller_observer
#check Solidity.Yul.World.DelegateRevertControls.stale_buffer
#check Solidity.Yul.World.DelegateRevertHeap.copied
#check Solidity.Yul.World.DelegateRevertHeap.image_exact
#check Solidity.Yul.World.DelegateRevertHeap.fields
#check Solidity.Yul.World.DelegateRevertHeap.alias
#check Solidity.Yul.World.DelegateRevertHeap.other
#check Solidity.Yul.World.DelegateRevertHeap.types
#check Solidity.Yul.World.DelegateRevertHeap.memOK
#check Solidity.Yul.World.DelegateRevertHeap.image_empty
#check Solidity.Yul.World.DelegateRevertPort.completed
#check Solidity.Yul.World.DelegateRevertPort.heap_eq
#check Solidity.Yul.World.DelegateRevertPort.run
#check Solidity.Yul.World.DelegateRevertPort.run_exact
#check Solidity.Yul.World.DelegateRevertPort.argument_copy
#check Solidity.Yul.World.DelegateRevertPort.exact_end_zero
#check Solidity.Yul.World.DelegateRevertPort.out_of_source_zero
#check Solidity.Yul.World.DelegateRevertPort.runBefore
#check Solidity.Yul.World.DelegateRevertPort.before_agrees
#check Solidity.Yul.World.DelegateRevertOutput.run
#check Solidity.Yul.World.DelegateRevertOutput.run_exact
#check Solidity.Yul.World.DelegateRevertOutput.post_rule
#check Solidity.Yul.World.DelegateRevertOutput.exact_end_identity
#check Solidity.Yul.World.DelegateRevertWitness.old
#check Solidity.Yul.World.DelegateRevertWitness.heap
#check Solidity.Yul.World.DelegateRevertWitness.live
#check Solidity.Yul.World.DelegateRevertWitness.placement
#check Solidity.Yul.World.DelegateRevertWitness.inputEntry
#check Solidity.Yul.World.DelegateRevertWitness.outputEntry
#check Solidity.Yul.World.DelegateRevertWitness.memory
#check Solidity.Yul.World.DelegateRevertWitness.distinct_entries
#check Solidity.Yul.World.DelegateRevertWitness.locals
#check Solidity.Yul.World.DelegateRevertWitness.fnLocals
#check Solidity.Yul.World.DelegateRevertWitness.source
#check Solidity.Yul.World.DelegateRevertWitness.loaded
#check Solidity.Yul.World.DelegateRevertWitness.reads
#check Solidity.Yul.World.DelegateRevertWitness.run
#check Solidity.Yul.World.DelegateRevertWitness.expected
#check Solidity.Yul.World.DelegateRevertWitness.run_exact
#check Solidity.Yul.World.DelegateRevertWitness.alias_readback
#check Solidity.Yul.World.DelegateRevertWitness.actual_mutation
#check Solidity.Yul.World.DelegateRevertWitness.input_untouched
#check Solidity.Yul.World.DelegateRevertWitness.childEntry
#check Solidity.Yul.World.DelegateRevertWitness.actual_body_reverts
#check Solidity.Yul.World.DelegateRevertWitness.source_write_is_nontrivial
#check Solidity.Yul.World.DelegateRevertWitness.full_image
#check Solidity.Yul.World.DelegateRevertWitness.wrong_heap
#check Solidity.Yul.World.DelegateRevertWitness.after
#check Solidity.Yul.World.DelegateRevertWitness.alias_evaluation
#check Solidity.Yul.World.DelegateRevertWitness.source_memOK
#check Solidity.Yul.World.DelegateRevertWitness.after_memOK
#check Solidity.Yul.World.DelegateSuccessBoundary.updated
#check Solidity.Yul.World.DelegateSuccessBoundary.completed
#check Solidity.Yul.World.DelegateSuccessBoundary.physical_coupled
#check Solidity.Yul.World.DelegateSuccessBoundary.invoke_empty
#check Solidity.Yul.World.DelegateSuccessBoundary.invoke_actual
#check Solidity.Yul.World.DelegateSuccessBoundary.call_success
#check Solidity.Yul.World.DelegateSuccessBoundary.enclosing_revert
#check Solidity.Yul.World.DelegateSuccessPreparation.selected_encoding
#check Solidity.Yul.World.DelegateSuccessPreparation.source_op
#check Solidity.Yul.World.DelegateSuccessFraming.image_empty
#check Solidity.Yul.World.DelegateSuccessFraming.other
#check Solidity.Yul.World.DelegateSuccessFraming.fields
#check Solidity.Yul.World.DelegateSuccessFraming.raw_outside
#check Solidity.Yul.World.DelegateSuccessFraming.witness_outer
#check Solidity.Yul.World.DelegateSuccessWitness.result
#check Solidity.Yul.World.DelegateSuccessWitness.run
#check Solidity.Yul.World.DelegateSuccessWitness.expected
#check Solidity.Yul.World.DelegateSuccessWitness.run_exact
#check Solidity.Yul.World.DelegateSuccessWitness.automatic
#check Solidity.Yul.World.DelegateSuccessWitness.automatic_exact
#check Solidity.Yul.World.DelegateSuccessWitness.successful_effects
#check Solidity.Yul.World.DelegateSuccessWitness.different_prefix
#check Solidity.Yul.World.DelegateSuccessWitness.success_not_rollback
#check Solidity.Yul.World.DelegateSuccessWitness.after
#check Solidity.Yul.World.DelegateSuccessWitness.full_image
#check Solidity.Yul.World.DelegateSuccessWitness.aliases
#check Solidity.Yul.World.DelegateSuccessWitness.input_untouched
#check Solidity.Yul.World.DelegateSuccessWitness.exact_end
#check Solidity.Yul.World.DelegateSuccessWitness.invalid_zero
#check Solidity.Yul.World.DelegateSuccessWitness.stale_buffer
#check Solidity.Yul.World.DelegateSuccessWitness.after_memOK
#check Solidity.Yul.World.DelegateSuccessOutput.run
#check Solidity.Yul.World.DelegateSuccessOutput.run_exact
#check Solidity.Yul.World.DelegateSuccessOutput.post_rule
#check Solidity.Yul.World.DelegateSuccessPort.heap_eq
#check Solidity.Yul.World.DelegateSuccessPort.run
#check Solidity.Yul.World.DelegateSuccessPort.run_exact
#check Solidity.Yul.World.DelegateSuccessPort.argument_copy
#check Solidity.Yul.World.DelegateSuccessPort.exact_end_zero
#check Solidity.Yul.World.DelegateSuccessPort.out_of_source_zero
#check Solidity.Yul.World.DelegateSuccessSlot.full_word
#check Solidity.Yul.World.DelegateSuccessSlot.complement
#check Solidity.Yul.World.DelegateSuccessSlot.residual_other
#check Solidity.Yul.World.DelegateSuccessSlot.account_other
#check Solidity.Yul.World.DelegateSuccessSlot.witness_word
#check Solidity.Yul.World.DelegateSuccessSlot.wrong_old_word
#check Solidity.Yul.World.DelegateSuccessSlot.transient_unchanged
#print axioms Solidity.Yul.World.DelegateBody.internal_success
#print axioms Solidity.Yul.World.DelegateBody.internal_revert
#print axioms Solidity.Yul.World.DelegateBody.picked
#print axioms Solidity.Yul.World.DelegateBody.dispatch_success
#print axioms Solidity.Yul.World.DelegateBody.enter_success
#print axioms Solidity.Yul.World.DelegateBody.dispatch_revert
#print axioms Solidity.Yul.World.DelegateBody.enter_revert
#print axioms Solidity.Yul.World.DelegateBody.internal_timeout
#print axioms Solidity.Yul.World.DelegateBody.dispatch_timeout
#print axioms Solidity.Yul.World.DelegateBody.enter_timeout
#print axioms Solidity.Yul.World.DelegateBody.read_body_timeout
#print axioms Solidity.Yul.World.StateCallRules.success_sound
#print axioms Solidity.Yul.World.StateCallRules.revert_sound
#print axioms Solidity.Yul.World.StateCallRules.inhabited_success
#print axioms Solidity.Yul.World.StateCallRules.inhabited_revert
#print axioms Solidity.Yul.World.StateCallExtra.low_empty
#print axioms Solidity.Yul.World.StateCallExtra.low_actual
#print axioms Solidity.Yul.World.StateCallExtra.low_call
#print axioms Solidity.Yul.World.StateCallExtra.low_witness
#print axioms Solidity.Yul.World.StateCallExtra.error_length
#print axioms Solidity.Yul.World.StateCallExtra.error_window
#print axioms Solidity.Yul.World.StateCallExtra.source_prefix_journals
#print axioms Solidity.Yul.World.StateCallExtra.success_full_word
#print axioms Solidity.Yul.World.StateCallExtra.dirty_true_input
#print axioms Solidity.Yul.World.StateCallExtra.dirty_true_success
#print axioms Solidity.Yul.World.StateCallExtra.dirty_true_output
#print axioms Solidity.Yul.World.StateCallExtra.pending_controls
#print axioms Solidity.Yul.World.StateCallExtra.success_size
#print axioms Solidity.Yul.World.StateCallExtra.revert_size
#print axioms Solidity.Yul.World.StateCallChecks.loaded
#print axioms Solidity.Yul.World.StateCallChecks.success
#print axioms Solidity.Yul.World.StateCallChecks.reverted
#print axioms Solidity.Yul.World.StateCallChecks.outer_after_success
#print axioms Solidity.Yul.World.StateCallChecks.static_reverted
#print axioms Solidity.Yul.World.StateCallChecks.written_value
#print axioms Solidity.Yul.World.StateCallChecks.caller_storage
#print axioms Solidity.Yul.World.StateCallChecks.full_prefix
#print axioms Solidity.Yul.World.StateCallChecks.initial_full_word
#print axioms Solidity.Yul.World.StateCallChecks.initial_bool
#print axioms Solidity.Yul.World.StateCallChecks.padding_unchanged
#print axioms Solidity.Yul.World.StateCallChecks.aliases
#print axioms Solidity.Yul.World.StateCallChecks.padding_refused
#print axioms Solidity.Yul.World.StateCallChecks.wrong_padding_refused
#print axioms Solidity.Yul.World.StateCallChecks.wrong_owner_refused
#print axioms Solidity.Yul.World.StateCallChecks.wrong_code_refused
#print axioms Solidity.Yul.World.StateCallChecks.caller_memOK
#print axioms Solidity.Yul.World.StateCall.static_internal
#print axioms Solidity.Yul.World.StateCall.static_dispatch
#print axioms Solidity.Yul.World.StateCall.static_enter
#print axioms Solidity.Yul.World.StateCall.static_source
#print axioms Solidity.Yul.World.StateCall.static_physical
#print axioms Solidity.Yul.World.StateCallPort.static_invoke_empty
#print axioms Solidity.Yul.World.StateCallPort.static_invoke_actual
#print axioms Solidity.Yul.World.StateCallPort.static_finish
#print axioms Solidity.Yul.World.StateCallPort.static_call
#print axioms Solidity.Yul.World.StateCallPort.invoke_success_empty
#print axioms Solidity.Yul.World.StateCallPort.invoke_revert_empty
#print axioms Solidity.Yul.World.StateCallPort.invoke_success_actual
#print axioms Solidity.Yul.World.StateCallPort.invoke_revert_actual
#print axioms Solidity.Yul.World.StateCallPort.call_success
#print axioms Solidity.Yul.World.StateCallPort.call_revert
#print axioms Solidity.Yul.World.StateCallPort.outer_revert
#print axioms Solidity.Yul.World.StateCall.internal_timeout
#print axioms Solidity.Yul.World.StateCall.dispatch_timeout
#print axioms Solidity.Yul.World.StateCall.enter_timeout
#print axioms Solidity.Yul.World.StateCall.source_timeout
#print axioms Solidity.Yul.World.StateCall.empty_dispatch
#print axioms Solidity.Yul.World.DelegateChecks.distinct
#print axioms Solidity.Yul.World.DelegateChecks.success
#print axioms Solidity.Yul.World.DelegateChecks.reverted_call
#print axioms Solidity.Yul.World.DelegateChecks.static_refusal
#print axioms Solidity.Yul.World.DelegateChecks.enclosing
#print axioms Solidity.Yul.World.DelegateChecks.full_state
#print axioms Solidity.Yul.World.DelegateChecks.inherited_context
#print axioms Solidity.Yul.World.DelegateChecks.input_view
#print axioms Solidity.Yul.World.DelegateChecks.output_view
#print axioms Solidity.Yul.World.DelegateChecks.precompile_control
#print axioms Solidity.Yul.World.DelegatePort.success_actual
#print axioms Solidity.Yul.World.DelegatePort.revert_actual
#print axioms Solidity.Yul.World.DelegatePort.call_success
#print axioms Solidity.Yul.World.DelegatePort.call_revert
#print axioms Solidity.Yul.World.DelegatePort.enclosing_revert
#print axioms Solidity.Yul.World.DelegatePort.static_actual
#print axioms Solidity.Yul.World.DelegatePort.call_static
#print axioms Solidity.Yul.World.DelegatePort.success_empty
#print axioms Solidity.Yul.World.DelegatePort.revert_empty
#print axioms Solidity.Yul.World.DelegatePort.static_empty
#print axioms Solidity.Yul.World.DelegatePort.precompile_refused
#print axioms Solidity.Yul.World.DelegatePort.depth_refused
#print axioms Solidity.Yul.World.DelegatePort.zero_refused
#print axioms Solidity.Yul.World.DelegatePort.owner_refused
#print axioms Solidity.Yul.World.DelegatePort.payload_refused
#print axioms Solidity.Yul.World.DelegatePort.padding_refused
#print axioms Solidity.Yul.World.DelegateStatic.static_internal
#print axioms Solidity.Yul.World.DelegateStatic.static_dispatch
#print axioms Solidity.Yul.World.DelegateStatic.static_enter
#print axioms Solidity.Yul.World.DelegateStatic.execute_revert
#print axioms Solidity.Yul.World.DelegatePhysical.ready
#print axioms Solidity.Yul.World.DelegatePhysical.source_op
#print axioms Solidity.Yul.World.DelegatePhysical.complement
#print axioms Solidity.Yul.World.DelegatePhysical.step_exact
#print axioms Solidity.Yul.World.DelegatePhysical.full_word
#print axioms Solidity.Yul.World.DelegatePhysical.target_unchanged
#print axioms Solidity.Yul.World.DelegatePhysical.no_transfer
#print axioms Solidity.Yul.World.DelegatePhysical.outer_rollback
#print axioms Solidity.Yul.World.DelegateEntry.selection
#print axioms Solidity.Yul.World.DelegateEntry.success
#print axioms Solidity.Yul.World.DelegateEntry.rollback_write
#print axioms Solidity.Yul.World.DelegateEntry.revert_exact
#print axioms Solidity.Yul.World.DelegateEntry.timeout
#print axioms Solidity.Yul.World.DelegateEntry.success_frame
#print axioms Solidity.Yul.World.DelegateExtra.dirty_true_input
#print axioms Solidity.Yul.World.DelegateExtra.dirty_true_call
#print axioms Solidity.Yul.World.DelegateExtra.dirty_true_output
#print axioms Solidity.Yul.World.DelegateExtra.wrong_code
#print axioms Solidity.Yul.World.DelegateExtra.wrong_owner
#print axioms Solidity.Yul.World.DelegateExtra.wrong_payload
#print axioms Solidity.Yul.World.DelegateExtra.wrong_padding
#print axioms Solidity.Yul.World.DelegateExtra.full_return_window
#print axioms Solidity.Yul.World.DelegateExtra.full_error_size
#print axioms Solidity.Yul.World.DelegateExtra.error_window
#print axioms Solidity.Yul.World.DelegateExtra.output_prefix
#print axioms Solidity.Yul.World.DelegateRules.success_sound
#print axioms Solidity.Yul.World.DelegateRules.revert_sound
#print axioms Solidity.Yul.World.DelegateRules.inhabited_success
#print axioms Solidity.Yul.World.DelegatePending.empty_actual
#print axioms Solidity.Yul.World.DelegatePending.actual
#print axioms Solidity.Yul.World.DelegatePending.call_pending
#print axioms Solidity.Yul.World.DelegatePending.witnessed
#print axioms Solidity.Yul.World.DelegateOutput.heap_eq
#print axioms Solidity.Yul.World.DelegateOutput.shared
#print axioms Solidity.Yul.World.DelegateOutput.reads
#print axioms Solidity.Yul.World.DelegateOutput.data
#print axioms Solidity.Yul.World.DelegateOutput.inside
#print axioms Solidity.Yul.World.DelegateOutput.copy_exact
#print axioms Solidity.Yul.World.DelegateOutput.called_exact
#print axioms Solidity.Yul.World.DelegateOutput.runAndCopy_exact
#print axioms Solidity.Yul.World.DelegateOutput.exact_destination
#print axioms Solidity.Yul.World.DelegateOutput.untouched_tail
#print axioms Solidity.Yul.World.HeapOutputTransport.exact_copy
#print axioms Solidity.Yul.World.HeapOutputTransport.sequence_exact
#print axioms Solidity.Yul.World.HeapOutputTransport.window_exact
#print axioms Solidity.Yul.World.HeapOutputTransport.window_bad_source
#print axioms Solidity.Yul.World.HeapOutputTransport.sequenceWindow_exact
#print axioms Solidity.Yul.World.HeapOutputTransport.destination_refused
#print axioms Solidity.Yul.World.HeapOutputTransport.image_frame
#print axioms Solidity.Yul.World.HeapOutputTransport.image_memOK
#print axioms Solidity.Yul.World.DelegateOutputChecks.outside_bytes
#print axioms Solidity.Yul.World.DelegateOutputChecks.header_preserved
#print axioms Solidity.Yul.World.DelegateOutputChecks.full_state
#print axioms Solidity.Yul.World.DelegateOutputChecks.destination_refusal
#print axioms Solidity.Yul.World.DelegateOutputChecks.stale_refusal
#print axioms Solidity.Yul.World.DelegateOutputChecks.actual_buffer
#print axioms Solidity.Yul.World.DelegateOutputChecks.full_prefix
#print axioms Solidity.Yul.World.DelegateOutputChecks.completed_memOK
#print axioms Solidity.Yul.World.DelegateOutputChecks.copied_memOK
#print axioms Solidity.Yul.World.DelegateOutputFailure.heap_eq
#print axioms Solidity.Yul.World.DelegateOutputFailure.shared
#print axioms Solidity.Yul.World.DelegateOutputFailure.called_exact
#print axioms Solidity.Yul.World.DelegateOutputFailure.inside
#print axioms Solidity.Yul.World.DelegateOutputFailure.argument_copy
#print axioms Solidity.Yul.World.DelegateOutputFailure.exact_end_window
#print axioms Solidity.Yul.World.DelegateOutputFailure.zero_inside
#print axioms Solidity.Yul.World.DelegateOutputFailure.exact_end_zero
#print axioms Solidity.Yul.World.DelegateOutputFailure.out_of_source_zero
#print axioms Solidity.Yul.World.DelegateOutputPort.heap_eq
#print axioms Solidity.Yul.World.DelegateOutputPort.run_exact
#print axioms Solidity.Yul.World.DelegateOutputRules.normal_sound
#print axioms Solidity.Yul.World.DelegateOutputRules.inhabited
#print axioms Solidity.Yul.World.DelegateRevertBoundary.invoke_empty
#print axioms Solidity.Yul.World.DelegateRevertBoundary.invoke_actual
#print axioms Solidity.Yul.World.DelegateRevertBoundary.call_revert
#print axioms Solidity.Yul.World.DelegateRevertControls.ready
#print axioms Solidity.Yul.World.DelegateRevertControls.argument
#print axioms Solidity.Yul.World.DelegateRevertControls.exact_end
#print axioms Solidity.Yul.World.DelegateRevertControls.invalid_zero
#print axioms Solidity.Yul.World.DelegateRevertControls.dirty_prefixes
#print axioms Solidity.Yul.World.DelegateRevertControls.mutation_then_rollback
#print axioms Solidity.Yul.World.DelegateRevertControls.not_old_caller
#print axioms Solidity.Yul.World.DelegateRevertControls.false_caller_observer
#print axioms Solidity.Yul.World.DelegateRevertControls.stale_buffer
#print axioms Solidity.Yul.World.DelegateRevertHeap.image_exact
#print axioms Solidity.Yul.World.DelegateRevertHeap.fields
#print axioms Solidity.Yul.World.DelegateRevertHeap.alias
#print axioms Solidity.Yul.World.DelegateRevertHeap.other
#print axioms Solidity.Yul.World.DelegateRevertHeap.types
#print axioms Solidity.Yul.World.DelegateRevertHeap.memOK
#print axioms Solidity.Yul.World.DelegateRevertHeap.image_empty
#print axioms Solidity.Yul.World.DelegateRevertPort.heap_eq
#print axioms Solidity.Yul.World.DelegateRevertPort.run_exact
#print axioms Solidity.Yul.World.DelegateRevertPort.argument_copy
#print axioms Solidity.Yul.World.DelegateRevertPort.exact_end_zero
#print axioms Solidity.Yul.World.DelegateRevertPort.out_of_source_zero
#print axioms Solidity.Yul.World.DelegateRevertPort.before_agrees
#print axioms Solidity.Yul.World.DelegateRevertOutput.run_exact
#print axioms Solidity.Yul.World.DelegateRevertOutput.post_rule
#print axioms Solidity.Yul.World.DelegateRevertOutput.exact_end_identity
#print axioms Solidity.Yul.World.DelegateRevertWitness.live
#print axioms Solidity.Yul.World.DelegateRevertWitness.distinct_entries
#print axioms Solidity.Yul.World.DelegateRevertWitness.loaded
#print axioms Solidity.Yul.World.DelegateRevertWitness.reads
#print axioms Solidity.Yul.World.DelegateRevertWitness.run_exact
#print axioms Solidity.Yul.World.DelegateRevertWitness.alias_readback
#print axioms Solidity.Yul.World.DelegateRevertWitness.actual_mutation
#print axioms Solidity.Yul.World.DelegateRevertWitness.input_untouched
#print axioms Solidity.Yul.World.DelegateRevertWitness.actual_body_reverts
#print axioms Solidity.Yul.World.DelegateRevertWitness.source_write_is_nontrivial
#print axioms Solidity.Yul.World.DelegateRevertWitness.full_image
#print axioms Solidity.Yul.World.DelegateRevertWitness.wrong_heap
#print axioms Solidity.Yul.World.DelegateRevertWitness.alias_evaluation
#print axioms Solidity.Yul.World.DelegateRevertWitness.source_memOK
#print axioms Solidity.Yul.World.DelegateRevertWitness.after_memOK
#print axioms Solidity.Yul.World.DelegateSuccessBoundary.physical_coupled
#print axioms Solidity.Yul.World.DelegateSuccessBoundary.invoke_empty
#print axioms Solidity.Yul.World.DelegateSuccessBoundary.invoke_actual
#print axioms Solidity.Yul.World.DelegateSuccessBoundary.call_success
#print axioms Solidity.Yul.World.DelegateSuccessBoundary.enclosing_revert
#print axioms Solidity.Yul.World.DelegateSuccessPreparation.selected_encoding
#print axioms Solidity.Yul.World.DelegateSuccessPreparation.source_op
#print axioms Solidity.Yul.World.DelegateSuccessFraming.image_empty
#print axioms Solidity.Yul.World.DelegateSuccessFraming.other
#print axioms Solidity.Yul.World.DelegateSuccessFraming.fields
#print axioms Solidity.Yul.World.DelegateSuccessFraming.raw_outside
#print axioms Solidity.Yul.World.DelegateSuccessFraming.witness_outer
#print axioms Solidity.Yul.World.DelegateSuccessWitness.run_exact
#print axioms Solidity.Yul.World.DelegateSuccessWitness.automatic_exact
#print axioms Solidity.Yul.World.DelegateSuccessWitness.successful_effects
#print axioms Solidity.Yul.World.DelegateSuccessWitness.different_prefix
#print axioms Solidity.Yul.World.DelegateSuccessWitness.success_not_rollback
#print axioms Solidity.Yul.World.DelegateSuccessWitness.full_image
#print axioms Solidity.Yul.World.DelegateSuccessWitness.aliases
#print axioms Solidity.Yul.World.DelegateSuccessWitness.input_untouched
#print axioms Solidity.Yul.World.DelegateSuccessWitness.exact_end
#print axioms Solidity.Yul.World.DelegateSuccessWitness.invalid_zero
#print axioms Solidity.Yul.World.DelegateSuccessWitness.stale_buffer
#print axioms Solidity.Yul.World.DelegateSuccessWitness.after_memOK
#print axioms Solidity.Yul.World.DelegateSuccessOutput.run_exact
#print axioms Solidity.Yul.World.DelegateSuccessOutput.post_rule
#print axioms Solidity.Yul.World.DelegateSuccessPort.heap_eq
#print axioms Solidity.Yul.World.DelegateSuccessPort.run_exact
#print axioms Solidity.Yul.World.DelegateSuccessPort.argument_copy
#print axioms Solidity.Yul.World.DelegateSuccessPort.exact_end_zero
#print axioms Solidity.Yul.World.DelegateSuccessPort.out_of_source_zero
#print axioms Solidity.Yul.World.DelegateSuccessSlot.full_word
#print axioms Solidity.Yul.World.DelegateSuccessSlot.complement
#print axioms Solidity.Yul.World.DelegateSuccessSlot.residual_other
#print axioms Solidity.Yul.World.DelegateSuccessSlot.account_other
#print axioms Solidity.Yul.World.DelegateSuccessSlot.witness_word
#print axioms Solidity.Yul.World.DelegateSuccessSlot.wrong_old_word
#print axioms Solidity.Yul.World.DelegateSuccessSlot.transient_unchanged
