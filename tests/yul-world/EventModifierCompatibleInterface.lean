import Solidity.Yul.World.EffectfulEmitControls
import Solidity.Yul.World.HeapWindowChecks
import Solidity.Yul.World.LocalEventBoundary
import Solidity.Yul.World.StaticEventRaw
import Solidity.Yul.World.StaticEventPortControls
import Solidity.Yul.World.MemoryEventControls
import Solidity.Yul.World.MemoryEventSource
import Solidity.Yul.World.MemoryEventEncoding
import Solidity.Yul.World.MemoryEventTopic
import Solidity.Yul.World.MemoryEventPort
import Solidity.Yul.World.MemoryEventPortControls
import Solidity.Yul.World.MemoryEventRaw
import Solidity.Yul.World.MemoryEventWitness
import Solidity.Yul.World.SourceHeapBoundary
import Solidity.Yul.World.SourceModifierArgument
import Solidity.Yul.World.SourceModifierBoundary
import Solidity.Yul.World.SourceModifierArgumentChecks
import Solidity.Yul.World.SourceModifierCall
import Solidity.Yul.World.SourceModifierFrame
import Solidity.Yul.World.SourceModifierFrameChecks

#check Solidity.Yul.World.EffectfulEmitControls.E
#check Solidity.Yul.World.EffectfulEmitControls.owner
#check Solidity.Yul.World.EffectfulEmitControls.other
#check Solidity.Yul.World.EffectfulEmitControls.frame
#check Solidity.Yul.World.EffectfulEmitControls.initial
#check Solidity.Yul.World.EffectfulEmitControls.entry
#check Solidity.Yul.World.EffectfulEmitControls.heap
#check Solidity.Yul.World.EffectfulEmitControls.locals
#check Solidity.Yul.World.EffectfulEmitControls.state
#check Solidity.Yul.World.EffectfulEmitControls.residual
#check Solidity.Yul.World.EffectfulEmitControls.encoding
#check Solidity.Yul.World.EffectfulEmitControls.observed
#check Solidity.Yul.World.EffectfulEmitControls.prepared
#check Solidity.Yul.World.EffectfulEmitControls.ready
#check Solidity.Yul.World.EffectfulEmitControls.plan
#check Solidity.Yul.World.EffectfulEmitControls.before_view
#check Solidity.Yul.World.EffectfulEmitControls.caller_prefixes
#check Solidity.Yul.World.EffectfulEmitControls.program
#check Solidity.Yul.World.EffectfulEmitControls.global
#check Solidity.Yul.World.EffectfulEmitControls.actual
#check Solidity.Yul.World.EffectfulEmitControls.wrongResidual
#check Solidity.Yul.World.EffectfulEmitControls.wrong_padding
#check Solidity.Yul.World.EffectfulEmitControls.wrong_view
#check Solidity.Yul.World.EffectfulEmitControls.correct_wrong_patch
#check Solidity.Yul.World.HeapWindowChecks.n33
#check Solidity.Yul.World.HeapWindowChecks.entry
#check Solidity.Yul.World.HeapWindowChecks.byteResult
#check Solidity.Yul.World.HeapWindowChecks.byte_crosses_word
#check Solidity.Yul.World.HeapWindowChecks.caller
#check Solidity.Yul.World.HeapWindowChecks.caller_ok
#check Solidity.Yul.World.HeapWindowChecks.stringResult
#check Solidity.Yul.World.HeapWindowChecks.string_reads
#check Solidity.Yul.World.HeapWindowChecks.string_crosses_word
#check Solidity.Yul.World.HeapWindowChecks.stateResult
#check Solidity.Yul.World.HeapWindowChecks.state_copy
#check Solidity.Yul.World.HeapWindowChecks.real_owner_memOK
#check Solidity.Yul.World.HeapWindowChecks.full_source_prefix
#check Solidity.Yul.World.HeapWindowChecks.source_alias
#check Solidity.Yul.World.HeapWindowChecks.shorter_prefix
#check Solidity.Yul.World.HeapWindowChecks.wrong_destination
#check Solidity.Yul.World.HeapWindowChecks.bad_source_zero
#check Solidity.Yul.World.HeapWindowChecks.beyond_payload_zero
#check Solidity.Yul.World.HeapWindowChecks.exact_end_zero
#check Solidity.Yul.World.HeapWindowChecks.unchanged_string_sides
#check Solidity.Yul.World.HeapWindowChecks.outside_and_other_cell
#check Solidity.Yul.World.HeapWindowChecks.header_and_reserved
#check Solidity.Yul.World.HeapWindowChecks.other_typed_image
#check Solidity.Yul.World.HeapWindowChecks.observed
#check Solidity.Yul.World.HeapWindowChecks.residual
#check Solidity.Yul.World.HeapWindowChecks.encoding
#check Solidity.Yul.World.HeapWindowChecks.coupled_all_fields
#check Solidity.Yul.World.HeapWindowChecks.actual_prefix_journals
#check Solidity.Yul.World.HeapWindowChecks.local_rule
#check Solidity.Yul.World.HeapWindowChecks.callObserved
#check Solidity.Yul.World.HeapWindowChecks.parent
#check Solidity.Yul.World.HeapWindowChecks.afterCall
#check Solidity.Yul.World.HeapWindowChecks.raw_call_short_output
#check Solidity.Yul.World.HeapWindowChecks.call_source_prefix
#check Solidity.Yul.World.HeapWindowChecks.call_buffer_writeback
#check Solidity.Yul.World.HeapWindowChecks.stale_buffer_refused
#check Solidity.Yul.World.HeapWindowChecks.wrong_selected_object
#check Solidity.Yul.World.HeapWindowChecks.postPlacement
#check Solidity.Yul.World.HeapWindowChecks.actual_post_placement
#check Solidity.Yul.World.LocalEventBoundary.LocalArguments
#check Solidity.Yul.World.LocalEventBoundary.staticExecute
#check Solidity.Yul.World.LocalEventBoundary.static_arguments_local
#check Solidity.Yul.World.StaticEventRaw.encoded_log
#check Solidity.Yul.World.StaticEventRaw.encoding_agreement
#check Solidity.Yul.World.StaticEventRaw.encoded_heap
#check Solidity.Yul.World.StaticEventRaw.mixed_source_heap
#check Solidity.Yul.World.StaticEventRaw.memory
#check Solidity.Yul.World.StaticEventRaw.loaded
#check Solidity.Yul.World.StaticEventRaw.mixed_view
#check Solidity.Yul.World.StaticEventRaw.wrong_region
#check Solidity.Yul.World.StaticEventRaw.wrong_anonymous_topics
#check Solidity.Yul.World.StaticEventRaw.source_heap_agreement
#check Solidity.Yul.World.StaticEventPortControls.shape
#check Solidity.Yul.World.StaticEventPortControls.fits
#check Solidity.Yul.World.StaticEventPortControls.run
#check Solidity.Yul.World.StaticEventPortControls.log
#check Solidity.Yul.World.StaticEventPortControls.legacyWords
#check Solidity.Yul.World.StaticEventPortControls.run_exact
#check Solidity.Yul.World.StaticEventPortControls.static_exact
#check Solidity.Yul.World.StaticEventPortControls.rollback_after
#check Solidity.Yul.World.StaticEventPortControls.ordered
#check Solidity.Yul.World.StaticEventPortControls.enclosing_revert
#check Solidity.Yul.World.MemoryEventControls.tag
#check Solidity.Yul.World.MemoryEventControls.label
#check Solidity.Yul.World.MemoryEventControls.blob
#check Solidity.Yul.World.MemoryEventControls.declaration
#check Solidity.Yul.World.MemoryEventControls.env
#check Solidity.Yul.World.MemoryEventControls.types
#check Solidity.Yul.World.MemoryEventControls.values
#check Solidity.Yul.World.MemoryEventControls.locals
#check Solidity.Yul.World.MemoryEventControls.args
#check Solidity.Yul.World.MemoryEventControls.part
#check Solidity.Yul.World.MemoryEventControls.allParts
#check Solidity.Yul.World.MemoryEventControls.dataParts
#check Solidity.Yul.World.MemoryEventControls.legacyData
#check Solidity.Yul.World.MemoryEventControls.data
#check Solidity.Yul.World.MemoryEventControls.typed
#check Solidity.Yul.World.MemoryEventControls.registered
#check Solidity.Yul.World.MemoryEventControls.shape
#check Solidity.Yul.World.MemoryEventControls.local_args
#check Solidity.Yul.World.MemoryEventControls.evaluated
#check Solidity.Yul.World.MemoryEventControls.partition
#check Solidity.Yul.World.MemoryEventControls.data_codec
#check Solidity.Yul.World.MemoryEventControls.full_codec
#check Solidity.Yul.World.MemoryEventSource.actual
#check Solidity.Yul.World.MemoryEventSource.actual_static
#check Solidity.Yul.World.MemoryEventEncoding.split
#check Solidity.Yul.World.MemoryEventEncoding.encode
#check Solidity.Yul.World.MemoryEventEncoding.encode_exact
#check Solidity.Yul.World.MemoryEventEncoding.overflow_refused
#check Solidity.Yul.World.MemoryEventTopic.topic
#check Solidity.Yul.World.MemoryEventTopic.word
#check Solidity.Yul.World.MemoryEventTopic.bytes_read
#check Solidity.Yul.World.MemoryEventTopic.string_read
#check Solidity.Yul.World.MemoryEventTopic.bytes_topic
#check Solidity.Yul.World.MemoryEventTopic.string_topic
#check Solidity.Yul.World.MemoryEventTopic.raw_hash
#check Solidity.Yul.World.MemoryEventTopic.bytes_codec
#check Solidity.Yul.World.MemoryEventTopic.string_codec
#check Solidity.Yul.World.MemoryEventTopic.storage_refused
#check Solidity.Yul.World.MemoryEventTopic.dangling_bytes
#check Solidity.Yul.World.MemoryEventPort.after
#check Solidity.Yul.World.MemoryEventPort.source_normal
#check Solidity.Yul.World.MemoryEventPort.source_static
#check Solidity.Yul.World.MemoryEventPort.execute
#check Solidity.Yul.World.MemoryEventPort.execute_normal
#check Solidity.Yul.World.MemoryEventPortControls.fits
#check Solidity.Yul.World.MemoryEventPortControls.run
#check Solidity.Yul.World.MemoryEventPortControls.log
#check Solidity.Yul.World.MemoryEventPortControls.run_exact
#check Solidity.Yul.World.MemoryEventPortControls.static_exact
#check Solidity.Yul.World.MemoryEventPortControls.wrong_preimage
#check Solidity.Yul.World.MemoryEventPortControls.cross_word
#check Solidity.Yul.World.MemoryEventPortControls.rollback_after
#check Solidity.Yul.World.MemoryEventPortControls.enclosing_revert
#check Solidity.Yul.World.MemoryEventRaw.hash_encoded
#check Solidity.Yul.World.MemoryEventRaw.reference
#check Solidity.Yul.World.MemoryEventRaw.topic_entry
#check Solidity.Yul.World.MemoryEventRaw.mixed_log
#check Solidity.Yul.World.MemoryEventRaw.source_log_agreement
#check Solidity.Yul.World.MemoryEventWitness.heap
#check Solidity.Yul.World.MemoryEventWitness.heap_found
#check Solidity.Yul.World.MemoryEventWitness.caller
#check Solidity.Yul.World.MemoryEventWitness.run
#check Solidity.Yul.World.MemoryEventWitness.run_exact
#check Solidity.Yul.World.MemoryEventWitness.actual_args
#check Solidity.Yul.World.MemoryEventWitness.aliases
#check Solidity.Yul.World.MemoryEventWitness.heap_types
#check Solidity.Yul.World.MemoryEventWitness.single
#check Solidity.Yul.World.MemoryEventWitness.any_length_topic
#check Solidity.Yul.World.MemoryEventWitness.boundaries
#check Solidity.Yul.World.MemoryEventWitness.dangling
#check Solidity.Yul.World.MemoryEventWitness.caller_memOK
#check Solidity.Yul.World.SourceHeapBoundary.enterInstance_heap
#check Solidity.Yul.World.SourceModifierArgument.parameter
#check Solidity.Yul.World.SourceModifierArgument.functionDecl
#check Solidity.Yul.World.SourceModifierArgument.failureSyntax
#check Solidity.Yul.World.SourceModifierArgument.modifierItems
#check Solidity.Yul.World.SourceModifierArgument.modifierDecl
#check Solidity.Yul.World.SourceModifierArgument.env
#check Solidity.Yul.World.SourceModifierArgument.args
#check Solidity.Yul.World.SourceModifierArgument.modifierBody
#check Solidity.Yul.World.SourceModifierArgument.body
#check Solidity.Yul.World.SourceModifierArgument.glob
#check Solidity.Yul.World.SourceModifierArgument.locals
#check Solidity.Yul.World.SourceModifierArgument.data
#check Solidity.Yul.World.SourceModifierArgument.argument_run
#check Solidity.Yul.World.SourceModifierArgument.actual
#check Solidity.Yul.World.SourceModifierArgument.entered_timeout
#check Solidity.Yul.World.SourceModifierArgument.invoked
#check Solidity.Yul.World.SourceModifierBoundary.uint
#check Solidity.Yul.World.SourceModifierBoundary.value
#check Solidity.Yul.World.SourceModifierBoundary.functionDecl
#check Solidity.Yul.World.SourceModifierBoundary.errorDecl
#check Solidity.Yul.World.SourceModifierBoundary.failureSyntax
#check Solidity.Yul.World.SourceModifierBoundary.modifierItems
#check Solidity.Yul.World.SourceModifierBoundary.modifierDecl
#check Solidity.Yul.World.SourceModifierBoundary.env
#check Solidity.Yul.World.SourceModifierBoundary.modifierBody
#check Solidity.Yul.World.SourceModifierBoundary.body
#check Solidity.Yul.World.SourceModifierBoundary.glob
#check Solidity.Yul.World.SourceModifierBoundary.data
#check Solidity.Yul.World.SourceModifierBoundary.actual
#check Solidity.Yul.World.SourceModifierBoundary.entered_timeout
#check Solidity.Yul.World.SourceModifierArgumentControls.owner
#check Solidity.Yul.World.SourceModifierArgumentControls.other
#check Solidity.Yul.World.SourceModifierArgumentControls.initial
#check Solidity.Yul.World.SourceModifierArgumentControls.entry
#check Solidity.Yul.World.SourceModifierArgumentControls.heap
#check Solidity.Yul.World.SourceModifierArgumentControls.caller
#check Solidity.Yul.World.SourceModifierArgumentControls.frame
#check Solidity.Yul.World.SourceModifierArgumentControls.selected
#check Solidity.Yul.World.SourceModifierCall.actual
#check Solidity.Yul.World.SourceModifierCall.entered_timeout
#check Solidity.Yul.World.SourceModifierFrame.fnLocals_after_arguments
#check Solidity.Yul.World.SourceModifierFrame.argument_halt
#check Solidity.Yul.World.SourceModifierFrameChecks.owner
#check Solidity.Yul.World.SourceModifierFrameChecks.other
#check Solidity.Yul.World.SourceModifierFrameChecks.initial
#check Solidity.Yul.World.SourceModifierFrameChecks.entry
#check Solidity.Yul.World.SourceModifierFrameChecks.heap
#check Solidity.Yul.World.SourceModifierFrameChecks.caller
#check Solidity.Yul.World.SourceModifierFrameChecks.frame
#print axioms Solidity.Yul.World.EffectfulEmitControls.ready
#print axioms Solidity.Yul.World.EffectfulEmitControls.before_view
#print axioms Solidity.Yul.World.EffectfulEmitControls.caller_prefixes
#print axioms Solidity.Yul.World.EffectfulEmitControls.actual
#print axioms Solidity.Yul.World.EffectfulEmitControls.wrong_padding
#print axioms Solidity.Yul.World.EffectfulEmitControls.wrong_view
#print axioms Solidity.Yul.World.EffectfulEmitControls.correct_wrong_patch
#print axioms Solidity.Yul.World.HeapWindowChecks.byte_crosses_word
#print axioms Solidity.Yul.World.HeapWindowChecks.caller_ok
#print axioms Solidity.Yul.World.HeapWindowChecks.string_reads
#print axioms Solidity.Yul.World.HeapWindowChecks.string_crosses_word
#print axioms Solidity.Yul.World.HeapWindowChecks.state_copy
#print axioms Solidity.Yul.World.HeapWindowChecks.real_owner_memOK
#print axioms Solidity.Yul.World.HeapWindowChecks.full_source_prefix
#print axioms Solidity.Yul.World.HeapWindowChecks.source_alias
#print axioms Solidity.Yul.World.HeapWindowChecks.shorter_prefix
#print axioms Solidity.Yul.World.HeapWindowChecks.wrong_destination
#print axioms Solidity.Yul.World.HeapWindowChecks.bad_source_zero
#print axioms Solidity.Yul.World.HeapWindowChecks.beyond_payload_zero
#print axioms Solidity.Yul.World.HeapWindowChecks.exact_end_zero
#print axioms Solidity.Yul.World.HeapWindowChecks.unchanged_string_sides
#print axioms Solidity.Yul.World.HeapWindowChecks.outside_and_other_cell
#print axioms Solidity.Yul.World.HeapWindowChecks.header_and_reserved
#print axioms Solidity.Yul.World.HeapWindowChecks.other_typed_image
#print axioms Solidity.Yul.World.HeapWindowChecks.coupled_all_fields
#print axioms Solidity.Yul.World.HeapWindowChecks.actual_prefix_journals
#print axioms Solidity.Yul.World.HeapWindowChecks.local_rule
#print axioms Solidity.Yul.World.HeapWindowChecks.raw_call_short_output
#print axioms Solidity.Yul.World.HeapWindowChecks.call_source_prefix
#print axioms Solidity.Yul.World.HeapWindowChecks.call_buffer_writeback
#print axioms Solidity.Yul.World.HeapWindowChecks.stale_buffer_refused
#print axioms Solidity.Yul.World.HeapWindowChecks.wrong_selected_object
#print axioms Solidity.Yul.World.HeapWindowChecks.actual_post_placement
#print axioms Solidity.Yul.World.LocalEventBoundary.static_arguments_local
#print axioms Solidity.Yul.World.StaticEventRaw.encoded_log
#print axioms Solidity.Yul.World.StaticEventRaw.encoding_agreement
#print axioms Solidity.Yul.World.StaticEventRaw.encoded_heap
#print axioms Solidity.Yul.World.StaticEventRaw.mixed_source_heap
#print axioms Solidity.Yul.World.StaticEventRaw.loaded
#print axioms Solidity.Yul.World.StaticEventRaw.mixed_view
#print axioms Solidity.Yul.World.StaticEventRaw.wrong_region
#print axioms Solidity.Yul.World.StaticEventRaw.wrong_anonymous_topics
#print axioms Solidity.Yul.World.StaticEventRaw.source_heap_agreement
#print axioms Solidity.Yul.World.StaticEventPortControls.shape
#print axioms Solidity.Yul.World.StaticEventPortControls.fits
#print axioms Solidity.Yul.World.StaticEventPortControls.run_exact
#print axioms Solidity.Yul.World.StaticEventPortControls.static_exact
#print axioms Solidity.Yul.World.StaticEventPortControls.rollback_after
#print axioms Solidity.Yul.World.StaticEventPortControls.ordered
#print axioms Solidity.Yul.World.StaticEventPortControls.enclosing_revert
#print axioms Solidity.Yul.World.MemoryEventControls.typed
#print axioms Solidity.Yul.World.MemoryEventControls.registered
#print axioms Solidity.Yul.World.MemoryEventControls.shape
#print axioms Solidity.Yul.World.MemoryEventControls.local_args
#print axioms Solidity.Yul.World.MemoryEventControls.evaluated
#print axioms Solidity.Yul.World.MemoryEventControls.partition
#print axioms Solidity.Yul.World.MemoryEventControls.data_codec
#print axioms Solidity.Yul.World.MemoryEventControls.full_codec
#print axioms Solidity.Yul.World.MemoryEventSource.actual
#print axioms Solidity.Yul.World.MemoryEventSource.actual_static
#print axioms Solidity.Yul.World.MemoryEventEncoding.encode_exact
#print axioms Solidity.Yul.World.MemoryEventEncoding.overflow_refused
#print axioms Solidity.Yul.World.MemoryEventTopic.word
#print axioms Solidity.Yul.World.MemoryEventTopic.bytes_read
#print axioms Solidity.Yul.World.MemoryEventTopic.string_read
#print axioms Solidity.Yul.World.MemoryEventTopic.bytes_topic
#print axioms Solidity.Yul.World.MemoryEventTopic.string_topic
#print axioms Solidity.Yul.World.MemoryEventTopic.raw_hash
#print axioms Solidity.Yul.World.MemoryEventTopic.bytes_codec
#print axioms Solidity.Yul.World.MemoryEventTopic.string_codec
#print axioms Solidity.Yul.World.MemoryEventTopic.storage_refused
#print axioms Solidity.Yul.World.MemoryEventTopic.dangling_bytes
#print axioms Solidity.Yul.World.MemoryEventPort.source_normal
#print axioms Solidity.Yul.World.MemoryEventPort.source_static
#print axioms Solidity.Yul.World.MemoryEventPort.execute_normal
#print axioms Solidity.Yul.World.MemoryEventPortControls.fits
#print axioms Solidity.Yul.World.MemoryEventPortControls.run_exact
#print axioms Solidity.Yul.World.MemoryEventPortControls.static_exact
#print axioms Solidity.Yul.World.MemoryEventPortControls.wrong_preimage
#print axioms Solidity.Yul.World.MemoryEventPortControls.cross_word
#print axioms Solidity.Yul.World.MemoryEventPortControls.rollback_after
#print axioms Solidity.Yul.World.MemoryEventPortControls.enclosing_revert
#print axioms Solidity.Yul.World.MemoryEventRaw.hash_encoded
#print axioms Solidity.Yul.World.MemoryEventRaw.topic_entry
#print axioms Solidity.Yul.World.MemoryEventRaw.mixed_log
#print axioms Solidity.Yul.World.MemoryEventRaw.source_log_agreement
#print axioms Solidity.Yul.World.MemoryEventWitness.heap_found
#print axioms Solidity.Yul.World.MemoryEventWitness.run_exact
#print axioms Solidity.Yul.World.MemoryEventWitness.actual_args
#print axioms Solidity.Yul.World.MemoryEventWitness.aliases
#print axioms Solidity.Yul.World.MemoryEventWitness.heap_types
#print axioms Solidity.Yul.World.MemoryEventWitness.any_length_topic
#print axioms Solidity.Yul.World.MemoryEventWitness.boundaries
#print axioms Solidity.Yul.World.MemoryEventWitness.dangling
#print axioms Solidity.Yul.World.MemoryEventWitness.caller_memOK
#print axioms Solidity.Yul.World.SourceHeapBoundary.enterInstance_heap
#print axioms Solidity.Yul.World.SourceModifierArgument.argument_run
#print axioms Solidity.Yul.World.SourceModifierArgument.actual
#print axioms Solidity.Yul.World.SourceModifierArgument.entered_timeout
#print axioms Solidity.Yul.World.SourceModifierArgument.invoked
#print axioms Solidity.Yul.World.SourceModifierBoundary.actual
#print axioms Solidity.Yul.World.SourceModifierBoundary.entered_timeout
#print axioms Solidity.Yul.World.SourceModifierCall.actual
#print axioms Solidity.Yul.World.SourceModifierCall.entered_timeout
#print axioms Solidity.Yul.World.SourceModifierFrame.fnLocals_after_arguments
#print axioms Solidity.Yul.World.SourceModifierFrame.argument_halt
