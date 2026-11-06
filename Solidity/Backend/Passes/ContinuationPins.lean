import Solidity.Backend.Passes.CaptureCases
import Solidity.Backend.Passes.AllocatingCapture
import Solidity.Backend.Passes.TailDivergence

/-! Exact axiom pins for saved-tail and capture continuation proofs. -/
namespace Solidity.Backend.Passes
/-- info: 'Solidity.Backend.Passes.primitive_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms primitive_tail
/-- info: 'Solidity.Backend.Passes.instr_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms instr_tail
/-- info: 'Solidity.Backend.Passes.loop_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loop_tail
/-- info: 'Solidity.Backend.Passes.exec_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exec_tail
/-- info: 'Solidity.Backend.Passes.run_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_tail
/-- info: 'Solidity.Backend.Passes.compilation_tail_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms compilation_tail_exact
/-- info: 'Solidity.Backend.Passes.compilation_success_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms compilation_success_shared
/-- info: 'Solidity.Backend.Passes.compilation_two_tails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms compilation_two_tails
/-- info: 'Solidity.Backend.Passes.raw_fault_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms raw_fault_counterexample
/-- info: 'Solidity.Backend.Passes.mapped_output_stack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mapped_output_stack
/-- info: 'Solidity.Backend.Passes.compilation_success_shared_mapped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms compilation_success_shared_mapped
/-- info: 'Solidity.Backend.Passes.TailControls.allocating_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms TailControls.allocating_shared
/-- info: 'Solidity.Backend.Passes.TailControls.pipeline_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms TailControls.pipeline_shared
/-- info: 'Solidity.Backend.Passes.TailControls.reached_failure_all_tails' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms TailControls.reached_failure_all_tails
/-- info: 'Solidity.Backend.Passes.TailControls.corruption' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms TailControls.corruption
/-- info: 'Solidity.Backend.Passes.TailControls.loop_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms TailControls.loop_reaches
/-- info: 'Solidity.Backend.Passes.TailControls.loop_all_tails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms TailControls.loop_all_tails
/-- info: 'Solidity.Backend.Passes.TailDivergence.source_diverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms TailDivergence.source_diverges
/-- info: 'Solidity.Backend.Passes.TailDivergence.diverges_all_tails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms TailDivergence.diverges_all_tails
/-- info: 'Solidity.Backend.Passes.TailDivergence.actual_recognizer_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms TailDivergence.actual_recognizer_accepts
/-- info: 'Solidity.Backend.Passes.capture_local_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms capture_local_frame
/-- info: 'Solidity.Backend.Passes.capture_memory_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms capture_memory_frame
/-- info: 'Solidity.Backend.Passes.capture_field_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms capture_field_frame
/-- info: 'Solidity.Backend.Passes.capture_then_alias_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms capture_then_alias_frame
/-- info: 'Solidity.Backend.Passes.capture_then_value_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms capture_then_value_frame
/-- info: 'Solidity.Backend.Passes.capture_local_alias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms capture_local_alias
/-- info: 'Solidity.Backend.Passes.capture_memory_alias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms capture_memory_alias
/-- info: 'Solidity.Backend.Passes.capture_field_alias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms capture_field_alias
/-- info: 'Solidity.Backend.Passes.CaptureControls.actual_capture_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CaptureControls.actual_capture_code
/-- info: 'Solidity.Backend.Passes.CaptureControls.source_capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CaptureControls.source_capture
/-- info: 'Solidity.Backend.Passes.CaptureControls.source_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CaptureControls.source_success
/-- info: 'Solidity.Backend.Passes.CaptureControls.fresh_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CaptureControls.fresh_reaches
/-- info: 'Solidity.Backend.Passes.CaptureControls.generic_capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CaptureControls.generic_capture
/-- info: 'Solidity.Backend.Passes.CaptureControls.generic_alias_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms CaptureControls.generic_alias_context
/-- info: 'Solidity.Backend.Passes.CaptureControls.generic_value_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms CaptureControls.generic_value_context
/-- info: 'Solidity.Backend.Passes.CaptureControls.source_aliases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CaptureControls.source_aliases
/-- info: 'Solidity.Backend.Passes.CaptureControls.shared_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CaptureControls.shared_output
/-- info: 'Solidity.Backend.Passes.CaptureControls.ordered_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CaptureControls.ordered_values
/-- info: 'Solidity.Backend.Passes.CaptureControls.after_effect_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CaptureControls.after_effect_read
/-- info: 'Solidity.Backend.Passes.CaptureControls.wrong_recapture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CaptureControls.wrong_recapture
/-- info: 'Solidity.Backend.Passes.CaptureControls.wrong_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CaptureControls.wrong_order
/-- info: 'Solidity.Backend.Passes.CaptureControls.source_failure_after_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms CaptureControls.source_failure_after_effect
/-- info: 'Solidity.Backend.Passes.CaptureControls.target_effect_before_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms CaptureControls.target_effect_before_failure
/-- info: 'Solidity.Backend.Passes.CaptureControls.failure_all_tails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CaptureControls.failure_all_tails
/-- info: 'Solidity.Backend.Passes.CaptureControls.stack_corruption' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CaptureControls.stack_corruption
/-- info: 'Solidity.Backend.Passes.AllocatingCapture.actual_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AllocatingCapture.actual_link
/-- info: 'Solidity.Backend.Passes.AllocatingCapture.fresh_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AllocatingCapture.fresh_source
/-- info: 'Solidity.Backend.Passes.AllocatingCapture.shared_maps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AllocatingCapture.shared_maps
/-- info: 'Solidity.Backend.Passes.AllocatingCapture.ordered_results' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AllocatingCapture.ordered_results
/-- info: 'Solidity.Backend.Passes.CaptureCases.Local.generic_instance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CaptureCases.Local.generic_instance
/-- info: 'Solidity.Backend.Passes.CaptureCases.Local.self_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CaptureCases.Local.self_source
/-- info: 'Solidity.Backend.Passes.CaptureCases.Local.deferred_store_matters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms CaptureCases.Local.deferred_store_matters
/-- info: 'Solidity.Backend.Passes.CaptureCases.Field.inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CaptureCases.Field.inhabited
end Solidity.Backend.Passes
