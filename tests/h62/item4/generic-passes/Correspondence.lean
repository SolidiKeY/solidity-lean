import Solidity.Backend.Passes.AssignmentAdditionControls
import Solidity.Backend.Passes.AssignmentSubtractionControls
import Solidity.Backend.Passes.AssignmentMultiplicationControls
namespace Solidity.Backend.Passes.H62Correspondence
theorem addition_initial : type_of% Solidity.Backend.Passes.AssignmentAdditionPass.Controls.initial :=
  Solidity.Backend.Passes.AssignmentAdditionPass.Controls.initial
theorem addition_input : type_of% Solidity.Backend.Passes.AssignmentAdditionPass.Controls.input :=
  Solidity.Backend.Passes.AssignmentAdditionPass.Controls.input
theorem addition_family : type_of% Solidity.Backend.Passes.AssignmentAdditionPass.Controls.family :=
  Solidity.Backend.Passes.AssignmentAdditionPass.Controls.family
theorem addition_prefix_run : type_of% Solidity.Backend.Passes.AssignmentAdditionPass.Controls.prefix_run :=
  Solidity.Backend.Passes.AssignmentAdditionPass.Controls.prefix_run
theorem addition_emitted : type_of% Solidity.Backend.Passes.AssignmentAdditionPass.Controls.emitted :=
  Solidity.Backend.Passes.AssignmentAdditionPass.Controls.emitted
theorem addition_source_execution : type_of% Solidity.Backend.Passes.AssignmentAdditionPass.Controls.source_execution :=
  Solidity.Backend.Passes.AssignmentAdditionPass.Controls.source_execution
theorem addition_complete_observations : type_of% Solidity.Backend.Passes.AssignmentAdditionPass.Controls.complete_observations :=
  Solidity.Backend.Passes.AssignmentAdditionPass.Controls.complete_observations
theorem addition_different_pipelines : type_of% Solidity.Backend.Passes.AssignmentAdditionPass.Controls.different_pipelines :=
  Solidity.Backend.Passes.AssignmentAdditionPass.Controls.different_pipelines
theorem addition_stale_rhs_refused : type_of% Solidity.Backend.Passes.AssignmentAdditionPass.Controls.stale_rhs_refused :=
  Solidity.Backend.Passes.AssignmentAdditionPass.Controls.stale_rhs_refused
theorem addition_short_frame_refused : type_of% Solidity.Backend.Passes.AssignmentAdditionPass.Controls.short_frame_refused :=
  Solidity.Backend.Passes.AssignmentAdditionPass.Controls.short_frame_refused
theorem addition_corrupted_saved_tail : type_of% Solidity.Backend.Passes.AssignmentAdditionPass.Controls.corrupted_saved_tail :=
  Solidity.Backend.Passes.AssignmentAdditionPass.Controls.corrupted_saved_tail
theorem subtraction_initial : type_of% Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.initial :=
  Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.initial
theorem subtraction_input : type_of% Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.input :=
  Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.input
theorem subtraction_prefix_run : type_of% Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.prefix_run :=
  Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.prefix_run
theorem subtraction_emitted : type_of% Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.emitted :=
  Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.emitted
theorem subtraction_source_execution : type_of% Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.source_execution :=
  Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.source_execution
theorem subtraction_complete_observations : type_of% Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.complete_observations :=
  Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.complete_observations
theorem subtraction_different_pipelines : type_of% Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.different_pipelines :=
  Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.different_pipelines
theorem subtraction_stale_rhs_refused : type_of% Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.stale_rhs_refused :=
  Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.stale_rhs_refused
theorem subtraction_short_frame_refused : type_of% Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.short_frame_refused :=
  Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.short_frame_refused
theorem subtraction_reversed_source : type_of% Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.reversed_source :=
  Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.reversed_source
theorem subtraction_wrong_order_reverts : type_of% Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.wrong_order_reverts :=
  Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.wrong_order_reverts
theorem subtraction_corrupted_saved_tail : type_of% Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.corrupted_saved_tail :=
  Solidity.Backend.Passes.AssignmentSubtractionPass.Controls.corrupted_saved_tail
theorem multiplication_initial : type_of% Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.initial :=
  Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.initial
theorem multiplication_input : type_of% Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.input :=
  Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.input
theorem multiplication_family : type_of% Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.family :=
  Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.family
theorem multiplication_prefix_run : type_of% Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.prefix_run :=
  Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.prefix_run
theorem multiplication_emitted : type_of% Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.emitted :=
  Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.emitted
theorem multiplication_source_execution : type_of% Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.source_execution :=
  Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.source_execution
theorem multiplication_complete_observations : type_of% Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.complete_observations :=
  Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.complete_observations
theorem multiplication_different_pipelines : type_of% Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.different_pipelines :=
  Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.different_pipelines
theorem multiplication_stale_rhs_refused : type_of% Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.stale_rhs_refused :=
  Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.stale_rhs_refused
theorem multiplication_short_frame_refused : type_of% Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.short_frame_refused :=
  Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.short_frame_refused
theorem multiplication_corrupted_saved_tail : type_of% Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.corrupted_saved_tail :=
  Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.corrupted_saved_tail
theorem multiplication_actual_unmasked : type_of% Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.actual_unmasked :=
  Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.actual_unmasked
theorem multiplication_unmasked_differs : type_of% Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.unmasked_differs :=
  Solidity.Backend.Passes.AssignmentMultiplicationPass.Controls.unmasked_differs
end Solidity.Backend.Passes.H62Correspondence
