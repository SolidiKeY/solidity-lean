import SolidityBridge.RoadmapV15.P10.ByteObservationControls
import GenericP10.ByteControls

/-! Kernel equality of complete original propositions, including all positive,
negative, refusal, resource-order and whole-state observations. The independent
candidate execution proofs consume native semantics, not the original proofs.
`proposition` merely selects a proof term's type for this comparison. -/
namespace GenericP10.Correspondence
private def proposition {P : Prop} (_proof : P) : Prop := P

theorem first_byte :
    proposition (@SolidityBridge.RoadmapV15.P10.ByteObservationControls.first_byte) =
      proposition (@GenericP10.ByteControls.first_byte) := rfl

theorem second_byte :
    proposition (@SolidityBridge.RoadmapV15.P10.ByteObservationControls.second_byte) =
      proposition (@GenericP10.ByteControls.second_byte) := rfl

theorem middle_zero :
    proposition (@SolidityBridge.RoadmapV15.P10.ByteObservationControls.middle_zero) =
      proposition (@GenericP10.ByteControls.middle_zero) := rfl

theorem penultimate_byte :
    proposition (@SolidityBridge.RoadmapV15.P10.ByteObservationControls.penultimate_byte) =
      proposition (@GenericP10.ByteControls.penultimate_byte) := rfl

theorem last_byte :
    proposition (@SolidityBridge.RoadmapV15.P10.ByteObservationControls.last_byte) =
      proposition (@GenericP10.ByteControls.last_byte) := rfl

theorem outside_word :
    proposition (@SolidityBridge.RoadmapV15.P10.ByteObservationControls.outside_word) =
      proposition (@GenericP10.ByteControls.outside_word) := rfl

theorem maximum_index :
    proposition (@SolidityBridge.RoadmapV15.P10.ByteObservationControls.maximum_index) =
      proposition (@GenericP10.ByteControls.maximum_index) := rfl

theorem zero_word :
    proposition (@SolidityBridge.RoadmapV15.P10.ByteObservationControls.zero_word) =
      proposition (@GenericP10.ByteControls.zero_word) := rfl

theorem maximum_word :
    proposition (@SolidityBridge.RoadmapV15.P10.ByteObservationControls.maximum_word) =
      proposition (@GenericP10.ByteControls.maximum_word) := rfl

theorem ordered_code :
    proposition (@SolidityBridge.RoadmapV15.P10.ByteObservationControls.ordered_code) =
      proposition (@GenericP10.ByteControls.ordered_code) := rfl

theorem ordered_word_bytes :
    proposition (@SolidityBridge.RoadmapV15.P10.ByteObservationControls.ordered_word_bytes) =
      proposition (@GenericP10.ByteControls.ordered_word_bytes) := rfl

theorem wrong_endian :
    proposition (@SolidityBridge.RoadmapV15.P10.ByteObservationControls.wrong_endian) =
      proposition (@GenericP10.ByteControls.wrong_endian) := rfl

theorem typed_image_client :
    proposition (@SolidityBridge.RoadmapV15.P10.ByteObservationControls.typed_image_client) =
      proposition (@GenericP10.ByteControls.typed_image_client) := rfl

theorem stack_boundary :
    proposition (@SolidityBridge.RoadmapV15.P10.ByteObservationControls.stack_boundary) =
      proposition (@GenericP10.ByteControls.stack_boundary) := rfl

theorem gas_refusal :
    proposition (@SolidityBridge.RoadmapV15.P10.ByteObservationControls.gas_refusal) =
      proposition (@GenericP10.ByteControls.gas_refusal) := rfl

theorem fuel_precedes_gas :
    proposition (@SolidityBridge.RoadmapV15.P10.ByteObservationControls.fuel_precedes_gas) =
      proposition (@GenericP10.ByteControls.fuel_precedes_gas) := rfl

theorem gas_precedes_stack :
    proposition (@SolidityBridge.RoadmapV15.P10.ByteObservationControls.gas_precedes_stack) =
      proposition (@GenericP10.ByteControls.gas_precedes_stack) := rfl

theorem stack_refusal :
    proposition (@SolidityBridge.RoadmapV15.P10.ByteObservationControls.stack_refusal) =
      proposition (@GenericP10.ByteControls.stack_refusal) := rfl

theorem capacity_refusal :
    proposition (@SolidityBridge.RoadmapV15.P10.ByteObservationControls.capacity_refusal) =
      proposition (@GenericP10.ByteControls.capacity_refusal) := rfl

theorem image_index_requires_bound :
    proposition (@SolidityBridge.RoadmapV15.P10.ByteObservationControls.image_index_requires_bound) =
      proposition (@GenericP10.ByteControls.image_index_requires_bound) := rfl

theorem scalar_refusal_control :
    proposition (@SolidityBridge.RoadmapV15.P10.ByteObservationControls.scalar_refusal_control) =
      proposition (@GenericP10.ByteControls.scalar_refusal_control) := rfl

#print axioms first_byte
#print axioms second_byte
#print axioms middle_zero
#print axioms penultimate_byte
#print axioms last_byte
#print axioms outside_word
#print axioms maximum_index
#print axioms zero_word
#print axioms maximum_word
#print axioms ordered_code
#print axioms ordered_word_bytes
#print axioms wrong_endian
#print axioms typed_image_client
#print axioms stack_boundary
#print axioms gas_refusal
#print axioms fuel_precedes_gas
#print axioms gas_precedes_stack
#print axioms stack_refusal
#print axioms capacity_refusal
#print axioms image_index_requires_bound
#print axioms scalar_refusal_control
end GenericP10.Correspondence
