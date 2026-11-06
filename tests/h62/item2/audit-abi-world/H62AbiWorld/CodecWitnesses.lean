import H62AbiWorld.WitnessSchema
import Solidity.Backend.AbiWorld.ErrorRoundtrip

namespace H62.AbiWorld.CodecWitnesses
open Solidity.Backend.AbiWorld

theorem word_length_hypotheses : hypotheses% Solidity.Backend.AbiWorld.word_length :=
  ⟨300,True.intro⟩
#print axioms word_length_hypotheses

theorem padded_length_hypotheses : hypotheses% Solidity.Backend.AbiWorld.padded_length :=
  ⟨[0,255],True.intro⟩
#print axioms padded_length_hypotheses

theorem padded_alignment_hypotheses : hypotheses% Solidity.Backend.AbiWorld.padded_alignment :=
  ⟨[0,255],True.intro⟩
#print axioms padded_alignment_hypotheses

theorem padded_bounds_hypotheses : hypotheses% Solidity.Backend.AbiWorld.padded_bounds :=
  ⟨[0,255],True.intro⟩
#print axioms padded_bounds_hypotheses

theorem padded_payload_hypotheses : hypotheses% Solidity.Backend.AbiWorld.padded_payload :=
  ⟨[0,255],True.intro⟩
#print axioms padded_payload_hypotheses

theorem padded_suffix_hypotheses : hypotheses% Solidity.Backend.AbiWorld.padded_suffix :=
  ⟨[0,255],True.intro⟩
#print axioms padded_suffix_hypotheses

theorem error_tail_hypotheses : hypotheses% Solidity.Backend.AbiWorld.error_tail :=
  ⟨[0,255],True.intro⟩
#print axioms error_tail_hypotheses

theorem error_offset_hypotheses : hypotheses% Solidity.Backend.AbiWorld.error_offset :=
  ⟨[0,255],True.intro⟩
#print axioms error_offset_hypotheses

theorem error_length_word_hypotheses : hypotheses% Solidity.Backend.AbiWorld.error_length_word :=
  ⟨[0,255],True.intro⟩
#print axioms error_length_word_hypotheses

theorem error_payload_hypotheses : hypotheses% Solidity.Backend.AbiWorld.error_payload :=
  ⟨[0,255],True.intro⟩
#print axioms error_payload_hypotheses

theorem packet_prefix_hypotheses : hypotheses% Solidity.Backend.AbiWorld.packet_prefix :=
  ⟨[0,255],[17],True.intro⟩
#print axioms packet_prefix_hypotheses

theorem packet_byte_hypotheses : hypotheses% Solidity.Backend.AbiWorld.packet_byte :=
  ⟨[0,255],[17],0,by decide,True.intro⟩
#print axioms packet_byte_hypotheses

theorem padded_injective_hypotheses : hypotheses% Solidity.Backend.AbiWorld.padded_injective :=
  ⟨[0,255],[0,255],rfl,rfl,True.intro⟩
#print axioms padded_injective_hypotheses

theorem error_body_alignment_hypotheses : hypotheses% Solidity.Backend.AbiWorld.error_body_alignment :=
  ⟨[0,255],True.intro⟩
#print axioms error_body_alignment_hypotheses

theorem numeral_byte_hypotheses : hypotheses% Solidity.Backend.AbiWorld.numeral_byte :=
  ⟨32,300,31,by decide,True.intro⟩
#print axioms numeral_byte_hypotheses

theorem numeral_mod_hypotheses : hypotheses% Solidity.Backend.AbiWorld.numeral_mod :=
  ⟨32,300,True.intro⟩
#print axioms numeral_mod_hypotheses

theorem word_eq_numeral_hypotheses : hypotheses% Solidity.Backend.AbiWorld.word_eq_numeral :=
  ⟨300,True.intro⟩
#print axioms word_eq_numeral_hypotheses

theorem read_word_hypotheses : hypotheses% Solidity.Backend.AbiWorld.read_word :=
  ⟨300,by decide,True.intro⟩
#print axioms read_word_hypotheses

theorem error_roundtrip_hypotheses : hypotheses% Solidity.Backend.AbiWorld.error_roundtrip :=
  ⟨[0,255],by decide,True.intro⟩
#print axioms error_roundtrip_hypotheses

end H62.AbiWorld.CodecWitnesses
