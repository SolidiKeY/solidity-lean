import H62AbiWorld.WitnessSchema
import Solidity.Backend.AbiWorld.ReturnWordTransportControls
import Solidity.Backend.AbiWorld.ErrorOffsetWindowControls
import Solidity.Backend.AbiWorld.PanicCallFrameControls

namespace H62.AbiWorld.WindowWitnesses
open Solidity Solidity.Backend.AbiWorld Solidity.Backend.Failure
abbrev machine := ErrorReadWindowControls.machine
abbrev u : ReturnWordTransport.UInt := LibraryResultPacket.uint ⟨300,by decide⟩
local instance (a : Nat) (bs : List UInt8) : Decidable (Fits a bs) :=
  inferInstanceAs (Decidable (a<wordLimit ∧ bs.length<wordLimit ∧ a+bs.length≤wordLimit))

theorem ErrorReadWindow_unpadded_hypotheses : hypotheses% Solidity.Backend.AbiWorld.ErrorReadWindow.unpadded :=
  ⟨[0,255],[17],by decide,True.intro⟩
#print axioms ErrorReadWindow_unpadded_hypotheses

theorem ErrorReadWindow_source_prefix_hypotheses : hypotheses% Solidity.Backend.AbiWorld.ErrorReadWindow.source_prefix :=
  ⟨[0,255],True.intro⟩
#print axioms ErrorReadWindow_source_prefix_hypotheses

theorem ErrorReadWindow_prefix_readback_hypotheses : hypotheses% Solidity.Backend.AbiWorld.ErrorReadWindow.prefix_readback :=
  ⟨[0,255],[17],by decide,True.intro⟩
#print axioms ErrorReadWindow_prefix_readback_hypotheses

theorem ErrorReadWindow_emitted_hypotheses : hypotheses% Solidity.Backend.AbiWorld.ErrorReadWindow.emitted :=
  ⟨[0,255],[17],8,[],machine,by decide,by decide,True.intro⟩
#print axioms ErrorReadWindow_emitted_hypotheses

theorem ErrorOffsetWindow_gap_readback_hypotheses : hypotheses% Solidity.Backend.AbiWorld.ErrorOffsetWindow.gap_readback :=
  ⟨[165],[0,255],[17],by decide,by decide,True.intro⟩
#print axioms ErrorOffsetWindow_gap_readback_hypotheses

theorem ErrorOffsetWindow_zero_offset_hypotheses : hypotheses% Solidity.Backend.AbiWorld.ErrorOffsetWindow.zero_offset :=
  ⟨[17],True.intro⟩
#print axioms ErrorOffsetWindow_zero_offset_hypotheses

theorem ErrorOffsetWindow_emitted_hypotheses : hypotheses% Solidity.Backend.AbiWorld.ErrorOffsetWindow.emitted :=
  ⟨[165],[0,255],[17],8,[],machine,by decide,by decide,True.intro⟩
#print axioms ErrorOffsetWindow_emitted_hypotheses

theorem PanicReadWindow_decode_hypotheses : hypotheses% Solidity.Backend.AbiWorld.PanicReadWindow.decode :=
  ⟨300,by decide,[17],True.intro⟩
#print axioms PanicReadWindow_decode_hypotheses

theorem PanicReadWindow_error_reject_hypotheses : hypotheses% Solidity.Backend.AbiWorld.PanicReadWindow.error_reject :=
  ⟨300,[17],True.intro⟩
#print axioms PanicReadWindow_error_reject_hypotheses

theorem PanicReadWindow_emitted_hypotheses : hypotheses% Solidity.Backend.AbiWorld.PanicReadWindow.emitted :=
  ⟨⟨300,by decide⟩,8,[],machine,by decide,by decide,True.intro⟩
#print axioms PanicReadWindow_emitted_hypotheses

theorem LibraryResultPacket_word_bytes_hypotheses : hypotheses% Solidity.Backend.AbiWorld.LibraryResultPacket.word_bytes :=
  ⟨300,True.intro⟩
#print axioms LibraryResultPacket_word_bytes_hypotheses

theorem LibraryResultPacket_encoded_values_hypotheses : hypotheses% Solidity.Backend.AbiWorld.LibraryResultPacket.encoded_values :=
  ⟨⟨300,by decide⟩,[0,255],True.intro⟩
#print axioms LibraryResultPacket_encoded_values_hypotheses

theorem LibraryResultPacket_length_hypotheses : hypotheses% Solidity.Backend.AbiWorld.LibraryResultPacket.length :=
  ⟨⟨300,by decide⟩,[0,255],True.intro⟩
#print axioms LibraryResultPacket_length_hypotheses

theorem LibraryResultPacket_marker_hypotheses : hypotheses% Solidity.Backend.AbiWorld.LibraryResultPacket.marker :=
  ⟨⟨300,by decide⟩,[0,255],True.intro⟩
#print axioms LibraryResultPacket_marker_hypotheses

theorem LibraryResultPacket_offset_hypotheses : hypotheses% Solidity.Backend.AbiWorld.LibraryResultPacket.offset :=
  ⟨⟨300,by decide⟩,[0,255],True.intro⟩
#print axioms LibraryResultPacket_offset_hypotheses

theorem LibraryResultPacket_payload_hypotheses : hypotheses% Solidity.Backend.AbiWorld.LibraryResultPacket.payload :=
  ⟨⟨300,by decide⟩,[0,255],True.intro⟩
#print axioms LibraryResultPacket_payload_hypotheses

theorem ReturnWordTransport_bytes_word_hypotheses : hypotheses% Solidity.Backend.AbiWorld.ReturnWordTransport.bytes_word :=
  ⟨[17],[34],300,True.intro⟩
#print axioms ReturnWordTransport_bytes_word_hypotheses

theorem ReturnWordTransport_load_word_hypotheses : hypotheses% Solidity.Backend.AbiWorld.ReturnWordTransport.load_word :=
  ⟨[17],[34],u,True.intro⟩
#print axioms ReturnWordTransport_load_word_hypotheses

theorem ReturnWordTransport_static_go_hypotheses : hypotheses% Solidity.Backend.AbiWorld.ReturnWordTransport.static_go :=
  ⟨[u],32,True.intro⟩
#print axioms ReturnWordTransport_static_go_hypotheses

theorem ReturnWordTransport_encoded_values_hypotheses : hypotheses% Solidity.Backend.AbiWorld.ReturnWordTransport.encoded_values :=
  ⟨[u],True.intro⟩
#print axioms ReturnWordTransport_encoded_values_hypotheses

theorem ReturnWordTransport_byte_length_hypotheses : hypotheses% Solidity.Backend.AbiWorld.ReturnWordTransport.byte_length :=
  ⟨[u],True.intro⟩
#print axioms ReturnWordTransport_byte_length_hypotheses

theorem ReturnWordTransport_wordAt_window_hypotheses : hypotheses% Solidity.Backend.AbiWorld.ReturnWordTransport.wordAt_window :=
  ⟨[17],[34],u,True.intro⟩
#print axioms ReturnWordTransport_wordAt_window_hypotheses

theorem ReturnWordTransport_wordAt_index_hypotheses : hypotheses% Solidity.Backend.AbiWorld.ReturnWordTransport.wordAt_index :=
  ⟨[u],[17],0,by decide,True.intro⟩
#print axioms ReturnWordTransport_wordAt_index_hypotheses

theorem ReturnWordTransport_words_readback_hypotheses : hypotheses% Solidity.Backend.AbiWorld.ReturnWordTransport.words_readback :=
  ⟨[u],[17],True.intro⟩
#print axioms ReturnWordTransport_words_readback_hypotheses

theorem ReturnWordTransport_decode_transport_hypotheses : hypotheses% Solidity.Backend.AbiWorld.ReturnWordTransport.decode_transport :=
  ⟨ReturnWordTransportControls.contract,[],[.val .uint,.val .uint,.val .uint],ReturnWordTransportControls.rets,ReturnWordTransportControls.xs,rfl,[17],True.intro⟩
#print axioms ReturnWordTransport_decode_transport_hypotheses

theorem ReturnWordTransport_truncated_hypotheses : hypotheses% Solidity.Backend.AbiWorld.ReturnWordTransport.truncated :=
  by
  refine ⟨[u], ?_⟩
  refine ⟨?_, True.intro⟩
  intro h
  cases h
#print axioms ReturnWordTransport_truncated_hypotheses

theorem ReturnWordTransport_emitted_hypotheses : hypotheses% Solidity.Backend.AbiWorld.ReturnWordTransport.emitted :=
  ⟨[u],8,[],machine,by decide,by decide,True.intro⟩
#print axioms ReturnWordTransport_emitted_hypotheses

end H62.AbiWorld.WindowWitnesses
