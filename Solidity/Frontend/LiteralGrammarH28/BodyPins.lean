import Solidity.Frontend.LiteralGrammarH28.BodyControls

/-! # Body theorem signatures and transitive axiom reports -/
namespace Solidity.Frontend.LiteralGrammarH28

#check @escape_complete
#print axioms escape_complete
#check @escape_sound
#print axioms escape_sound
#check @body_complete
#print axioms body_complete
#check @Body.toStrBody
#print axioms Body.toStrBody
#check @body_sound
#print axioms body_sound
#check @body_iff
#print axioms body_iff
#check @Body.deterministic
#print axioms Body.deterministic
#check @body_none_iff
#print axioms body_none_iff
#check @utf8_length
#print axioms utf8_length
#check @utf8_length_le
#print axioms utf8_length_le
#check @Escape.length_le
#print axioms Escape.length_le
#check @Body.length_le
#print axioms Body.length_le
#check @encodeBody_grammar
#print axioms encodeBody_grammar
#check @encodeBody_roundtrip
#print axioms encodeBody_roundtrip
#check @encodeBody_length
#print axioms encodeBody_length
#check @bodyControls_pass
#print axioms bodyControls_pass
#check @bodyGrammar_inhabited
#print axioms bodyGrammar_inhabited
#check @oldStrBody_overlap
#print axioms oldStrBody_overlap
#check @bodyCRLF_empty
#print axioms bodyCRLF_empty
#check @bodyCRLF_no_alternate
#print axioms bodyCRLF_no_alternate
#check @bodyEncoding_control
#print axioms bodyEncoding_control

end Solidity.Frontend.LiteralGrammarH28
