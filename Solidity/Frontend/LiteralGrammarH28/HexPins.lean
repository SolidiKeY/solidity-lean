import Solidity.Frontend.LiteralGrammarH28.HexControls

/-! # Exact hex theorem signatures and transitive axiom reports -/
namespace Solidity.Frontend.LiteralGrammarH28

#check @hexBody_complete
#print axioms hexBody_complete
#check @hexBody_sound
#print axioms hexBody_sound
#check @hexBody_iff
#print axioms hexBody_iff
#check @HexBody.deterministic
#print axioms HexBody.deterministic
#check @hexBody_none_iff
#print axioms hexBody_none_iff
#check @HexBody.length_bounds
#print axioms HexBody.length_bounds
#check @byteEncoding_table
#print axioms byteEncoding_table
#check @byteEncoding_facts
#print axioms byteEncoding_facts
#check @encodeHex_grammar
#print axioms encodeHex_grammar
#check @encodeHex_roundtrip
#print axioms encodeHex_roundtrip
#check @encodeHex_length
#print axioms encodeHex_length
#check @hexControls_pass
#print axioms hexControls_pass
#check @hexGrammar_inhabited
#print axioms hexGrammar_inhabited
#check @hexGrammar_no_trailing
#print axioms hexGrammar_no_trailing
#check @hexEncoding_control
#print axioms hexEncoding_control

end Solidity.Frontend.LiteralGrammarH28
