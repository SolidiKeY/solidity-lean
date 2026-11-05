import Solidity.Frontend.LiteralGrammarH28.BoundaryControls

/-! # Exact quote/scanner signatures and axiom reports -/
namespace Solidity.Frontend.LiteralGrammarH28

#check @quotedBody_complete
#print axioms quotedBody_complete
#check @quotedBody_sound
#print axioms quotedBody_sound
#check @quotedBody_iff
#print axioms quotedBody_iff
#check @plainString_complete
#print axioms plainString_complete
#check @plainString_sound
#print axioms plainString_sound
#check @plainString_iff
#print axioms plainString_iff
#check @quoteBytes_quoted
#print axioms quoteBytes_quoted
#check @encodePlain_roundtrip
#print axioms encodePlain_roundtrip
#check @quoteBytes_length
#print axioms quoteBytes_length
#check @encodePlain_length
#print axioms encodePlain_length
#check @Scan.input_nonempty
#print axioms Scan.input_nonempty
#check @Scan.partition
#print axioms Scan.partition
#check @untilQuote_complete
#print axioms untilQuote_complete
#check @untilQuote_sound
#print axioms untilQuote_sound
#check @untilQuote_iff
#print axioms untilQuote_iff
#check @Scan.closer
#print axioms Scan.closer
#check @Scan.append_suffix
#print axioms Scan.append_suffix
#check @untilQuote_append_suffix
#print axioms untilQuote_append_suffix
#check @printable_safe
#print axioms printable_safe
#check @unicode_safe
#print axioms unicode_safe
#check @hexDigit_safe
#print axioms hexDigit_safe
#check @Body.scan
#print axioms Body.scan
#check @body_scan_value
#print axioms body_scan_value
#check @HexBody.scan
#print axioms HexBody.scan
#check @hex_scan_value
#print axioms hex_scan_value
#check @encodePlain_scan
#print axioms encodePlain_scan
#check @quoteControls_pass
#print axioms quoteControls_pass
#check @scanControls_pass
#print axioms scanControls_pass
#check @plainControls_pass
#print axioms plainControls_pass
#check @quotedGrammar_inhabited
#print axioms quotedGrammar_inhabited
#check @plainGrammar_inhabited
#print axioms plainGrammar_inhabited
#check @scannerGrammar_inhabited
#print axioms scannerGrammar_inhabited
#check @scannerGrammar_empty_refused
#print axioms scannerGrammar_empty_refused
#check @scanner_nonliteral_boundary
#print axioms scanner_nonliteral_boundary

end Solidity.Frontend.LiteralGrammarH28
