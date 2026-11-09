import Solidity.Frontend.LiteralGrammarH28.Body
import Solidity.Frontend.LiteralGrammarH28.BodyControls
import Solidity.Frontend.LiteralGrammarH28.BoundaryControls
import Solidity.Frontend.LiteralGrammarH28.Classification
import Solidity.Frontend.LiteralGrammarH28.EncodingValue
import Solidity.Frontend.LiteralGrammarH28.FragmentCompleteness
import Solidity.Frontend.LiteralGrammarH28.Fragments
import Solidity.Frontend.LiteralGrammarH28.FullControls
import Solidity.Frontend.LiteralGrammarH28.Global
import Solidity.Frontend.LiteralGrammarH28.Hex
import Solidity.Frontend.LiteralGrammarH28.HexControls
import Solidity.Frontend.LiteralGrammarH28.HexEncoding
import Solidity.Frontend.LiteralGrammarH28.Lengths
import Solidity.Frontend.LiteralGrammarH28.ModeGrammar
import Solidity.Frontend.LiteralGrammarH28.Quoted
import Solidity.Frontend.LiteralGrammarH28.Roundtrips
import Solidity.Frontend.LiteralGrammarH28.Scanner
import Solidity.Frontend.LiteralGrammarH28.Split
import Solidity.Frontend.LiteralGrammarH28.TaggedEncoding
import Solidity.Frontend.LiteralGrammarH28.Utf8Shape
import Solidity.Frontend.LiteralGrammarH28.WordTable

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
#check @quoted_plain_eq
#print axioms quoted_plain_eq
#check @quote_punct_none
#print axioms quote_punct_none
#check @solTok_plain_eq
#print axioms solTok_plain_eq
#check @yulTok_plain_eq
#print axioms yulTok_plain_eq
#check @solTok_hex_eq
#print axioms solTok_hex_eq
#check @yulTok_hex_eq
#print axioms yulTok_hex_eq
#check @solTok_unicode_eq
#print axioms solTok_unicode_eq
#check @option_map_same_iff
#print axioms option_map_same_iff
#check @solTok_plain_iff
#print axioms solTok_plain_iff
#check @solTok_hex_iff
#print axioms solTok_hex_iff
#check @solTok_unicode_iff
#print axioms solTok_unicode_iff
#check @Plain.solTok
#print axioms Plain.solTok
#check @HexLiteral.solTok
#print axioms HexLiteral.solTok
#check @UnicodeLiteral.solTok
#print axioms UnicodeLiteral.solTok
#check @quote_trivia_none
#print axioms quote_trivia_none
#check @classify_sol_plain
#print axioms classify_sol_plain
#check @classify_yul_plain
#print axioms classify_yul_plain
#check @classify_sol_hex
#print axioms classify_sol_hex
#check @classify_yul_hex
#print axioms classify_yul_hex
#check @classify_sol_unicode
#print axioms classify_sol_unicode
#check @classify_yul_unicode_refused
#print axioms classify_yul_unicode_refused
#check @classify_asm_double
#print axioms classify_asm_double
#check @classify_asm_single_refused
#print axioms classify_asm_single_refused
#check @codepoint_complete
#print axioms codepoint_complete
#check @codepoint_sound
#print axioms codepoint_sound
#check @codepoint_iff
#print axioms codepoint_iff
#check @codepoint_nonempty
#print axioms codepoint_nonempty
#check @hexVal_lt16
#print axioms hexVal_lt16
#check @hexPair_lt256
#print axioms hexPair_lt256
#check @hexPair_exactNat
#print axioms hexPair_exactNat
#check @hexQuad_lt65536
#print axioms hexQuad_lt65536
#check @Body.uni_value
#print axioms Body.uni_value
#check @fragments_tagged_iff
#print axioms fragments_tagged_iff
#check @fragments_solTok_iff
#print axioms fragments_solTok_iff
#check @fragments_classify_sol_iff
#print axioms fragments_classify_sol_iff
#check @fragments_yul_plain_iff
#print axioms fragments_yul_plain_iff
#check @fragments_yul_hex_iff
#print axioms fragments_yul_hex_iff
#check @encoded_hex_fragments
#print axioms encoded_hex_fragments
#check @encoded_unicode_fragments
#print axioms encoded_unicode_fragments
#check @encoded_hex_fragments_roundtrip
#print axioms encoded_hex_fragments_roundtrip
#check @encoded_unicode_fragments_roundtrip
#print axioms encoded_unicode_fragments_roundtrip
#check @Fragments.plain_split_head
#print axioms Fragments.plain_split_head
#check @Fragments.hex_split_head
#print axioms Fragments.hex_split_head
#check @Fragments.unicode_split_head
#print axioms Fragments.unicode_split_head
#check @encoded_hex_fragments_value
#print axioms encoded_hex_fragments_value
#check @encoded_unicode_fragments_value
#print axioms encoded_unicode_fragments_value
#check @FragmentValue.byteLength
#print axioms FragmentValue.byteLength
#check @fragments_mapM_iff
#print axioms fragments_mapM_iff
#check @Fragments.append
#print axioms Fragments.append
#check @FragmentValue.append
#print axioms FragmentValue.append
#check @fragments_none_iff
#print axioms fragments_none_iff
#check @Fragments.classified
#print axioms Fragments.classified
#check @Fragments.plain_classified
#print axioms Fragments.plain_classified
#check @Fragments.hex_classified
#print axioms Fragments.hex_classified
#check @Fragments.unicode_classified
#print axioms Fragments.unicode_classified
#check @encoded_fragments_grammar
#print axioms encoded_fragments_grammar
#check @encoded_fragments_roundtrip
#print axioms encoded_fragments_roundtrip
#check @encoded_fragments_value
#print axioms encoded_fragments_value
#check @Plain.split
#print axioms Plain.split
#check @Fragments.split_head
#print axioms Fragments.split_head
#check @fullControls_pass
#print axioms fullControls_pass
#check @assemblyGrammar_inhabited_empty_value
#print axioms assemblyGrammar_inhabited_empty_value
#check @unicodeGrammar_inhabited_invalid_bytes
#print axioms unicodeGrammar_inhabited_invalid_bytes
#check @codepoint_surrogate_control
#print axioms codepoint_surrogate_control
#check @plainFragments_inhabited
#print axioms plainFragments_inhabited
#check @hexFragments_inhabited
#print axioms hexFragments_inhabited
#check @unicodeFragments_inhabited
#print axioms unicodeFragments_inhabited
#check @fragments_bad_second_refused
#print axioms fragments_bad_second_refused
#check @cross_fragment_CR_LF_control
#print axioms cross_fragment_CR_LF_control
#check @mixedModeSequence_inhabited
#print axioms mixedModeSequence_inhabited
#check @yulUnicodeMode_refused
#print axioms yulUnicodeMode_refused
#check @solWordTable_no_literal
#print axioms solWordTable_no_literal
#check @solWord_no_literal
#print axioms solWord_no_literal
#check @solTok_literal_sound
#print axioms solTok_literal_sound
#check @solTok_literal_iff
#print axioms solTok_literal_iff
#check @yulWordTable_no_literal
#print axioms yulWordTable_no_literal
#check @yulWord_no_literal
#print axioms yulWord_no_literal
#check @yulNumber_no_literal
#print axioms yulNumber_no_literal
#check @yulTok_literal_sound
#print axioms yulTok_literal_sound
#check @Plain.yulTok
#print axioms Plain.yulTok
#check @HexLiteral.yulTok
#print axioms HexLiteral.yulTok
#check @yulTok_plain_iff
#print axioms yulTok_plain_iff
#check @yulTok_hex_iff
#print axioms yulTok_hex_iff
#check @yulTok_unicode_impossible
#print axioms yulTok_unicode_impossible
#check @Flavor.Rel.noTrivia
#print axioms Flavor.Rel.noTrivia
#check @classify_sol_literal_iff
#print axioms classify_sol_literal_iff
#check @classify_yul_literal_sound
#print axioms classify_yul_literal_sound
#check @classify_yul_plain_iff
#print axioms classify_yul_plain_iff
#check @classify_yul_hex_iff
#print axioms classify_yul_hex_iff
#check @classify_yul_unicode_impossible
#print axioms classify_yul_unicode_impossible
#check @solTok_no_flavor_iff
#print axioms solTok_no_flavor_iff
#check @classify_asm_plain_iff
#print axioms classify_asm_plain_iff
#check @classify_asm_nonplain_impossible
#print axioms classify_asm_nonplain_impossible
#check @classify_pragma_literal_impossible
#print axioms classify_pragma_literal_impossible
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
#check @hexControls_pass
#print axioms hexControls_pass
#check @hexGrammar_inhabited
#print axioms hexGrammar_inhabited
#check @hexGrammar_no_trailing
#print axioms hexGrammar_no_trailing
#check @hexEncoding_control
#print axioms hexEncoding_control
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
#check @modeLiteral_iff
#print axioms modeLiteral_iff
#check @ModeLiteral.split
#print axioms ModeLiteral.split
#check @modeSequence_iff
#print axioms modeSequence_iff
#check @ModeSequence.append
#print axioms ModeSequence.append
#check @sequenceBytes_append
#print axioms sequenceBytes_append
#check @ModeSequence.split_head
#print axioms ModeSequence.split_head
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
#check @encodePlain_sol_classify
#print axioms encodePlain_sol_classify
#check @encodePlain_yul_classify
#print axioms encodePlain_yul_classify
#check @encodeHex_sol_classify
#print axioms encodeHex_sol_classify
#check @encodeHex_yul_classify
#print axioms encodeHex_yul_classify
#check @encodeUnicode_sol_classify
#print axioms encodeUnicode_sol_classify
#check @encodeAssembly_grammar
#print axioms encodeAssembly_grammar
#check @encodeAssembly_classify
#print axioms encodeAssembly_classify
#check @encodeAssembly_length
#print axioms encodeAssembly_length
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
#check @Scan.split_quoted
#print axioms Scan.split_quoted
#check @Scan.split_hex
#print axioms Scan.split_hex
#check @Scan.split_unicode
#print axioms Scan.split_unicode
#check @split_yul_unicode_word
#print axioms split_yul_unicode_word
#check @Plain.split_mode
#print axioms Plain.split_mode
#check @HexLiteral.split
#print axioms HexLiteral.split
#check @UnicodeLiteral.split
#print axioms UnicodeLiteral.split
#check @hex_regular
#print axioms hex_regular
#check @encodeBody_regular
#print axioms encodeBody_regular
#check @regular_irregularBreak
#print axioms regular_irregularBreak
#check @bidi_walk_noE2
#print axioms bidi_walk_noE2
#check @regular_bidiBalanced
#print axioms regular_bidiBalanced
#check @encodeHexLiteral_grammar
#print axioms encodeHexLiteral_grammar
#check @encodeUnicodeLiteral_grammar
#print axioms encodeUnicodeLiteral_grammar
#check @encodeHexLiteral_roundtrip
#print axioms encodeHexLiteral_roundtrip
#check @encodeUnicodeLiteral_roundtrip
#print axioms encodeUnicodeLiteral_roundtrip
#check @encodeHexLiteral_length
#print axioms encodeHexLiteral_length
#check @encodeUnicodeLiteral_length
#print axioms encodeUnicodeLiteral_length
#check @word_cases
#print axioms word_cases
#check @word_dite
#print axioms word_dite
#check @word_transport
#print axioms word_transport
#check @solWordTable_nonliteral
#print axioms solWordTable_nonliteral
#check @Scan.deterministic
#print axioms Scan.deterministic
#check @Scan.isSuffix
#print axioms Scan.isSuffix
#check @Scan.length_lt
#print axioms Scan.length_lt
#check @Scan.length_eq
#print axioms Scan.length_eq
#check @Plain.length_le
#print axioms Plain.length_le
#check @HexLiteral.length_bounds
#print axioms HexLiteral.length_bounds
#check @HexBody.length_tight
#print axioms HexBody.length_tight
#check @HexLiteral.length_le_tight
#print axioms HexLiteral.length_le_tight
#check @UnicodeLiteral.length_le
#print axioms UnicodeLiteral.length_le
#check @Fragments.length_eq
#print axioms Fragments.length_eq
#check @Fragments.flatten_length_le
#print axioms Fragments.flatten_length_le
#check @FragmentValue.plain_length_le
#print axioms FragmentValue.plain_length_le
#check @FragmentValue.hex_length_le
#print axioms FragmentValue.hex_length_le
#check @FragmentValue.unicode_length_le
#print axioms FragmentValue.unicode_length_le
#check @CodepointBytes.shape
#print axioms CodepointBytes.shape
#check @CodepointBytes.value
#print axioms CodepointBytes.value
#check @utf8_injective
#print axioms utf8_injective
#check @uniEscape_shape
#print axioms uniEscape_shape
#check @uniEscape_value
#print axioms uniEscape_value

end Solidity.Frontend.LiteralGrammarH28
