import Solidity.Frontend.LiteralGrammarH28.ModeGrammar
import Solidity.Frontend.LiteralGrammarH28.FragmentCompleteness
import Solidity.Frontend.LiteralGrammarH28.EncodingValue
import Solidity.Frontend.LiteralGrammarH28.BoundaryControls
import Solidity.Frontend.LiteralGrammarH28.BodyControls
import Solidity.Frontend.LiteralGrammarH28.HexControls

/-! # Full nonnumeric classification and fragment kernel controls

Model expectations are independent of compiler outcomes. In particular the
three recorded model/compiler differences remain distinct and visible.
-/
namespace Solidity.Frontend.LiteralGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def fullControls : List (String × Mode × Bytes × Option Kind) := [
  ("yul-word-priority", .yul 0, [97], some (.tok (.ident "a"))),
  ("yul-punctuation-priority", .yul 0, [40], some (.tok (.punct .lparen))),
  ("yul-hex-no-closer", .yul 0, [104, 101, 120, 34, 48], none),
  ("yul-hex-odd", .yul 0, [104, 101, 120, 34, 48, 34], none),
  ("yul-plain-bad-escape", .yul 0, [34, 92, 122, 34], none),
  ("asm-bad-escape", .asm, [34, 92, 122, 34], none),
  ("asm-no-closer", .asm, [34, 65, 66], none),
  ("plain-double-empty", .sol, [34, 34], some (.tok (.str []))),
  ("plain-single-empty", .sol, [39, 39], some (.tok (.str []))),
  ("simple-escapes-double", .sol, [34, 92, 39, 92, 34, 92, 92, 92, 110, 92, 114, 92, 116, 34], some (.tok (.str [39, 34, 92, 10, 13, 9]))),
  ("line-continuations-double", .sol, [34, 65, 92, 10, 66, 92, 13, 67, 92, 13, 10, 68, 34], some (.tok (.str [65, 66, 67, 68]))),
  ("simple-escapes-single", .sol, [39, 92, 39, 92, 34, 92, 92, 92, 110, 92, 114, 92, 116, 39], some (.tok (.str [39, 34, 92, 10, 13, 9]))),
  ("line-continuations-single", .sol, [39, 65, 92, 10, 66, 92, 13, 67, 92, 13, 10, 68, 39], some (.tok (.str [65, 66, 67, 68]))),
  ("hex-byte-escapes", .sol, [34, 92, 120, 48, 48, 92, 120, 70, 102, 34], some (.tok (.str [0, 255]))),
  ("plain-unicode-escape", .sol, [34, 92, 117, 48, 48, 101, 57, 34], some (.tok (.str [195, 169]))),
  ("unicode-escape-thresholds", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 92, 117, 48, 48, 55, 102, 92, 117, 48, 48, 56, 48, 92, 117, 48, 55, 102, 102, 92, 117, 48, 56, 48, 48, 92, 117, 68, 56, 48, 48, 92, 117, 68, 70, 70, 70, 92, 117, 70, 70, 70, 70, 34], some (.tok (.unicodeStr [127, 194, 128, 223, 191, 224, 160, 128, 237, 160, 128, 237, 191, 191, 239, 191, 191]))),
  ("unicode-raw", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 195, 169, 240, 159, 146, 161, 34], some (.tok (.unicodeStr [195, 169, 240, 159, 146, 161]))),
  ("unicode-balanced-bidi", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 226, 128, 174, 65, 226, 128, 172, 34], some (.tok (.unicodeStr [226, 128, 174, 65, 226, 128, 172]))),
  ("hex-double-empty", .sol, [104, 101, 120, 34, 34], some (.tok (.hexStr []))),
  ("hex-single-empty", .sol, [104, 101, 120, 39, 39], some (.tok (.hexStr []))),
  ("hex-adjacent", .sol, [104, 101, 120, 34, 48, 48, 70, 70, 97, 70, 34], some (.tok (.hexStr [0, 255, 175]))),
  ("hex-separated", .sol, [104, 101, 120, 39, 48, 48, 95, 70, 70, 95, 48, 49, 39], some (.tok (.hexStr [0, 255, 1]))),
  ("plain-concat#0", .sol, [34, 65, 34], some (.tok (.str [65]))),
  ("plain-concat#1", .sol, [39, 92, 120, 48, 48, 39], some (.tok (.str [0]))),
  ("plain-concat#2", .sol, [34, 92, 117, 48, 48, 101, 57, 34], some (.tok (.str [195, 169]))),
  ("unicode-concat#0", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 65, 34], some (.tok (.unicodeStr [65]))),
  ("unicode-concat#1", .sol, [117, 110, 105, 99, 111, 100, 101, 39, 195, 169, 39], some (.tok (.unicodeStr [195, 169]))),
  ("hex-concat#0", .sol, [104, 101, 120, 34, 48, 48, 34], some (.tok (.hexStr [0]))),
  ("hex-concat#1", .sol, [104, 101, 120, 39, 70, 70, 95, 48, 49, 39], some (.tok (.hexStr [255, 1]))),
  ("yul-empty", .yul 7, [34, 34], some (.tok (.str []))),
  ("yul-single", .yul 7, [39, 65, 39], some (.tok (.str [65]))),
  ("yul-escapes", .yul 7, [34, 92, 120, 48, 48, 92, 120, 70, 70, 34], some (.tok (.str [0, 255]))),
  ("yul-hex", .yul 7, [104, 101, 120, 34, 48, 48, 95, 70, 102, 34], some (.tok (.hexStr [0, 255]))),
  ("yul-CRLF", .yul 7, [34, 65, 92, 13, 10, 66, 34], some (.tok (.str [65, 66]))),
  ("assembly-double-flag", .asm, [34, 109, 101, 109, 111, 114, 121, 45, 115, 97, 102, 101, 34], some (.tok (.str [109, 101, 109, 111, 114, 121, 45, 115, 97, 102, 101]))),
  ("bad-simple", .sol, [34, 92, 122, 34], none),
  ("short-x", .sol, [34, 92, 120, 48, 34], none),
  ("x-first", .sol, [34, 92, 120, 103, 48, 34], none),
  ("x-second", .sol, [34, 92, 120, 48, 103, 34], none),
  ("short-u", .sol, [34, 92, 117, 48, 48, 48, 34], none),
  ("u-invalid-0", .sol, [34, 92, 117, 103, 48, 48, 48, 34], none),
  ("u-invalid-1", .sol, [34, 92, 117, 48, 103, 48, 48, 34], none),
  ("u-invalid-2", .sol, [34, 92, 117, 48, 48, 103, 48, 34], none),
  ("u-invalid-3", .sol, [34, 92, 117, 48, 48, 48, 103, 34], none),
  ("plain-raw-high", .sol, [34, 195, 169, 34], none),
  ("plain-raw-LF", .sol, [34, 65, 10, 66, 34], none),
  ("unicode-raw-LF", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 65, 10, 66, 34], none),
  ("unicode-FF", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 12, 34], none),
  ("unicode-VT", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 11, 34], none),
  ("unicode-U2028", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 226, 128, 168, 34], none),
  ("unicode-U2029", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 226, 128, 169, 34], none),
  ("unicode-open-bidi", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 226, 128, 174, 34], none),
  ("unicode-close-bidi", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 226, 128, 172, 34], none),
  ("hex-odd", .sol, [104, 101, 120, 34, 48, 34], none),
  ("hex-leading", .sol, [104, 101, 120, 34, 95, 48, 48, 34], none),
  ("hex-trailing", .sol, [104, 101, 120, 34, 48, 48, 95, 34], none),
  ("hex-doubled", .sol, [104, 101, 120, 34, 48, 48, 95, 95, 102, 102, 34], none),
  ("hex-intrapair", .sol, [104, 101, 120, 34, 48, 95, 48, 34], none),
  ("hex-invalid-first", .sol, [104, 101, 120, 34, 103, 48, 34], none),
  ("hex-invalid-second", .sol, [104, 101, 120, 34, 48, 103, 34], none),
  ("hex-space", .sol, [104, 101, 120, 34, 48, 48, 32, 102, 102, 34], none),
  ("yul-bare-hex", .yul 7, [104, 101, 120], none),
  ("yul-unicode", .yul 7, [117, 110, 105, 99, 111, 100, 101, 34, 65, 34], none),
  ("assembly-empty-flag", .asm, [34, 34], none),
  ("assembly-single-flag", .asm, [39, 109, 101, 109, 111, 114, 121, 45, 115, 97, 102, 101, 39], none),
  ("unicode-valid-thresholds", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 92, 117, 48, 48, 48, 48, 92, 117, 48, 48, 55, 102, 92, 117, 48, 48, 56, 48, 92, 117, 48, 55, 102, 102, 92, 117, 48, 56, 48, 48, 92, 117, 70, 70, 70, 70, 34], some (.tok (.unicodeStr [0, 127, 194, 128, 223, 191, 224, 160, 128, 239, 191, 191]))),
  ("plain-surrogate-escape", .sol, [34, 92, 117, 68, 56, 48, 48, 34], some (.tok (.str [237, 160, 128]))),
  ("unicode-escaped-irregular", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 92, 120, 48, 99, 92, 117, 50, 48, 50, 56, 34], some (.tok (.unicodeStr [12, 226, 128, 168]))),
  ("unicode-escaped-bidi", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 92, 117, 50, 48, 50, 101, 34], some (.tok (.unicodeStr [226, 128, 174]))),
  ("plain-raw-TAB", .sol, [34, 65, 9, 66, 34], none),
  ("plain-raw-NUL", .sol, [34, 0, 34], none),
  ("plain-raw-DEL", .sol, [34, 127, 34], none),
  ("unicode-raw-TAB", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 65, 9, 66, 34], some (.tok (.unicodeStr [65, 9, 66]))),
  ("unicode-raw-NUL", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 0, 34], some (.tok (.unicodeStr [0]))),
  ("unicode-raw-DEL", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 127, 34], some (.tok (.unicodeStr [127]))),
  ("unicode-raw-CR", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 65, 13, 66, 34], none),
  ("yul-raw-TAB", .yul 7, [34, 65, 9, 66, 34], none),
  ("plain-double-other-quote", .sol, [34, 39, 34], some (.tok (.str [39]))),
  ("plain-single-other-quote", .sol, [39, 34, 39], some (.tok (.str [34]))),
  ("unicode-double-other-quote", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 39, 34], some (.tok (.unicodeStr [39]))),
  ("unicode-single-other-quote", .sol, [117, 110, 105, 99, 111, 100, 101, 39, 34, 39], some (.tok (.unicodeStr [34]))),
  ("yul-single-other-quote", .yul 7, [39, 34, 39], some (.tok (.str [34]))),
  ("raw-invalid-UTF8-ff", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 255, 34], some (.tok (.unicodeStr [255]))),
  ("raw-invalid-UTF8-e2", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 226, 34], some (.tok (.unicodeStr [226]))),
  ("raw-invalid-UTF8-e280", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 226, 128, 34], some (.tok (.unicodeStr [226, 128]))),
  ("bidi-other80", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 226, 128, 128, 34], some (.tok (.unicodeStr [226, 128, 128]))),
  ("bidi-other81", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 226, 129, 128, 34], some (.tok (.unicodeStr [226, 129, 128]))),
  ("bidi-balanced-LRE", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 226, 128, 170, 65, 226, 128, 172, 34], some (.tok (.unicodeStr [226, 128, 170, 65, 226, 128, 172]))),
  ("bidi-open-LRE", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 226, 128, 170, 34], none),
  ("bidi-balanced-RLE", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 226, 128, 171, 65, 226, 128, 172, 34], some (.tok (.unicodeStr [226, 128, 171, 65, 226, 128, 172]))),
  ("bidi-open-RLE", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 226, 128, 171, 34], none),
  ("bidi-balanced-LRO", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 226, 128, 173, 65, 226, 128, 172, 34], some (.tok (.unicodeStr [226, 128, 173, 65, 226, 128, 172]))),
  ("bidi-open-LRO", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 226, 128, 173, 34], none),
  ("bidi-balanced-RLO", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 226, 128, 174, 65, 226, 128, 172, 34], some (.tok (.unicodeStr [226, 128, 174, 65, 226, 128, 172]))),
  ("bidi-open-RLO", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 226, 128, 174, 34], none),
  ("bidi-balanced-LRI", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 226, 129, 166, 65, 226, 129, 169, 34], some (.tok (.unicodeStr [226, 129, 166, 65, 226, 129, 169]))),
  ("bidi-open-LRI", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 226, 129, 166, 34], none),
  ("bidi-balanced-RLI", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 226, 129, 167, 65, 226, 129, 169, 34], some (.tok (.unicodeStr [226, 129, 167, 65, 226, 129, 169]))),
  ("bidi-open-RLI", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 226, 129, 167, 34], none),
  ("bidi-balanced-FSI", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 226, 129, 168, 65, 226, 129, 169, 34], some (.tok (.unicodeStr [226, 129, 168, 65, 226, 129, 169]))),
  ("bidi-open-FSI", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 226, 129, 168, 34], none),
  ("bidi-close-PDI", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 226, 129, 169, 34], none),
  ("empty-source", .sol, [], none),
  ("trivia-priority", .sol, [32], some (.trivia .ws)),
  ("punct-priority", .sol, [40], some (.tok (.punct .lparen))),
  ("hex-word-priority", .sol, [104, 101, 120], some (.tok (.kw .hex))),
  ("unicode-word-priority", .sol, [117, 110, 105, 99, 111, 100, 101], some (.tok (.kw .unicode))),
  ("asm-empty-value-nonempty-source", .asm, [34, 92, 10, 34], some (.tok (.str []))),
  ("asm-punct-priority", .asm, [40], some (.tok (.punct .lparen))),
  ("asm-hex-refused", .asm, [104, 101, 120, 34, 48, 48, 34], none),
  ("asm-unicode-refused", .asm, [117, 110, 105, 99, 111, 100, 101, 34, 65, 34], none),
  ("yul-depth-zero", .yul 0, [34, 65, 34], some (.tok (.str [65]))),
  ("pragma-semi", .pragma, [59], some (.tok (.punct .semi))),
  ("pragma-quoted-word", .pragma, [34, 65, 34], some (.tok (.pragmaWord "\"A\""))),
  ("pragma-space-in-quoted-word", .pragma, [34, 65, 32, 66, 34], none),
  ("quoted-wrong-closing", .sol, [34, 65, 39], none),
  ("hex-missing-closing", .sol, [104, 101, 120, 34, 48, 48], none),
  ("unicode-missing-closing", .sol, [117, 110, 105, 99, 111, 100, 101, 34, 65], none)]

theorem fullControls_pass : fullControls.all
    (fun (_, mode, raw, expected) => decide (classify mode raw = expected)) = true := by
  decide +kernel

theorem assemblyGrammar_inhabited_empty_value : AssemblyLiteral [34, 92, 10, 34] [] :=
  (classify_asm_plain_iff _ _).mp (by decide +kernel)

theorem unicodeGrammar_inhabited_invalid_bytes : UnicodeLiteral
    [117, 110, 105, 99, 111, 100, 101, 34, 255, 34] [255] :=
  (classify_sol_literal_iff .unicode _ _).mp (by decide +kernel)

theorem codepoint_surrogate_control : CodepointBytes 55296 [237, 160, 128] :=
  (codepoint_iff _ _).mp (by decide +kernel)

theorem plainFragments_inhabited : Fragments Plain
    [[34, 65, 34], [39, 92, 120, 48, 48, 39], [34, 92, 117, 48, 48, 69, 57, 34]]
    [[65], [0], [195, 169]] :=
  (fragments_solTok_iff .plain _ _).mp (by decide +kernel)

theorem hexFragments_inhabited : Fragments HexLiteral
    [[104, 101, 120, 34, 48, 48, 34], [104, 101, 120, 39, 70, 70, 95, 48, 49, 39]]
    [[0], [255, 1]] :=
  (fragments_solTok_iff .hex _ _).mp (by decide +kernel)

theorem unicodeFragments_inhabited : Fragments UnicodeLiteral
    [[117, 110, 105, 99, 111, 100, 101, 34, 65, 34],
     [117, 110, 105, 99, 111, 100, 101, 39, 195, 169, 39]] [[65], [195, 169]] :=
  (fragments_solTok_iff .unicode _ _).mp (by decide +kernel)

theorem fragments_bad_second_refused (values : List Bytes) :
    ¬ Fragments Plain [[34, 65, 34], [34, 92, 122, 34]] values :=
  (fragments_none_iff Plain plainString plainString_iff _).mp (by decide +kernel) values

theorem cross_fragment_CR_LF_control :
    [[34, 92, 13, 34], [39, 92, 10, 39]].mapM plainString = some [[], []] := by
  decide +kernel

theorem mixedModeSequence_inhabited : ModeSequence .sol
    [[34, 65, 34], [104, 101, 120, 34, 70, 70, 34],
     [117, 110, 105, 99, 111, 100, 101, 34, 66, 34]]
    [(.plain, [65]), (.hex, [255]), (.unicode, [66])] :=
  (modeSequence_iff _ _ _).mp (by decide +kernel)

theorem yulUnicodeMode_refused (raw out : Bytes) :
    ¬ ModeLiteral (.yul 0) .unicode raw out := by
  intro h
  exact classify_yul_unicode_impossible 0 raw out ((modeLiteral_iff _ _ _ _).mpr h)

end Solidity.Frontend.LiteralGrammarH28
