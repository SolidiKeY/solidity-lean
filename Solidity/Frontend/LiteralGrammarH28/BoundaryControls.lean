import Solidity.Frontend.LiteralGrammarH28.Scanner

/-! # Independently enumerated quote/scanner boundary controls

Quoted-body helper acceptance is distinguished from valid body decoding.
Both quote modes cover all scanner clauses and binary suffix preservation.
-/
namespace Solidity.Frontend.LiteralGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def quoteControls : List (String × Bytes × Option (UInt8 × Bytes)) := [
  ("empty", [], none),
  ("opener-double", [34], none),
  ("opener-single", [39], none),
  ("empty-double", [34, 34], some (34, [])),
  ("empty-single", [39, 39], some (39, [])),
  ("double-body", [34, 65, 34], some (34, [65])),
  ("single-body", [39, 65, 39], some (39, [65])),
  ("wrong-close-double", [34, 65, 39], none),
  ("wrong-close-single", [39, 65, 34], none),
  ("invalid-opener", [33, 65, 33], none),
  ("internal-quote-helper", [34, 34, 34], some (34, [34])),
  ("binary-body-helper", [39, 0, 255, 39], some (39, [0, 255]))]

def scanControls : List (String × UInt8 × Bytes × Option (Bytes × Bytes)) := [
  ("double-CRLF-at-EOF", 34, [92, 13, 10], none),
  ("single-CRLF-at-EOF", 39, [92, 13, 10], none),
  ("double-empty", 34, [], none),
  ("double-close", 34, [34, 65], some ([34], [65])),
  ("double-raw", 34, [65, 34, 66], some ([65, 34], [66])),
  ("double-raw-LF", 34, [10, 34], none),
  ("double-raw-CR", 34, [13, 34], none),
  ("double-unterminated", 34, [65], none),
  ("double-lone-slash", 34, [92], none),
  ("double-escaped-final-quote", 34, [92, 34], none),
  ("double-escape-quote", 34, [92, 34, 34, 1], some ([92, 34, 34], [1])),
  ("double-escape-slash", 34, [92, 92, 34], some ([92, 92, 34], [])),
  ("double-escape-LF", 34, [92, 10, 34], some ([92, 10, 34], [])),
  ("double-escape-CR", 34, [92, 13, 34], some ([92, 13, 34], [])),
  ("double-escape-CRLF", 34, [92, 13, 10, 34], some ([92, 13, 10, 34], [])),
  ("double-unknown-escape-scan", 34, [92, 122, 34], some ([92, 122, 34], [])),
  ("double-binary-suffix", 34, [34, 0, 255, 92, 13, 10, 34], some ([34], [0, 255, 92, 13, 10, 34])),
  ("double-binary-interior", 34, [255, 0, 34], some ([255, 0, 34], [])),
  ("single-empty", 39, [], none),
  ("single-close", 39, [39, 65], some ([39], [65])),
  ("single-raw", 39, [65, 39, 66], some ([65, 39], [66])),
  ("single-raw-LF", 39, [10, 39], none),
  ("single-raw-CR", 39, [13, 39], none),
  ("single-unterminated", 39, [65], none),
  ("single-lone-slash", 39, [92], none),
  ("single-escaped-final-quote", 39, [92, 39], none),
  ("single-escape-quote", 39, [92, 39, 39, 1], some ([92, 39, 39], [1])),
  ("single-escape-slash", 39, [92, 92, 39], some ([92, 92, 39], [])),
  ("single-escape-LF", 39, [92, 10, 39], some ([92, 10, 39], [])),
  ("single-escape-CR", 39, [92, 13, 39], some ([92, 13, 39], [])),
  ("single-escape-CRLF", 39, [92, 13, 10, 39], some ([92, 13, 10, 39], [])),
  ("single-unknown-escape-scan", 39, [92, 122, 39], some ([92, 122, 39], [])),
  ("single-binary-suffix", 39, [39, 0, 255, 92, 13, 10, 39], some ([39], [0, 255, 92, 13, 10, 39])),
  ("single-binary-interior", 39, [255, 0, 39], some ([255, 0, 39], []))]

def plainControls : List (String × Bytes × Option Bytes) := [
  ("empty-input", [], none),
  ("missing-close-double", [34], none),
  ("missing-close-single", [39], none),
  ("empty-double", [34, 34], some []),
  ("empty-single", [39, 39], some []),
  ("escaped-value", [34, 92, 120, 102, 70, 34], some [255]),
  ("unknown-escape", [34, 92, 122, 34], none),
  ("internal-quote", [34, 34, 34], none),
  ("raw-high", [39, 255, 39], none),
  ("CRLF-empty", [34, 92, 13, 10, 34], some [])]

theorem quoteControls_pass : quoteControls.all
    (fun (_, raw, expected) => quotedBody raw == expected) = true := by decide +kernel

theorem scanControls_pass : scanControls.all
    (fun (_, q, raw, expected) => untilQuote q raw == expected) = true := by decide +kernel

theorem plainControls_pass : plainControls.all
    (fun (_, raw, expected) => plainString raw == expected) = true := by decide +kernel

theorem quotedGrammar_inhabited : Quoted [34, 0, 255, 34] 34 [0, 255] :=
  ⟨Or.inl rfl, rfl⟩

theorem plainGrammar_inhabited : Plain [34, 92, 120, 102, 70, 34] [255] :=
  plainString_sound _ _ (by decide +kernel)

theorem scannerGrammar_inhabited : Scan 39 [92, 122, 39, 255] [92, 122, 39] [255] :=
  untilQuote_sound _ _ _ _ (by decide +kernel)

theorem scannerGrammar_empty_refused (q : UInt8) (pre suffix : Bytes) :
    ¬ Scan q [] pre suffix := by
  intro h
  exact h.input_nonempty rfl

/-- Exact equivalence cannot be extended to a nonliteral delimiter. -/
theorem scanner_nonliteral_boundary :
    Scan 92 [92, 0] [92] [0] ∧ untilQuote 92 [92, 0] = none :=
  ⟨.close, by decide +kernel⟩

end Solidity.Frontend.LiteralGrammarH28
