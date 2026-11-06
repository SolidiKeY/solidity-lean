import Solidity.Frontend.LiteralGrammarH28.Body

/-! # Independent body and escape kernel controls

Coverage names are independent of function induction. Cases pin CRLF priority,
each successful simple tag, malformed/truncated x/u, all four bad unicode-digit
positions, both quote modes and exact byte semantics at UTF8 thresholds and
surrogates. No UTF8 validation is added to the raw unicode body predicate.
-/
namespace Solidity.Frontend.LiteralGrammarH28
open Solidity.Source Solidity.Frontend.Checked

inductive BodyMode where
  | all | none | plain (q : UInt8) | unicode (q : UInt8)

def BodyMode.allowed : BodyMode → UInt8 → Bool
  | .all => fun _ => true
  | .none => fun _ => false
  | .plain q => printable q
  | .unicode q => unicodeChar q

def bodyControls : List (String × BodyMode × Bytes × Option Bytes) := [
  ("empty", .none, [], some []),
  ("raw-arbitrary", .all, [0, 10, 13, 255], some [0, 10, 13, 255]),
  ("raw-plain", .plain 34, [32, 65, 126], some [32, 65, 126]),
  ("raw-plain-control", .plain 34, [31], none),
  ("raw-plain-high", .plain 34, [255], none),
  ("raw-unicode-invalid-utf8", .unicode 34, [255], some [255]),
  ("raw-unicode-LF", .unicode 34, [10], none),
  ("raw-unicode-CR", .unicode 34, [13], none),
  ("raw-same-quote", .plain 34, [34], none),
  ("raw-other-quote", .plain 39, [34], some [34]),
  ("raw-other-quote-double", .plain 34, [39], some [39]),
  ("raw-single-quote-refusal", .plain 39, [39], none),
  ("unicode-double-quote-refusal", .unicode 34, [34], none),
  ("unicode-double-other-quote", .unicode 34, [39], some [39]),
  ("unicode-single-quote-refusal", .unicode 39, [39], none),
  ("unicode-single-other-quote", .unicode 39, [34], some [34]),
  ("escape-single", .none, [92, 39], some [39]),
  ("escape-double", .none, [92, 34], some [34]),
  ("escape-slash", .none, [92, 92], some [92]),
  ("escape-n", .none, [92, 110], some [10]),
  ("escape-r", .none, [92, 114], some [13]),
  ("escape-t", .none, [92, 116], some [9]),
  ("escape-LF", .none, [92, 10], some []),
  ("escape-CR", .none, [92, 13], some []),
  ("escape-CRLF", .none, [92, 13, 10], some []),
  ("CRLF-followed-raw-LF", .all, [92, 13, 10, 10], some [10]),
  ("CR-then-escaped-LF", .none, [92, 13, 92, 10], some []),
  ("invalid-simple", .none, [92, 48], none),
  ("lone-backslash", .all, [92], none),
  ("x-zero", .none, [92, 120, 48, 48], some [0]),
  ("x-mixed-case", .none, [92, 120, 102, 70], some [255]),
  ("x-invalid-first", .all, [92, 120, 103, 48], none),
  ("x-invalid-second", .all, [92, 120, 48, 103], none),
  ("x-truncated-0", .all, [92, 120], none),
  ("x-truncated-1", .all, [92, 120, 48], none),
  ("x-exact-two-digits", .all, [92, 120, 52, 49, 50], some [65, 50]),
  ("u-007f", .none, [92, 117, 48, 48, 55, 102], some [127]),
  ("u-0080", .none, [92, 117, 48, 48, 56, 48], some [194, 128]),
  ("u-07ff", .none, [92, 117, 48, 55, 102, 102], some [223, 191]),
  ("u-0800", .none, [92, 117, 48, 56, 48, 48], some [224, 160, 128]),
  ("u-D800", .none, [92, 117, 68, 56, 48, 48], some [237, 160, 128]),
  ("u-DFFF", .none, [92, 117, 68, 70, 70, 70], some [237, 191, 191]),
  ("u-FFFF", .none, [92, 117, 70, 70, 70, 70], some [239, 191, 191]),
  ("u-truncated-0", .all, [92, 117], none),
  ("u-truncated-1", .all, [92, 117, 48], none),
  ("u-truncated-2", .all, [92, 117, 48, 48], none),
  ("u-truncated-3", .all, [92, 117, 48, 48, 48], none),
  ("u-invalid-digit-0", .all, [92, 117, 103, 48, 48, 48], none),
  ("u-invalid-digit-1", .all, [92, 117, 48, 103, 48, 48], none),
  ("u-invalid-digit-2", .all, [92, 117, 48, 48, 103, 48], none),
  ("u-invalid-digit-3", .all, [92, 117, 48, 48, 48, 103], none),
  ("u-exact-four-digits", .all, [92, 117, 48, 48, 52, 49, 50], some [65, 50]),
  ("mixed-recursive", .all, [65, 92, 110, 92, 120, 52, 49, 92, 117, 48, 48, 69, 57, 92, 13, 10, 66], some [65, 10, 65, 195, 169, 66])]

theorem bodyControls_pass : bodyControls.all
    (fun (_, m, raw, out) => strBody m.allowed raw == out) = true := by
  decide +kernel

/-- A nonempty mixed derivation inhabits the independent grammar. -/
theorem bodyGrammar_inhabited :
    Body (fun _ => true) [65, 92, 110, 92, 120, 52, 49] [65, 10, 65] :=
  body_sound _ _ _ (by decide +kernel)

/-- Existing relation's overlap is retained visibly as a counterexample. -/
theorem oldStrBody_overlap : StrBody (fun _ => true) [92, 13, 10] [10] :=
  .esc (c := 13) (o := []) (r := [10]) (out := [10])
    (by decide +kernel) (.char (b := 10) (r := []) (out := []) rfl (by decide +kernel) .nil)

theorem bodyCRLF_empty : Body (fun _ => true) [92, 13, 10] [] :=
  .crlf .nil

theorem bodyCRLF_no_alternate : ¬ Body (fun _ => true) [92, 13, 10] [10] := by
  intro h
  have e : strBody (fun _ => true) [92, 13, 10] = some [10] := body_complete h
  have impossible : strBody (fun _ => true) [92, 13, 10] ≠ some [10] := by decide +kernel
  exact impossible e

/-- The round trip includes arbitrary high bytes under the empty predicate. -/
theorem bodyEncoding_control :
    strBody (fun _ => false) (encodeBody [0, 127, 128, 255]) = some [0, 127, 128, 255] :=
  encodeBody_roundtrip _ _

end Solidity.Frontend.LiteralGrammarH28
