import Solidity.Frontend.LiteralGrammarH28.HexEncoding

/-! # Hex body kernel controls

Rows are enumerated independently from the decoder recursion: empty; every
pair digit category and case; adjacent and separated groups; odd counts;
leading/trailing/doubled/intra-pair separators; invalid first/second digits
in adjacent and separated groups; and whitespace. These finite controls
supplement the universal proofs; they are not completeness by sampling.
-/
namespace Solidity.Frontend.LiteralGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def hexControls : List (String × Option Bytes) := [
  ("", some []), ("00", some [0]), ("ff", some [255]), ("FF", some [255]),
  ("aF", some [175]), ("09", some [9]), ("0001", some [0, 1]),
  ("00_01", some [0, 1]), ("00_01FF_ee", some [0, 1, 255, 238]),
  ("_", none), ("0", none), ("000", none), ("_00", none), ("00_", none),
  ("00__00", none), ("0_0", none), ("00_0", none), ("g0", none),
  ("0g", none), ("gg", none), ("g0_00", none), ("0g_00", none),
  ("00_g0", none), ("00_0g", none), ("00g0", none), ("000g", none), ("00 00", none), ("00\n00", none)]

theorem hexControls_pass :
    hexControls.all (fun row => hexBody (ascii row.1) == row.2) = true := by
  decide +kernel

/-- An inhabited nonempty grammar control with a separator. -/
theorem hexGrammar_inhabited : HexBody (ascii "00_01FF_ee") [0, 1, 255, 238] :=
  hexBody_sound _ _ (by decide +kernel)

/-- A universal negative grammar control, not merely a decoder observation. -/
theorem hexGrammar_no_trailing (out : Bytes) : ¬ HexBody (ascii "00_") out :=
  (hexBody_none_iff _).mp (by decide +kernel) out

/-- A concrete value encoding control includes both endpoints and high bytes. -/
theorem hexEncoding_control :
    encodeHex [0, 1, 127, 128, 254, 255] = ascii "00017f80feff" := by
  decide +kernel

end Solidity.Frontend.LiteralGrammarH28
