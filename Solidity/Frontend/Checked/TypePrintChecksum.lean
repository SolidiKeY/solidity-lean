import Solidity.Frontend.Checked.TypeExampleCore

/-! Isolated unchanged G09 kernel control, for bounded performance checking. -/

namespace Solidity.Frontend.Checked

open Solidity.Source

/-- A 40-digit hex literal whose lowercase spelling is its checksum, spelled
otherwise, keeps its cleared flag through printing. -/
theorem print_checksum_flag :
    (reprintFingerprint "contract C { address a = 0x000000000000000000000000000000000000000B; }") ==
      fingerprint (parseWithLayout (ascii
        "contract C { address a = 0x000000000000000000000000000000000000000B; }")) &&
    (reprintFingerprint "contract C { string s = unicode\"\\u2028\\u202e\\u202c\"; }").isSome
      = true := by
  decide +kernel

end Solidity.Frontend.Checked
