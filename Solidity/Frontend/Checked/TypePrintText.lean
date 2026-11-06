import Solidity.Frontend.Checked.TypeExampleCore

/-! Isolated unchanged G09 kernel control, for bounded performance checking. -/

namespace Solidity.Frontend.Checked

open Solidity.Source

theorem print_text :
    (match parseWithLayout (ascii "contract C{uint constant public x=0x01;string s='a\\n';}") with
      | .ok (u, L) => (u.print L).map Bytes.str
      | .error _ => none) =
      some "contract C { uint256 constant public x = 0x01 ; string s = \"a\\x0a\" ; }" := by
  decide +kernel

end Solidity.Frontend.Checked
