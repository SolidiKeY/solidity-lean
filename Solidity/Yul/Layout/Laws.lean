import Solidity.Yul.Layout.Laws.WriteRead
import Solidity.Yul.Layout.Laws.Alloc

/-!
# The laws of the layout view

`view_laws` assembles `Shrink.LayoutView.Laws` at `view` from its seven
fields: `local_read` (`Laws/Read.lean`), `write_total`, `illTyped` and `frame`
(`Laws/Write.lean`), `write_read` (`Laws/WriteRead.lean`), `alloc_read` and
`alloc_total` (`Laws/Alloc.lean`).
-/
namespace Solidity.Yul.Layout

open Solidity.Goals

/-- **The laws** of the layout view, for every layout, location, tree, state
and parameters. -/
theorem view_laws : view.Laws where
  local_read := local_read
  write_read := write_read
  write_total := write_total
  illTyped := illTyped
  frame := frame
  alloc_read := alloc_read
  alloc_total := alloc_total

end Solidity.Yul.Layout
