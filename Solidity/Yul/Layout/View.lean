import Solidity.Yul.Layout.Alloc
import Solidity.Yul.Layout.Geometric

/-!
# The one layout view

`view` is the geometry with its allocator. `view_geometric` is the
transcription check `geometric` at that allocator.
-/
namespace Solidity.Yul.Layout

open Solidity.Goals

/-- **The layout view**: `geometry` and the bump allocator `alloc`. -/
def view : Shrink.LayoutView := ⟨geometry, alloc⟩

/-- The view has the pinned placements and codecs. -/
theorem view_geometric : view.Geometric := geometric alloc

end Solidity.Yul.Layout
