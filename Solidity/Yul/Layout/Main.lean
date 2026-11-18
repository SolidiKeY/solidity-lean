import Solidity.Yul.Layout.Laws
import Solidity.Yul.Layout.Instances.Storage
import Solidity.Yul.Layout.Instances.Memory
import Solidity.Yul.Layout.Instances.Allocation

/-!
# The layout-view goal

`view_instances` collects the nine per-shape instances of `view`;
`view_correct` closes `Solidity.Goals.yulLayoutView`.
-/
namespace Solidity.Yul.Layout

open Solidity.Goals

/-- Every per-shape instance of the one layout view. -/
theorem view_instances : view.Instances where
  scalarPath := Instances.scalarPath
  apart := Instances.apart
  cells := Instances.cells
  wordList := Instances.wordList
  memberArray := Instances.memberArray
  bytesObject := Instances.bytesObject
  enumerated := Instances.enumerated
  byteAllocation := Instances.byteAllocation
  objectAllocation := Instances.objectAllocation

/-- The layout-view goal: one view with its laws, geometry and instances. -/
theorem view_correct : Solidity.Goals.yulLayoutView :=
  ⟨view, view_laws, view_geometric, view_instances⟩

end Solidity.Yul.Layout
