import Solidity.Semantics.Storage.TypeLayout

/-!
# Boolean packing differs from the full-word model

Claim tested: `Evm.offsetIn` and `Evm.size` agree with solc storage layout
for representable boolean fields and fixed arrays. For
`contract C { bool a; bool b; bool[2] flags; uint256 tail; }`, solc places
`b` at slot 0, byte 1, and `tail` at slot 2. The full-word model places
`b` at slot 1 and `tail` at slot 4. This is an external-layout mismatch,
not a refutation of the full-word arithmetic theorems.

Culprit: Solidity/Semantics/Storage/TypeLayout.lean:16 (sizeF primitive
fallback) and :25 (offsetIn); Solidity/Evm/Layout.lean:10 claims solc layout.
Suggested fix: track byte widths and offsets, pack booleans, and round arrays
and structs to slot boundaries, or restrict external agreement to unpacked
layouts. No production definition is changed by this witness.
-/

namespace Solidity.Examples.RedTeam.StorageLayout.BoolPacking

open Solidity Evm

/-- The model gives the second boolean a fresh word, unlike solc slot 0. -/
theorem second_bool_mismatch :
    offsetIn [("a", .prim .bool), ("b", .prim .bool)] "b" = 1 ∧
    offsetIn [("a", .prim .bool), ("b", .prim .bool)] "b" ≠ 0 := by
  decide

/-- Solidity `bool[2]` needs one slot; the model allocates two words. -/
theorem fixed_bool_mismatch :
    size (.ref (.fixed (.prim .bool) 2)) = 2 ∧
    size (.ref (.fixed (.prim .bool) 2)) ≠ 1 := by
  decide

/-- After two packed booleans and a bool array solc starts tail at slot 2. -/
theorem tail_mismatch :
    offsetIn [("a", .prim .bool), ("b", .prim .bool),
      ("flags", .ref (.fixed (.prim .bool) 2)), ("tail", .prim .uint)] "tail" = 4 ∧
    offsetIn [("a", .prim .bool), ("b", .prim .bool),
      ("flags", .ref (.fixed (.prim .bool) 2)), ("tail", .prim .uint)] "tail" ≠ 2 := by
  decide

/-- Solidity `struct Packed { bool a; bool b; }` occupies one slot. -/
theorem struct_bool_mismatch :
    size (.ref (.struct "Packed{a:bool;b:bool}")) = 2 ∧
    size (.ref (.struct "Packed{a:bool;b:bool}")) ≠ 1 := by
  decide

/-- Dynamic `bool[]` element 1 remains in data slot 0, byte 1 in solc.
The model stride used by `Evm.Occ.elem` is one whole slot. -/
theorem dynamic_bool_stride_mismatch :
    1 * size (.prim .bool) = 1 ∧ 1 * size (.prim .bool) ≠ 0 := by
  decide

/-- Shared-ancestor Solidity fixture `Shared`: given solc's flattened order,
word-sized fields agree. This tests offsets, not a Lean C3 linearizer. -/
theorem shared_ancestor_offsets :
    (let fields : List (Name × Ty) :=
      [("ancestor", .prim .uint), ("left", .prim .uint),
       ("right", .prim .uint), ("last", .prim .uint)]
     [offsetIn fields "ancestor", offsetIn fields "left",
      offsetIn fields "right", offsetIn fields "last"]) = [0, 1, 2, 3] := by
  decide

end Solidity.Examples.RedTeam.StorageLayout.BoolPacking
