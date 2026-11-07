import Solidity.Source.Calldata
import Solidity.Source.SemanticsExamples

/-!
# Controls of the static-element `calldata` copies (G18.05)

`cdToMem` copies a `uint256[2][] calldata` and a `uint256[2] calldata` into
memory element by element at the element's head stride (`cdStaticToMem`),
inner arrays allocated before the outer one, as `zeroData` allocates. Every
element is validated (a dirty `bool` reverts with no data); an element that
is not statically encoded is not inline, so its copy is `stuck`. The one-word
copy of a `uint256[] calldata` is unchanged.

The copies are exercised here by calling `cdToMem` directly; the nested
conversion from typed source is in `CalldataNestedCopyControls.lean`.
-/

namespace Solidity.Source.CalldataStaticCopyControls

open Solidity.Source Solidity.Source.SemanticsExamples

/-- A big-endian ABI word holding a small number. -/
def w (n : Nat) : List UInt8 := List.replicate 31 0 ++ [n.toUInt8]
def u : STy := .int IntTy.u256
def pair : STy := .array .memory u (some 2)
def frame : Fr := { F0 with cd := w 1 ++ w 2 ++ w 3 ++ w 4 }

/-- The words of a heap object's elements. -/
def words (o : Option (Σ τ, Data EB.layout τ)) : Option (List (Option Nat)) :=
  match o with
  | some ⟨_, .array _ _ xs⟩ => some ((List.ofFn xs).map fun
      | .val v => (Val.word v).map (·.val)
      | _ => none)
  | _ => none

def nested := (cdToMem frame (.array .memory pair none) 0 2 : EM EB [] _).run (L0 EB, sB)
def fixed := (cdToMem frame pair 32 2 : EM EB [] _).run (L0 EB, sB)
def flat := (cdToMem frame (.array .memory u none) 0 4 : EM EB [] _).run (L0 EB, sB)
def dirty := (cdToMem { F0 with cd := w 1 ++ w 2 } (.array .memory .bool (some 2)) 0 2 :
  EM EB [] _).run (L0 EB, sB)
def dynamic := (cdToMem frame (.array .memory (.array .memory (.bytes .memory) (some 1)) none) 0 1 :
  EM EB [] _).run (L0 EB, sB)

/-- `uint256[2][]` of length 2: the inner arrays hold words 1,2 and 3,4 (a
64-byte stride), the outer array their two references. -/
theorem nested_copy :
    nested.1 = .ok (.val (.memRef rfl (sB.heap.next + 2))) ∧
    words (nested.2.2.heap.get sB.heap.next) = some [some 1, some 2] ∧
    words (nested.2.2.heap.get (sB.heap.next + 1)) = some [some 3, some 4] ∧
    (nested.2.2.heap.get (sB.heap.next + 2)).map (·.1) = some (.array .memory pair none) := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- `uint256[2]` at offset 32: words 2,3. -/
theorem fixed_copy :
    fixed.1 = .ok (.val (.memRef rfl sB.heap.next)) ∧
    words (fixed.2.2.heap.get sB.heap.next) = some [some 2, some 3] := by
  refine ⟨rfl, rfl⟩

/-- The one-word copy keeps its 32-byte stride. -/
theorem flat_copy : words (flat.2.2.heap.get sB.heap.next) = some [some 1, some 2, some 3, some 4] := rfl

/-- A `bool` element holding 2 reverts with no data. -/
theorem dirty_reverts : dirty.1 = .error (.revert []) := rfl

/-- A dynamically encoded element is not inline: the copy is `stuck`. -/
theorem dynamic_stuck : dynamic.1 = .error (.stuck "calldata conversion") := rfl

end Solidity.Source.CalldataStaticCopyControls
