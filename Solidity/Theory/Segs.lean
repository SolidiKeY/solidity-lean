import Solidity.Semantics

/-!
# Two paths that part

What the side conditions of the frame rules read of two paths of segments:
whether the read path leaves the written one (`diverges`), and the
segment a length is read at (`lengthSeg`), KeY's `size` member.
-/

namespace Solidity
namespace Theory

open Semantics

/-- The segment a length is read at. -/
abbrev lengthSeg : Selector := .len

/-- The read path leaves the written one: they agree up to some point and
then differ.  Neither a prefix nor an extension diverges — `[]` is a prefix
of everything, which is why both `nil` arms are `false`. -/
def diverges : List Selector -> List Selector -> Bool
  | [], _ => false
  | _ :: _, [] => false
  | a :: p, b :: q => if a = b then diverges p q else true

end Theory
end Solidity
