import Solidity.Syntax.Elab.Values

/-! Slice element copies expand only into existing, intrinsically checked
memory allocation, loops and assignments. No memory alias is used as a copy. -/
namespace Solidity
open Semantics
variable [FreshNames]

/-- Copy a slice element. A fixed primitive row gets a fresh object on every
outer iteration, including when two source rows share a memory identity.
`ws` is rooted at the outer array, hence the row starts at `[]`.
Other reference shapes keep a named refusal until their deep copy is supplied. -/
def sliceElementCopy (E : Ty) (ws : List (String × Nat))
    (source target : RawExpr) : ElabM (List RawStmt) := do
  match E with
  | .prim _ => pure [.assign target source]
  | .ref R@(.fixed (.prim _) n) =>
    let row := toString (← freshCapture "mv")
    let i := toString (← freshCapture "se")
    pure [
      .declMemory (rawTyW ws (.ref R) "[]") row none,
      .decl (.named "uint") i (some (.num 0)),
      .whileLoop {} (.binop .lt (.name i) (.num n)) [
        .assign (.index (.name row) (.name i)) (.index source (.name i)),
        .assign (.name i) (.binop .add (.name i) (.num 1))],
      .assign target (.name row)]
  | .ref _ => throw "sliceReferenceCopyUnsupported: a slice reference element needs a fixed primitive row; other reference shapes are refused"

end Solidity
