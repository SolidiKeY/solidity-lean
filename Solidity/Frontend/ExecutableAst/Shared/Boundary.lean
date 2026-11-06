import Lean.Data.Json
import Solidity.Syntax

/-! # Executable compiler-AST reader boundary

The callbacks return only the existing surface syntax used by the intrinsic
elaborator. This is not a new statement, term, or verification representation.
Resolved declaration tables may be captured by callbacks; no Lean environment
is an argument. The default reader's deliberate refusals remain errors.
-/
namespace Solidity.Frontend.ExecutableAst.Shared
open Lean (Json)

/-- Concrete extension boundary for memory/reference and control/tuple readers.
Implementations must propagate child failures and preserve evaluation order.
The callbacks are values, not an alternative AST or a proof certificate. -/
structure Reader where
  typeName : Json → Except String (Ty × RawTy)
  expression : Json → Except String RawExpr
  statements : Json → Except String (List RawStmt)
  params : Json → Bool → String → Except String (List (String × Ty))
  specification : Json → Except String FunSpec

end Solidity.Frontend.ExecutableAst.Shared
