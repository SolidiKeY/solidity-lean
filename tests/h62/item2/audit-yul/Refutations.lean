import Solidity.Frontend.SolcJson.YulWords
import Solidity.Yul.Checks.ClosedFunctions
import Solidity.Yul.Checks.ClosedPure
import Solidity.Yul.ExternalScope
import Solidity.Yul.GlobalExternal
import Solidity.Yul.ScalarLocals
import Solidity.Yul.WordCells
import Solidity.Yul.Views.MemberStorageDeclaration

/-! H69 intentional-refutation certificates. Each declaration retains the full
original telescope and derives False from it using the unchanged theorem.
Empty intrinsic contexts, disallowed access and fixed/pure profile separation
are negative controls. They are not ordinary success contracts or new exclusions.
-/
namespace H62.AuditYul.Refutations
open Solidity Solidity.Yul Solidity.Yul.Closed

/-- An empty declaration table has no positional declaration. -/
theorem declaration_impossible (d : Solidity.Frontend.YulJson.Declaration []) : False :=
  Solidity.Frontend.YulJson.Words.declaration_impossible d

/-- An empty declaration table cannot have a declaration-backed reference. -/
theorem reference_impossible
    (r : Solidity.Frontend.YulJson.Reference Solidity.Frontend.YulJson.Words.emptyDeclarations) : False :=
  Solidity.Frontend.YulJson.Words.reference_impossible r

/-- Empty function signatures have no intrinsically typed member. -/
theorem no_empty_member {sig : Sig} (i : Member [] sig) : False :=
  Solidity.Yul.Checks.ClosedFunctions.no_empty_member i

/-- Empty external contexts have no intrinsically typed reference. -/
theorem no_external_reference (r : ExternalRef [] false) : False :=
  Solidity.Yul.Checks.ClosedFunctions.no_external_reference r

/-- MLOAD is deliberately outside the pure-word builtin profile. -/
theorem no_memory_builtin (d : WordBuiltinD .mload) : False :=
  Solidity.Yul.Checks.ClosedPure.no_memory_builtin d

/-- Function-visible globals cannot satisfy the external-variable write cap.
This does not prohibit sstore/tstore effects. -/
theorem function_noWrites {rootTypes X decls name suffix ref}
    {scope : ExternalScope rootTypes X}
    (d : ScopedExternalD decls (.function scope) true name suffix ref) : False :=
  Solidity.Yul.ScopedExternalD.function_noWrites d

/-- Global-only external-name resolution cannot carry a write capability. -/
theorem global_noWrites {X decls name suffix ref}
    (d : @GlobalExternalD X decls true name suffix ref) : False :=
  Solidity.Yul.GlobalExternalD.noWrites d

/-- Global projection excludes scalar Solidity VALUE locals. -/
theorem scalar_not_globals {X} (ref : ScalarRef (globals X)) : False :=
  Solidity.Yul.ScalarRef.not_globals ref

/-- Fixed packing is separated from dynamic-length storage arrays. -/
theorem no_dynamic_array {E τ}
    (d : Solidity.Yul.Views.FixedDeclaration E (.array .storage τ none)) : False :=
  Solidity.Yul.Views.FixedDeclaration.no_dynamic_array d

/-- The global projection has no scalar/address/selector word-local cells. -/
theorem wordCell_not_globals {X} (cell : WordCell (globals X)) : False :=
  Solidity.Yul.WordCell.not_globals cell

#print axioms declaration_impossible
#print axioms reference_impossible
#print axioms no_empty_member
#print axioms no_external_reference
#print axioms no_memory_builtin
#print axioms function_noWrites
#print axioms global_noWrites
#print axioms scalar_not_globals
#print axioms no_dynamic_array
#print axioms wordCell_not_globals
end H62.AuditYul.Refutations
