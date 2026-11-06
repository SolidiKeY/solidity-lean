import Solidity.Frontend.Yul.Grammar

/-! Kernel controls for grammar certification only. Syntax acceptance of function
and loop forms does not assert their static legality or execution semantics. -/
namespace Solidity.Yul.Checks.Parsing
open Solidity.Source Solidity.Frontend.Checked

/-- Nonempty assembly crosses the existing Solidity/Yul lexer-mode boundary. -/
theorem expression_block :
    (parseAssembly (ascii "assembly (\"memory-safe\") { pop(add(7,9)) }")).isSome = true := by
  decide +kernel

theorem flags_preserved :
    (parseAssembly (ascii "assembly (\"memory-safe\") { }")).map (·.flags) = some ["memory-safe"] := by
  decide +kernel

theorem function_loop_grammar :
    (parseAssembly (ascii "assembly (\"memory-safe\") { let x := twice(3) function twice(a) -> r { for {} a { a := sub(a,1) } { r := add(r,2) } } }")).isSome = true := by
  decide +kernel

theorem malformed_call_refused :
    (parseAssembly (ascii "assembly (\"memory-safe\") { pop(add(7,)) }")).isSome = false := by
  decide +kernel

theorem unclosed_block_refused :
    (parseAssembly (ascii "assembly (\"memory-safe\") { pop(1)")).isSome = false := by
  decide +kernel

theorem ordinary_statement_not_assembly :
    (parseAssembly (ascii "{} ")).isSome = false := by decide +kernel

end Solidity.Yul.Checks.Parsing
