# Inline assembly VY1: Yul syntax, checking and word semantics

The `Solidity/Yul/**` library (root `Yul.lean`) and its JSON ingress
`Frontend/SolcJson/Yul*.lean`, from the vy1-words lane.

## Proved

- Words and builtins (`Words`, `WordLaws`, `Builtins`, `CatalogLaws`): word
  operations on `Fin (2 ^ 256)` with zero-divisor and large-shift conventions;
  builtin arities and tiers (`TierPolicy`, `BuiltinUse`, `WordPolicy`).
- Syntax and static checks (`Syntax`, `StatementTags`, `Static`,
  `ExpressionCheck`, `LocalScope`, `FunctionScope`, `Declaration*`,
  `PlacementCheck`, `AssignmentCheck`, `ReservedNames`): an intrinsic AST and
  primitive checkers; `ExpressionCheck.inferExpr_iff` holds for every
  environment and expression.
- Typing and extraction (`BlockTyping`, `ScopedBlockTyping`, `BlockExtract*`,
  `ClosedSyntax`, `Typing*`).
- Closed fuelled execution (`ClosedFunctions`, `ClosedPure`, `ClosedRun`,
  `ClosedHorizon`, `HorizonAdapter`) and a direct tier-A runner
  (`Open*`; `OpenComposition.run_agrees` for all code, policy and state).
- A Lean-only word logic (`WordUpdates`, `WordLogic`, `WordRules`,
  `WordNotation`, `WordAgreement`, `WordCoverage`, `Word{Terms,Branches,Switch,
  Loops,Arguments,Expressions}`) and a raw-cell runner (`WordCells`,
  `WordLocals`, `WordInputs`, `WordAdapter*`). The logic is shallow: `atom`
  takes a Lean predicate, so `rule_sound` in this existence form is weak; the
  concrete rule premise comes from `rule_exists`. Its 20 rules have no rows in
  the rule map yet.
- Source local bridge and statement adapters (`Source*`, `Local*`, `Clean*`,
  `Raw*`): a concrete bool-control slice; `RawSourceAdapter.Adapter.correct`
  is an obligation the caller supplies, and `SourceBoundary` proves only
  impossibility results. This is not a general P16 Source embedding.
- `Checks/**`: kernel controls, including integer-oracle vectors
  (`Checks/Arithmetic`, `Checks/Shifts`; finite tests, not universal opcode
  agreement). `WordPrint` holds the printers; nothing imports it yet.

## Open

General Source embedding (P16), agreement of the word operations with
`Evm.Machine` (signed operations), rule-map rows for the Yul rules, a deep
word logic, the vector generator and the JSON fixtures.
