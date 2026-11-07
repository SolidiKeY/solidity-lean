# Lowering correctness: bounded prior-art study (H117)

## Open question

How do CompCert, CakeML, KEVM and Yul/EVM semantics justify loop lowering with break/continue/return, unchecked arithmetic rewriting and partial or monadic elaborators? Which mechanism can connect our actual `lowerLoops` / `uncheckStmts` to existing G19 proofs without new per-case copies (H112)? This study proposes no interface freeze, exclusion, premise or implementation change.

## Our current state

All repository references below refer to base **a0a9ca15ba35fd6e8d9a9be10e4b6b45dbf45d3e**. Source is read only; sole changed file is this report.

- Solidity/Syntax/Elab/Lower.lean:543: `lowerLoops (rs : Option (List String)) (ss : List RawStmt) : ElabM (List RawStmt)`. Both sides are raw syntax, not the resolved intrinsic Source statements or G19 target `Prog`. It projects `lowerList`'s result after initializing loop flags.
- Solidity/Syntax/Elab/Values.lean:651: `ElabM` is ReaderT over two StateT layers ending in `Except String`: scope, local context/fresh counter and call memo matter. `freshCapture` at :728 increments that counter. Success must be associated with the exact incoming scope/state and output; freshness is an obligation, not alpha equality by wish.
- Solidity/Syntax/Elab/Lower.lean:422,438,484: mutually recursive `partial def lowerList`, `lowerStmt`, `lowerLoop` hide behind the non-partial wrapper. At :450-451 out-of-loop break/continue fail; :457 rejects return without function return slots; :473 rejects jumps in try inside loops. Partiality is not just an error constructor: the proof route must also avoid assuming kernel reduction of opaque partial recursion.
- Solidity/Syntax/Elab/Lower.lean:349-385: `LoopFlags`, `LowerM`, `LoopFlags.flag`, `notAny` manage distinct loop break/continue flags and a nest-shared return flag. At :495-500 effectful while conditions are moved to iteration heads; :512-535 do-while gets a first-iteration flag, continue resets each iteration, updates are guarded by break/return, and invariants acquire flag-typing tautologies. :538 emits the outer return test. A generic simulation needs these control and scope invariants.
- Solidity/Syntax/Elab/Lower.lean:707-736: `partial def uncheckStmts : List RawStmt → Except String (List RawStmt)` recursively rewrites arithmetic, inc/dec and blocks, preserves loop specifications (:728), rejects assignment-inc/dec (:716) and nested checking blocks (:722). The transformation is for the semantics of an unchecked context; it cannot preserve the checked semantics of overflowing input.
- Call sites: Solidity/Syntax/Elab/Arms.lean:829 lowers function loops; :1522 and :1926 lower standalone loops; :2036 runs `uncheckStmts` under an unchecked reader scope before branch elaboration. Solidity/Syntax/Elab/Lower.lean:701 invokes loop lowering before return lowering in modifiers. Thus raw-output equality alone cannot establish the full resolved-source-to-model endpoint.
- docs/audits/proof-coverage.md:150 identifies F3: actual elaborator functions lack correctness linkage. Solidity/Source/Agreement/NormalStatement.lean:6-9 explicitly denies a general inhabited program pair; `NormalLocalsObligation` at :24 only constrains normal primitive locals in one direction, not errors, state, association or termination.
- Solidity/Lowering/G19/AssignmentWhileBreak.lean:12 defines a hand-written `code`; :74 `correct` assumes `ContextMap`, related source locals/target environment, Boolean reflection, Boolean slots and exact slot-map equations. It proves execution at `fuel+3`, target execution, post-local relation and unchanged target globals. It does not invoke the raw elaborator, prove arbitrary loop bodies, equate source journal with target storage, or prove physical gas.
- G19 has 18 `correct` declarations and 18 companion Controls files (36 files). This is bounded semantic evidence, not a total lowering relation. Source/Agreement contains primitive/local composition infrastructure; its normal-result contract retains the missing association explicitly.

### Construct-to-shape map

Paths in the next table are relative to Solidity/Lowering/G19/. Each anchor is the `correct` declaration. A covered shape means the listed fixed family, not its entire syntax constructor.

| Lower construct | Existing shape and anchor | Gap to actual lowering |
|---|---|---|
| while + assignment condition + break | AssignmentWhileBreak.lean:74 | raw lowering/elaboration output association |
| while + continue / reset | AssignmentWhileContinue.lean:86; AssignmentWhileReset.lean:205 | arbitrary body/iteration induction and flag scope |
| while + return | WhileReturn.lean:43 | arbitrary return values and nested control |
| do-while + break/continue/return | AssignmentDoWhileBreak.lean:74; AssignmentDoWhileContinue.lean:76; AssignmentDoWhileReturn.lean:94 | first flag and generic recursion |
| for + break/continue/return | AssignmentForBreak.lean:64; AssignmentForContinue.lean:186; AssignmentForReturn.lean:56 | generic init/update and skipped updates |
| return and suffix control | AssignmentReturnFlag.lean:69; ReturnTail.lean:140; ReturnPair.lean:90 | return-slot binding and full result agreement |
| conditionals / continuation | ConditionalStatement.lean:94; ConditionalSequence.lean:108; ConditionalReturn.lean:63; ConditionalReturnContinuation.lean:54 | compositional link to actual generated guards |
| checked/unchecked blocks | AssignmentBlocks.lean:113 | Boolean assignment blocks only; numeric panic/wrap rewrite uncovered |
| general nested loops, try jumps, arithmetic rewrite | uncovered by a general G19 correctness theorem | distinguish explicit elaborator refusals from missing proofs |

Inventory checkpoint complete; external mechanisms and proposals follow in subsequent checkpoints.
