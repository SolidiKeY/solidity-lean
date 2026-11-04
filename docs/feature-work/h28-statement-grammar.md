# H28 statement grammar — work in progress

Pinned base: `6f3eedf0788ee1f8a3bcf230558c712ecdca04d5`.
Branch: `codex/solidity-h28-sol-20261104/statement-grammar`.
Repository: `/workspace/solidity-lean`.
Exclusive scope is the StatementGrammarH28 namespace, this document and
`tests/h28-sol/statement-grammar/`. Upstream inputs are unchanged.
Local registration is in the namespace's `registration.tsv`; shared roots and
module maps remain integrator-owned.

## Inventory

The pinned grammar is `tests/upstream/grammar-0.8.38/SolidityParser.g4`,
lines 454–543. Syntax is `Solidity/Source/Syntax.lean`, lines 371–402;
yield is `Solidity/Frontend/Checked/Print.lean`, lines 465–531;
parser is `Solidity/Frontend/Checked/Parser.lean`, lines 586–770.

| Grammar clause | Existing Syn constructors | Boundary / contextual condition |
| --- | --- | --- |
| statement: block | blockStmt, block | balanced braces; item list can be empty |
| simpleStatement | simpleStmt | trailing semicolon |
| variableDeclarationStatement | declVar, declTuple | optional initializer for one variable; required tuple initializer; leading/interior/trailing holes |
| expressionStatement | exprStmt | expression atom followed by semicolon |
| ifStatement | ifStmt | absent/present else; nearest open if |
| forStatement | forStmt | independently optional init/condition/update; two semicolons and closing paren; loop body context |
| whileStatement | whileStmt | condition parentheses; loop body context |
| doWhileStatement | doWhile | body, while, parenthesized condition, semicolon; closes dangling-if path |
| continueStatement | continueStmt | loop context only; semicolon |
| breakStatement | breakStmt | loop context only; semicolon |
| tryStatement | tryStmt | returns list empty/nonempty; braced body; mandatory first catch, remaining catch list |
| catchClause | catchPlain, catchSig | absent signature or optional name plus mandatory first parameter and remaining list; braced body |
| returnStatement | returnStmt | absent/present expression; semicolon |
| emitStatement | emit | path atom, positional/named call arguments, semicolon |
| revertStatement | revert | contextual identifier revert; path atom, call arguments, semicolon |
| assemblyStatement | assembly | optional evmasm dialect; empty/nonempty flag list; Yul braces/list; existing profile exclusion retained |
| block repetition | nil, cons, stmtItem | arbitrary indexed item list |
| uncheckedBlock | uncheckedItem | outside unchecked only; inner unchecked context set true |
| grammar options | none, some | existing category-indexed option representation |

`Syn.openIf` propagates through the else branch of an if with else, through
for/while bodies, and stops at all other roots (including do-while and
blocks). An if without else is open regardless of its then branch.
`Syn.precNode` forbids an else-bearing if whose then branch is open.
No expression uniqueness claim (SOL-EU) is in scope. Lexical identifier
validity and existing layout and precedence contracts are not weakened.

## Queue and acceptance status

1. Inventory and intrinsic shapes: in progress, not accepted.
2. Balanced token/list splitting, nearest-else and token root discrimination:
   pending. Shape discrimination alone is not token discrimination.
3. Parse/yield uniqueness and syntax-derived sufficient parser fuel: pending.
   No assumed successful parse may discharge completeness.
4. Constructor-complete kernel controls, solc 0.8.38 positive/negative fixtures,
   scope-complete acceptance, finder/skeptic reviews, final gates and seal:
   pending.
Backfill block/list and fuel strengthening: pending.

`Shape.lean` defines a finite root observation over existing indexed Syn,
not a replacement AST. Its inhabited representatives are syntax witnesses,
not solc semantic acceptance witnesses. Required review and verification
results will be recorded before acceptance. No checkpoint or whole-goal PASS
is currently claimed.

## Setup evidence

Clean checkout began on branch work at the exact base. Fetch of master and
of the full base succeeded; origin/master equals the pinned base. Assigned
branch was created at that base without resetting local work. The branch
creation preceded discovery of the writer-lock instructions; subsequent
writes and checks use the prescribed lock.
Actual toolchain: Lean 4.24.0, commit
797c613eb9b6d4ec95db23e3e00af9ac6657f24b; Lake 5.0.0-src+797c613.
The initial KeySort probe printed `Build completed successfully (2 jobs).`
It used a local Docker container capped at 12 GiB, MemorySwap equal to
Memory (zero swap), one CPU and LEAN_NUM_THREADS=1. This cached runtime
probe predates the explicit Lean -j1 wrapper, so RUNTIME_GATE_PASS is not
claimed yet. VM cgroup memory.max is 17179869184 bytes; active swap is zero.
Systemd is offline; bounded Docker is used instead.

## Assembly subinventory and parser dependencies

Assembly retains its existing profile exclusion; this is not a new exclusion.
Its embedded existing constructors are yulBlock, yulLet, yulAssign,
yulExprStmt, yulIf, yulFor, yulSwitch, yulLeave, yulBreak, yulContinue,
and yulFun (eleven yulStmt alternatives), plus yulCase for switch arms.
Bodies are nil/cons lists; switch default and let initializer are none/some.
Yul expression dependencies are yulPath, yulCall, yulLit. These are enumerated
for inventory, not proved covered or unique here. The existing approximation
of Yul grammar constraints in Syntax/Prec is retained. Assembly dialect and
flags, function argument/return names, multiple assignment paths, switch
cases/default and nested blocks remain in the coverage queue.
Non-expression parser dependencies also include typeName, param, varDecl,
callArgs, namedArg, tuple declaration slots, return parameter lists and
catch signatures. They must not be discharged by an expression-atom premise.

## Root-inventory review

Independent read-only finder and skeptic reviews inspected Shape and the
pinned inputs without Lean server use or builds. Both confirmed all thirteen
roots, exact loop-context inhabitation, no replacement AST and no token or
parser overclaim. Confirmed findings were fixed: corrected yield/parser
source ranges, explicitly included trailing declaration holes, and added the
Yul subinventory and non-expression parser dependencies above. These reviews
accept only the narrow root observation, not queue item 1 or the whole goal.

## Checkpoint A: intrinsic root inventory (narrow accepted increment)

Finder and skeptic final read-only verdicts pass the root inventory, root
controls and runtime runner after all confirmed findings were fixed. Neither
reviewer used the Lean server or ran builds. The gate runner now verifies
and copies its external configuration, checks current dependencies before
builds, samples actual Lean arguments/concurrency, retains failure samples,
requires successful cleanup/resource evidence, recursively hashes gate logs,
and stops its exact owned runtime on failure. Cgroup peak is explicitly
container-lifetime evidence, while timed batch gates report command peak RSS.
This infrastructure does not establish any grammar theorem by itself.

RUNTIME_GATE_PASS (runtime only): `python3 tests/h28-sol/statement-grammar/runtime.py
build Solidity.KeySort` exited 0 and printed `Build completed successfully
(2 jobs).` at `/workspace/h28-statement-grammar-evidence/run-1793796373472468514`.
The toolchain is the exact Lean/Lake version above. The copied alternate
configuration supplies -j1; Docker memory.max=12884901888, swap.max=0,
one CPU, LEAN_NUM_THREADS=1 and a 4 GiB VM-headroom guard are enforced.

| Gate | Outcome | Immutable evidence directory |
| --- | --- | --- |
| runtime.py build Solidity.Frontend.StatementGrammarH28.Shape | pass; 0.74s timed wall; peak RSS 405160 KiB | /workspace/h28-statement-grammar-evidence/run-1793796088591632373 |
| runtime.py diag Solidity/Frontend/StatementGrammarH28/Shape.lean | pass, zero errors | /workspace/h28-statement-grammar-evidence/run-1793796395458365607 |
| runtime.py diag tests/h28-sol/statement-grammar/RootControls.lean | pass, zero errors | /workspace/h28-statement-grammar-evidence/run-1793796263843710242 |
| runtime.py gate tests/h28-sol/statement-grammar/RootControls.lean | pass, repository per-file gate exit 0 | /workspace/h28-statement-grammar-evidence/run-1793796404804886016 |

The early Shape build predates the final evidence-runner improvements;
its kernel axiom output remains valid and all source identities are saved.
Each of hasRoot_exists, hasRoot_unique, root_discriminate, root_allowed,
root_inhabited and root_inhabited_iff printed `does not depend on any axioms`.
Their exact public signatures are in Shape.lean, captured by source hash.
These statements concern HasRoot and Root.allowed only; none is a token
uniqueness or concrete parser completeness theorem.

Retained failures: run-1793796125038226546 reports the original RootControls
`decide` free-variable elaboration error, fixed by an explicit closed Root
comparison; run-1793796243391157840 reports an overbroad runtime configuration
validator (`weakLeanArgs` on unrelated library entries), fixed by validating
the applicable Solidity library. Earlier diagnostics with an incorrectly
separated MCP argument list are not used as serial-compliance evidence;
the corrected server and worker both visibly carry -j1. No failed check has
been relabeled PASS. No speed-motivated upstream refactor was made.

The full work queue remains incomplete: intrinsic token-boundary relations,
balanced splitting, open-spine/nearest-else proofs, token root discrimination,
parse/yield uniqueness, syntax-derived parser fuel/completeness, full kernel
variants, solc fixtures, full gates, scope acceptance and sealed final handoff.
Checkpoint A is not queue-wide or whole-goal completion.

## Checkpoint B: open-spine and nearest-else contract

NearestElse.lean defines OpenSpine intrinsically over existing indexed Syn.
The missing-else root, else-branch propagation, for-body propagation and
while-body propagation exactly characterize Syn.openIf for arbitrary syntax.
Block and do-while boundaries are closed for arbitrary bodies. nearestElse_node
uses exactly the existing precNode premise; nearestElse uses existing prec.
This is the local no-capture contract, not attachment-position uniqueness,
token-yield uniqueness, or parser completeness. Expressions are not traversed.

An inhabited kernel control gives distinct outer/inner association trees,
a successful common yield to the explicit tokens
`if (p) if (q) return; else return;`, outer precedence refusal and inner
precedence acceptance. The example is a counterexample to unconditional raw
yield uniqueness; the requested precedence-qualified uniqueness remains open.
All four OpenSpine constructors have inhabited controls; arbitrary blocks and
do-while bodies are tested as closed boundaries.

Finder and skeptic read-only reviews found the Option-equality control needed
a successful-yield witness (equal failures would be insufficient); finder
also requested an elseBranch control. Both fixes were implemented and both
reviewers returned narrow PASS without Lean/server/build use.

| Gate | Outcome | Evidence directory |
| --- | --- | --- |
| runtime.py diag Solidity/Frontend/StatementGrammarH28/NearestElse.lean | pass, zero errors | /workspace/h28-statement-grammar-evidence/run-1793796519850435959 |
| runtime.py build Solidity.Frontend.StatementGrammarH28.NearestElse | pass; 1.34s timed wall; peak RSS 416344 KiB | /workspace/h28-statement-grammar-evidence/run-1793796615688240659 |
| runtime.py diag tests/h28-sol/statement-grammar/NearestElseControls.lean | pass, strengthened controls | /workspace/h28-statement-grammar-evidence/run-1793796735545103488 |
| runtime.py gate tests/h28-sol/statement-grammar/NearestElseControls.lean | pass, repository per-file gate | /workspace/h28-statement-grammar-evidence/run-1793796851761080156 |

Exact axiom output: openSpine_iff depends on [propext, Quot.sound]; nearestElse
on [propext]; nearestElse_node, block_closed and doWhile_closed have no axioms.
All five named dangling controls have no axioms. These are the standard Lean
foundations; no custom axiom, sorry, unsafe or native_decide was introduced.
Exact signatures are in the immutable module/test sources captured by the
input manifests. Retained failed run-1793796482613356211 reports an invalid
attempt to use Bool.and_eq_true as an iff constant; this was fixed by reusing
the existing Syn.prec_root theorem. The failure guard stopped the owned
runtime, which was restarted with the same ID and limits before the retry.

Checkpoint B is accepted only as this local contract increment. Balanced
block/list token splitting, token-root discrimination, attachment-position and
parse/yield uniqueness, compound syntax-derived parser completeness, solc
fixtures and final acceptance remain pending. The full goal remains active.

## Checkpoint C: concrete control-leaf parser coverage

LeafCoverage.lean proves equations of the actual existing stmt parser for
break, continue and return without an expression. Success preserves arbitrary
suffix tokens, reversed layout state and EOF; keyword/semicolon source ranges
are arbitrary. Sufficient fuel comes directly from syntax and the actual
calls: n+1 for break/continue and n+2 for empty return. No successful parse is
assumed. Universal zero-fuel rejection and empty-return fuel-1 rejection show
these leaf bounds are minimal. Outside-loop controls reject break/continue
at the keyword offset; return underfuel reports the semicolon offset after
consuming the keyword. Actual Syn.yield equations connect each manual token
prefix to its corresponding intrinsic constructor and preserve layout.
This is token-parser coverage, not lexer validity, solc acceptance or whole
statement completeness. Expression-bearing return and compound constructors
remain pending.

Finder and skeptic independently reviewed these equations and the inhabited
controls without Lean/server/build use. Finder requested nonempty suffix and
layout/EOF states, both unchecked values, zero-fuel controls and actual yield
connections. Those were added. Both final narrow verdicts pass with no
remaining findings. Controls use a nonempty else suffix, nonempty layout and
nonzero offsets to test preservation and boundary/error positions.

| Gate | Outcome | Evidence directory |
| --- | --- | --- |
| runtime.py diag Solidity/Frontend/StatementGrammarH28/LeafCoverage.lean | pass, zero errors | /workspace/h28-statement-grammar-evidence/run-1793796966865579471 |
| runtime.py build Solidity.Frontend.StatementGrammarH28.LeafCoverage | pass; 0.65s timed wall; peak RSS 398788 KiB | /workspace/h28-statement-grammar-evidence/run-1793796989518189752 |
| runtime.py diag tests/h28-sol/statement-grammar/LeafCoverageControls.lean | pass, zero errors | /workspace/h28-statement-grammar-evidence/run-1793797022103617313 |
| runtime.py gate tests/h28-sol/statement-grammar/LeafCoverageControls.lean | pass; 0.32s timed wall; peak RSS 377904 KiB | /workspace/h28-statement-grammar-evidence/run-1793797045186775409 |

All ten public theorems printed `does not depend on any axioms`: break_coverage,
continue_coverage, empty_return_coverage, break_outside_loop,
continue_outside_loop, empty_return_underfuel, control_zero_fuel, break_yield,
continue_yield and empty_return_yield. Exact signatures and premises are in
the immutable module source, with input hashes in the evidence manifests.
No false target or semantic exclusion has been silently discharged.

## Current queue accounting and next work

| Original obligation | Current evidence / remaining work |
| --- | --- |
| Every statement/block constructor and grammar alternative inventory | recorded, including embedded Yul and non-expression parser dependencies |
| Intrinsic shape/token-boundary relations | intrinsic root and open-spine relations proved; token-boundary relations pending |
| Balanced block/list splitting | pending, including backfill strengthening |
| Nearest-else association | existing local no-capture contract proved; unique attachment/token decomposition pending |
| Simple/block/loop/control token-root discrimination | syntactic root discrimination proved; token-root discrimination pending |
| Parse/yield uniqueness under precedence/layout | pending; SOL-EU excluded; no new expression-uniqueness premise asserted |
| Concrete parser completeness with syntax-derived fuel | break/continue/empty return proved; all other constructors and dependencies pending |
| Constructor-complete kernel controls | narrow root, dangling-else and three leaf controls pass; full variants pending |
| Positive/negative return-expression/unchecked/try variants | pending |
| solc 0.8.38 grammar fixtures | pending; no external solc result claimed |
| Full repository gates and scope-complete acceptance | pending; per-file gates do not replace final gates |
| Finder/skeptic and immutable handoff | narrow A/B/C increments reviewed; complete-assignment review and final seal pending |

Next: balanced block/list token decomposition and token-boundary invariants,
then recursive constructor parser fuel/completeness and remaining controls.
All original constraints, frozen inputs and other owners remain binding. The
persistent goal is not marked complete or replaced. No push, merge or PR.
