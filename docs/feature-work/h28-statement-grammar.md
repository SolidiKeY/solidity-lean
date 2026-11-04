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
| Intrinsic shape/token-boundary relations | root/open-spine plus actual-yield BlockBoundary proved; coverage of arbitrary syntax by balanced witnesses pending |
| Balanced block/list splitting | balanced-brace prefixes and lists of braced segments proved; exact Syn block/list yield/layout decomposition proved; arbitrary mixed statement-list token splitting pending |
| Nearest-else association | existing local no-capture contract proved; unique attachment/token decomposition pending |
| Simple/block/loop/control token-root discrimination | syntactic root discrimination proved; token-root discrimination pending |
| Parse/yield uniqueness under precedence/layout | unrestricted intrinsic target refuted, even with InProfile; SG-CEX-01 retained open; other positive uniqueness obligations pending |
| Concrete parser completeness with syntax-derived fuel | control leaves plus arbitrary-length leaf-list blocks/blockStmt/unchecked families proved; unrestricted intrinsic-profile completeness refuted by SG-CEX-01; other constructors/dependencies pending |
| Constructor-complete kernel controls | narrow root, dangling-else and three leaf controls pass; full variants pending |
| Positive/negative return-expression/unchecked/try variants | pending |
| solc 0.8.38 grammar fixtures | pending; no external solc result claimed |
| Full repository gates and scope-complete acceptance | pending; per-file gates do not replace final gates |
| Finder/skeptic and immutable handoff | narrow A/B/C increments reviewed; complete-assignment review and final seal pending |

Next: balanced block/list token decomposition and token-boundary invariants,
then recursive constructor parser fuel/completeness and remaining controls.
All original constraints, frozen inputs and other owners remain binding. The
persistent goal is not marked complete or replaced. No push, merge or PR.

## Checkpoint D: SG-CEX-01 — inhabited flag representation counterexample

The original unrestricted statement-yield uniqueness target is false under
the existing precedence/layout contract, independently of SOL-EU. Existing
assembly flag fields are String, but yield uses ascii, narrowing each Unicode
scalar to UInt8. ASCII A and U+0141 Ł are distinct and both yield byte 65.
FlagCounterexample.lean proves distinct trees, successful identical yields
and prec=true for both. The canonical-rethrow variants also both satisfy the
existing InProfile predicate: its exemption checks the Yul body, not flags.
No Solidity expression subtree occurs in these witnesses.

The exact universally quantified yield-uniqueness targets, with and without
InProfile, are refuted in kernel-checked theorems. The actual stmt parser
normalizes the empty-body token input to ASCII for every fuel n+2, preserving
arbitrary suffix/layout state. A separate flag-prefix factor leaves Yul
parsing opaque and proves that no fuel and no output state can recover the
Unicode canonical-rethrow tree. The public
not_profile_statement_parser_complete refutes even existential-fuel recovery
of every existing InProfile/prec/successful-yield intrinsic tree. No assumed
successful body parse is used.

These exact intrinsic targets remain OPEN/REFUTED in the original ledger;
no producer repair, new premise, exclusion or weakening was introduced.
The existing non-ASCII SOURCE-token refusal is retained (frontend-parse.md,
lines 318–321; Parser.strArg). It does not constrain arbitrary existing Syn
String fields, prec or InProfile, and does not invalidate the counterexample.
This is not a claim of ambiguous accepted source bytes, whole-source parse
failure or solc semantic validity of unknown assembly flag A. InProfile is
syntax exclusion, not type/semantic checking. The controls explicitly retain
non-ASCII UTF-8 and empty-token refusals and positive ASCII decoding.

Finder and skeptic independently reviewed the representation collision,
profile witnesses, exact universal targets, opaque-body proof and controls,
without Lean/server/build use. Both final narrow verdicts pass. The skeptic's
wording correction was applied: only the flag prefix is asserted to decode
to ASCII in any successful canonical-rethrow parse.

| Gate | Outcome | Evidence directory |
| --- | --- | --- |
| runtime.py diag Solidity/Frontend/StatementGrammarH28/FlagCounterexample.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793799120982271358 |
| runtime.py build Solidity.Frontend.StatementGrammarH28.FlagCounterexample | pass; 2.94s timed wall; peak RSS 488552 KiB | /workspace/h28-statement-grammar-evidence/run-1793799159296682838 |
| runtime.py diag tests/h28-sol/statement-grammar/FlagCounterexampleControls.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793798950472579702 |
| runtime.py gate Solidity/Frontend/StatementGrammarH28/FlagCounterexample.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793799223003714422 |
| runtime.py gate tests/h28-sol/statement-grammar/FlagCounterexampleControls.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793799226244431944 |

Exact axiom signatures: flag_prefix_factor depends on [Quot.sound];
flag_profile_unicode_no_fuel and not_profile_statement_parser_complete depend
on [propext, Quot.sound]. All twelve other printed counterexample theorems
have no axioms. These are existing Lean foundations, not new axiom declarations.
Exact public statements and input identities are saved in the module and
run manifests. Source.Ctor replays two baseline unused-simp warnings, outside
this lane; producer files were not edited.

Retained failure: run-1793797683973857099 exhausted the unchanged 200000
heartbeat budget while directly reducing the separate ASCII canonical-body
success equation at fuel n+6. That success-bound proof remains unproved; it
is not needed by the checked no-fuel result. Prefix proof attempts in
run-1793797867568143994 and run-1793797951487495638 failed elaboration. The
checked proof instead rewrites the existing stmt equation and keeps the Yul
body parser opaque. No proof budget was raised and no failed run was relabeled.

Coordinator update: origin/master was fetched and remote-verified at
b419c3cf4f642ae519b66bebc26cdf2f7cf93574. This branch and its input versions
remain based on 6f3eedf0788ee1f8a3bcf230558c712ecdca04d5; no merge/reset occurred.
The published new backend/Yul interfaces are unrelated to these statement
proofs, so no duplicate producer or new dependency was introduced.

The authorized balanced block/list and fuel backfill continues. Full queue
acceptance, remaining constructor coverage/controls, fixtures and final gates
are unfinished. The frozen persistent goal is not marked complete.

## Checkpoint E: balanced block/list decomposition backfill

Balance.lean proves a brace-scanner frame theorem for arbitrary depth and
suffix, unique content/suffix splitting of balanced braced prefixes, and
unique decomposition of arbitrary-length lists of balanced braced segments.
BraceBalanced is a token predicate, not an AST. BlockBoundary is intrinsically
indexed by the existing Syn block and its actual yield and input/output
layouts. The syntax-indexed splitting theorem concludes token-body and suffix
equality, not equality of trees deriving those tokens.

YieldSplit.lean proves exact decomposition and recomposition of existing
Syn block and list yields, for arbitrary syntax/categories and layouts. List
splitting exposes head token segments, tail segments and the exact intermediate
layout N between input L and final M. A successful block yield contains one
braced flattened item segment with the same final layout as its item list.
Balanced actual item yields produce an intrinsic BlockBoundary witness.
No parser success is assumed in these grammar-yield equations.

This is a narrow backfill increment: balancing of every arbitrary expression
atom, coverage of all Syn blocks by BlockBoundary, and token splitting of
mixed statement lists are STILL OPEN. Per-part balance remains an explicit
premise; it is not silently supplied by a successful parser or confused with
SOL-EU. The original arbitrary-syntax obligation is not marked complete.

Controls include nonempty return blocks, nested blocks and unchecked blocks
in existing indexed contexts, arbitrary scanner suffixes, and rejection of
an early closing brace despite equal total brace counts. Actual string atoms
exercise L→N→M with two fragment choices and a nonempty residual layout.
String bytes 123/125 remain string tokens, not punctuation braces. Invalid
fragment lengths and empty fragment choices fail. No successful yield is
mocked. All witnesses are existing Syn values.

Separate read-only finder and skeptic reviews pass the narrow proofs and
controls, without Lean/server/build use. Finder requested nonempty/nested
intrinsic controls beyond the empty witness; those were added. Both reviewers
confirmed the precise limits on universal syntax coverage and mixed lists.
The final local unused-simp warning in the layout control was removed.

| Gate | Outcome | Evidence directory |
| --- | --- | --- |
| runtime.py diag Solidity/Frontend/StatementGrammarH28/Balance.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793798392749704798 |
| runtime.py build Solidity.Frontend.StatementGrammarH28.Balance | pass; 0.65s timed wall; peak RSS 409936 KiB | /workspace/h28-statement-grammar-evidence/run-1793798440871849495 |
| runtime.py diag Solidity/Frontend/StatementGrammarH28/YieldSplit.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793798772789829921 |
| runtime.py build Solidity.Frontend.StatementGrammarH28.YieldSplit | pass; 11.65s timed wall; peak RSS 529952 KiB | /workspace/h28-statement-grammar-evidence/run-1793798972971418619 |
| runtime.py diag tests/h28-sol/statement-grammar/BalanceControls.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793798935841289274 |
| runtime.py diag tests/h28-sol/statement-grammar/YieldSplitControls.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793799351873943685 |
| runtime.py gate Solidity/Frontend/StatementGrammarH28/Balance.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793799394523501932 |
| runtime.py gate Solidity/Frontend/StatementGrammarH28/YieldSplit.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793799395302199855 |
| runtime.py gate tests/h28-sol/statement-grammar/BalanceControls.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793799406518489970 |
| runtime.py gate tests/h28-sol/statement-grammar/YieldSplitControls.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793799407296252208 |

Exact axiom outputs for Balance: balanced_scan_frame, close_after_balanced and
unmatched_close_not_balanced use [propext]; balanced_braced_split,
balanced_braced_list_unique and block_boundary_split use [propext, Quot.sound];
balanced_flatten and empty_block_boundary have no axioms. For YieldSplit,
block_yield_decompose and list_yield_cons_decompose use [propext, Quot.sound];
block_yield_map, list_cons_yield_bind, block_yield_of_items, list_yield_cons_of
and block_boundary_of_items have no axioms. These are existing Lean foundations;
there are no new custom axioms or trust shortcuts. Exact signatures, commands,
exits, timings, RSS, source hashes and control axiom outputs are in the sealed
source/evidence. No speed-motivated upstream refactor was made.

Retained failures: run-1793798115614860910 used the unavailable List.Forall
name; the equivalent explicit member-wise proposition is now used.
run-1793798515617629097, run-1793798600656417495 and
run-1793798711211803233 failed attempts at definitional monad equality. The
checked proof first rewrites the existing yield equation, exposes Option
binds and splits at the exact intermediate layout. The layout control's
run-1793799056008112752 failed because an empty-tail membership branch had
not simplified; that was fixed and checked. No failed run is hidden or PASS.

Remaining original work includes arbitrary syntax/atom boundary coverage,
mixed statement-list decomposition, nearest-else attachment-position and
remaining root/conditional uniqueness results where independent of SOL-EU,
remaining constructor fuel/coverage and controls, solc fixtures, full gates,
full-scope reviews/acceptance and final handoff. SG-CEX-01 remains OPEN/REFUTED;
no premise or producer is changed to make it disappear. The existing goal
continues with these obligations, not a replacement goal or VM.

## Checkpoint F: syntax-derived control-block and list-loop fuel

BlockLeafCoverage.lean defines LeafItems as a relation on existing indexed
Syn item lists and their tokens. It admits arbitrary list lengths of empty
return, break and continue, retaining the intrinsic loop/unchecked contexts.
It introduces no replacement AST. It is explicitly not the whole statement
grammar. Generated internal locations are zero; arbitrary source-position
or lexer correctness is not claimed. Arbitrary suffix tokens, layout and EOF
are preserved by the successful coverage equations.

The proof derives token length = itemCount + itemCount from syntax. The actual
many loop's token-derived fuel is sufficient for itemCount parsing steps and
the necessary stopping step. With exactly itemCount iterations, the existing
manyAux parser fails at the closing brace with no progress, universally over
all represented lists. Every operational success premise in the helper
composition lemmas is discharged by concrete existing-parser leaf equations.
Final completeness theorems assume only LeafItems, never successful parsing.

Uniform sufficient nesting fuel is n+4 for a block and n+5 for its blockStmt
or unchecked-item wrapper. These are sufficient bounds, not asserted minimal
nesting bounds. Arbitrary list length is handled by the independently proved
many iteration bound. Nested unchecked input is refused for every positive
item fuel. The relation also derives actual Syn list yields, block yields
and successful block toks [], connecting parser inputs to the existing yield
specification instead of mocking a successful parse.

Controls contain arbitrary-count and 80-item return lists, mixed return,
break and continue lists in both unchecked states, blockStmt and unchecked
wrappers, nonempty else suffix/layout/EOF, universal stopping-step underfuel,
actual yields and nested-unchecked refusal. Separate read-only finder and
skeptic reviews pass the complete narrow source/control increment. Neither
used Lean/server/builds. The skeptic requested the actual-yield connection;
it was added and both reviewers accepted it. The restriction to this leaf
relation and zero-offset inputs remains explicit.

| Gate | Outcome | Evidence directory |
| --- | --- | --- |
| runtime.py diag Solidity/Frontend/StatementGrammarH28/BlockLeafCoverage.lean | pass, final yield/underfuel additions | /workspace/h28-statement-grammar-evidence/run-1793800827348532515 |
| runtime.py build Solidity.Frontend.StatementGrammarH28.BlockLeafCoverage | pass; 4.08s timed wall; peak RSS 510844 KiB | /workspace/h28-statement-grammar-evidence/run-1793801075967086471 |
| runtime.py diag tests/h28-sol/statement-grammar/BlockLeafCoverageControls.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793801537126732798 |
| runtime.py gate Solidity/Frontend/StatementGrammarH28/BlockLeafCoverage.lean | pass, no local warnings | /workspace/h28-statement-grammar-evidence/run-1793801699935772492 |
| runtime.py gate tests/h28-sol/statement-grammar/BlockLeafCoverageControls.lean | pass, no local warnings | /workspace/h28-statement-grammar-evidence/run-1793801704641692241 |

Exact public signatures and all 24 printed theorem axiom sets are in the
source and gate output. many_aux_none, many_aux_cons, many_aux_cons_error,
uncheckedInput_eq and leaf_step_stop have no axioms. blockInput_eq uses
[propext]. stmt_block_prefix, item_unchecked_prefix,
unchecked_nested_refused and the three concrete leaf_step success theorems
use [Quot.sound]. The remaining printed theorems use [propext, Quot.sound].
Only existing Lean foundations occur; no custom axiom, unsafe, native_decide
or raised maxHeartbeats was introduced.

Retained failures: run-1793799901568202090 attempted induction on a fixed
indexed Syn category; the checked inverse theorem uses indexed recursion.
run-1793800030559517318 exposed generated-equation and stateful-option-match
issues; the checked proof rewrites the generated equations and retains the
stateful matcher until its result is known. run-1793800253330800174 lacked
an explicit Except type in a change expression. run-1793800505573602267 had
uninstantiated constructor/projection patterns and a flattened-list equality;
explicit witnesses, typed projected equalities and append_nil fixed those.
run-1793801452731473003 required explicit itemCount equations in the concrete
three-item underfuel control. All failed runs remain visible.

External fixture setup only: the official soljson-v0.8.38+commit.1835d247.js
was retrieved and SHA-256 verified as
6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390,
matching the existing repository pin. In the same bounded runtime it reports
0.8.38+commit.1835d247.Emscripten.clang; Node is v24.19.0. No solc grammar
fixture PASS is claimed yet. The next work is constructor-complete kernel
controls and these pinned external fixtures, then remaining boundary/root/
attachment results and full gates/reviews. General compound completeness,
mixed-list splitting, all-Syn balance and scope acceptance remain open.
SG-CEX-01 is still OPEN/REFUTED and all original constraints remain binding.


## Checkpoint G: constructor-complete finite parser controls

FixtureData.lean, FixtureControls/Case00 through Case44 and
ConstructorControls.lean certify 45 concrete checked-source cases using
`decide +kernel`, with no native computation in the proof chain. The checked
observer selects function f bodies, excluding helper g, and inspects existing
intrinsic Syn nodes. Its structurally recursive list observer has fuel 64;
exhaustion returns no tags and cannot fabricate coverage. This is a finite
fixture observer, not a universal traversal completeness assertion.

The manifest enumerates every fixture, its source hash, checked-parser
acceptance/profile expectations, exact constructor obligations and solc
expectations. The 40 required constructors include all statement roots,
block/item/simple/catch alternatives, list/option alternatives and all Yul
statement/block/expression forms. check-fixture-sync.py checks all 45 source
strings against Lean, the exact case certificates/imports/list and unique
40-constructor coverage. statement_fixture_constructor_inventory alone is
metadata coverage; statement_constructor_fixture_witnesses connects it to
the actual closed-case certificates: for every required Ctor, an accepted
checked parser tree exists with that constructor in its observed f body.
No successful parse premise remains in that final theorem. It does not
assert AST equality, universal syntax coverage or expression uniqueness.

There are 28 positive cases, 14 grammar/context refusals and three semantic
refusals accepted by the checked parser but rejected by solc. The latter
require exact TypeError codes 8863 (void valued return), 6777 (empty valued
return) and 3542 (unknown catch name). Positive variants include nested
blocks, declarations/initializers/tuple holes, expression statements, both
if alternatives and nearest dangling else, empty/full for, while/do, both
return alternatives, break/continue, unchecked, positional/named emit and
revert, try without/with returns and plain/signature catches, generic and
memory-safe assembly, canonical rethrow and comprehensive Yul forms.
Negative controls include outside-loop controls, nested unchecked, direct
unchecked if/for bodies, stray/double else, missing delimiters/catches,
empty catch parameters, invalid Yul switch and unknown assembly dialect.
All files and exact expectations are enumerated in fixtures/manifest.json;
there are no ignored or sampled cases.

The pinned external compiler is solc-js
0.8.38+commit.1835d247.Emscripten.clang, SHA-256
6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390,
with Node v24.19.0. All 45 external expectations pass, including AST checks
for tuple holes, inner-else association, catch signatures and all 15 required
Yul AST node kinds. These compiler results are external tests, not Lean
proofs. Generic assembly fixtures have profile=false; the canonical rethrow
has profile=true. Existing profile refusals are preserved.

| Gate | Outcome | Evidence directory |
| --- | --- | --- |
| runtime.py diag Solidity/Frontend/StatementGrammarH28/ConstructorControls.lean | pass, final actual constructor witness theorem | /workspace/h28-statement-grammar-evidence/run-1793805946662140520 |
| runtime.py build Solidity.Frontend.StatementGrammarH28.ConstructorControls | pass, imports all 45 kernel certificates | /workspace/h28-statement-grammar-evidence/run-1793806125552223750 |
| runtime.py gate Solidity/Frontend/StatementGrammarH28/ConstructorControls.lean | pass; no warnings | /workspace/h28-statement-grammar-evidence/run-1793806147002093821 |
| runtime.py gate Solidity/Frontend/StatementGrammarH28/FixtureData.lean | pass; no warnings | /workspace/h28-statement-grammar-evidence/run-1793806156523464168 |
| runtime.py solc tests/h28-sol/statement-grammar/solc-fixtures.mjs | pass; all 45 expected outcomes | /workspace/h28-statement-grammar-evidence/run-1793805232591644267 |
| check-fixture-sync.py | pass; all 45 cases and 40 obligations | saved checkpoint G inventory |

Every individual certificate was built serially; the saved G inventory lists
the passing run for each Case00..44 and all observed theorem axiom sets.
The 45 closed-case certificates use propext (as recorded by actual
#print axioms output); the constructor metadata inventory has no axioms.
statement_fixtures_all_checked uses propext. checked_fixture_observes
and statement_constructor_fixture_witnesses use propext and Quot.sound.
There are no custom axioms, unsafe/native_decide or raised heartbeats.

Retained failed experiments include the monolithic corpus headroom refusal
(run-1793802814787171168), an indexed well-founded observer elaboration
failure (run-1793803110925222515), Case00 checks before the observer was
replaced by structural Nat recursion (run-1793803376063463918 and
run-1793803849861886512), and the intermediate aggregate conjunction
projection error (run-1793805858692001358). The monolithic source and its
hash are retained. A diagnostic-only #eval was never used as a proof.
Cache hints used read-only POSIX_FADV_DONTNEED, without deleting data.
The Case13 runtime false refusal (run-1793804297065249712) observed a
completed Lean zombie; the guard now excludes stat Z only, retains live
-j1 checks and the original failed receipt, and Case13 was rerun successfully.
No proof budget changed. Splitting the kernel corpus and structural observer
keeps individual checks bounded; no speedup percentage is claimed.

The solc runner now seals setup failures as well as case failures, copies
its own source and hash, and is invoked inside the same 12 GiB/no-swap,
single-CPU guarded runtime. Its deliberate wrong-compiler-hash control exits
1 with status=fail and sealed results at
/workspace/h28-statement-grammar-evidence/solc-negative-setup-1793805407280692935;
the outer control records that rejection as expected, never relabeling the
failed inner gate. Runtime input hashes include recursive fixture/module
paths. Registration includes all 47 new modules locally; shared roots and
module maps remain untouched under the assignment.

Separate read-only finder and skeptic reviews pass the finite G increment,
including actual existential parser witnesses, all-case synchronization,
registration, failure sealing and resource guard behavior. Neither used
Lean/server/builds. Their findings about missing local registration and
unsealed solc setup failures were fixed; suggested exact list synchronization
and semantic error codes were also added.

This checkpoint completes finite constructor controls and pinned external
fixtures only. Arbitrary syntax/atom balance, mixed-list splitting,
nearest-else attachment-position and token-root/conditional uniqueness,
remaining universal compound fuel coverage, full repository gates and
whole-scope acceptance/reviews remain unfinished. SG-CEX-01 remains
OPEN/REFUTED. The persistent original goal continues without a new premise,
producer change, exclusion, VM or replacement goal.


## Checkpoint H: unique intrinsic nearest-else positions

ElsePosition.lean refines the existing openIf contract with NearestSlot,
a relation indexed by an existing Syn statement and a list of observed
statement edges. No replacement syntax or expression traversal is introduced.
The five relation alternatives are a missing-else root whose then branch is
closed, descent through an open then branch, descent through an existing
else branch, a for body and a while body. Unlike OpenSpine.missing, the root
alternative cannot stop before a nearer exposed missing else inside then.

nearestSlot_unique proves arbitrary two related paths equal. slotOfOpen
constructively handles every statement constructor; nearestSlot_exists_iff
and nearestSlot_unique_exists give existence exactly when openIf=true and
unique existence respectively. prec_else_no_then_slot proves the existing
prec=true contract forbids every then-branch slot at an else-bearing if.
These are universal results for intrinsic statement positions, independent
of expression uniqueness. They do not prove token-level association or parser
uniqueness, and do not imply that every arbitrary raw Syn tree satisfies prec.

Controls inhabit all five relation constructors, including a for/while/then
path. A two-missing-if tree has nearest path [thenBranch], and the outer []
path is proved impossible. Closing the inner if exposes the outer root slot;
an existing else redirects the path into its else branch. Arbitrary block
and do-while bodies hide internal slots, and the wrong outer attachment is
kernel-checked to fail the existing precedence contract. All relation clauses
and all 13 statement roots are covered by the universal source definitions
and proofs; these are not only finite fixture assertions.

| Gate | Outcome | Evidence directory |
| --- | --- | --- |
| runtime.py diag Solidity/Frontend/StatementGrammarH28/ElsePosition.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793806453197594452 |
| runtime.py build Solidity.Frontend.StatementGrammarH28.ElsePosition | pass; 2.04s timed wall, RSS 429144 KiB | /workspace/h28-statement-grammar-evidence/run-1793806489384777736 |
| runtime.py diag tests/h28-sol/statement-grammar/ElsePositionControls.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793806540601075377 |
| runtime.py gate Solidity/Frontend/StatementGrammarH28/ElsePosition.lean | pass, no warnings | /workspace/h28-statement-grammar-evidence/run-1793806563294152781 |
| runtime.py gate tests/h28-sol/statement-grammar/ElsePositionControls.lean | pass, no warnings | /workspace/h28-statement-grammar-evidence/run-1793806577242791476 |

nearestSlot_unique has no axioms. The existence equivalence, unique existence
and precedence exclusion use only propext and Quot.sound. Exact signatures
and all printed control axiom sets are saved in the gate logs. No custom
axiom, unsafe/native_decide, expression premise or budget raise was added.
The first attempt (run-1793806432901494391) did not generalize the competing
path in the uniqueness induction; the final proof generalizes it explicitly.
The failed receipt is retained. Separate read-only finder and skeptic pass
source and all controls, without using Lean/server/builds. Registration is
local only.

Checkpoint G also has exact-head passing constructor and KeySort gates at
adcaa8105854cfc09e5536890912a1530d020a7b, with actual Lean 4.24.0 and
Lake 5.0.0-src+797c613. Its runtime-g.json records permitted KeySort PASS
before RUNTIME_GATE_PASS. The invalid KeySort path setup refusal at
run-1793806282988676952 is retained; the verified Solidity/KeySort.lean
passed at run-1793806303988860870. That is a per-file runtime receipt, not
a full repository gate claim.

Remaining work: arbitrary syntax/atom balance, mixed-list splitting,
token-root discrimination and token-level conditional uniqueness/association,
remaining universal compound fuel coverage, full repository gates,
whole-scope reviews/acceptance and final handoff. The intrinsic attachment
position obligation is now proved; its token-level counterpart is not.
SG-CEX-01 remains OPEN/REFUTED, and the original persistent goal stays active.
