# H28 statement grammar — work in progress

Pinned base: `6f3eedf0788ee1f8a3bcf230558c712ecdca04d5`.
Branch: `codex/solidity-h28-sol-20261104/statement-grammar` (Codex, to checkpoint X
and the e6849d3b rebase); since 2026-11-05 the moved lane
`cloud/moved4-20261105/statement-grammar`, started from master
`aec9adf1ad8666a7e591e42a537069a93dc858cb` (see "Moved lane" at the end).
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

1. Inventory and intrinsic shapes: constructor inventory and intrinsic root/
   nearest-position results proved; final whole-scope acceptance pending.
2. Splitting/root/association: recursive block/control balance, mixed boundary
   splitting, intrinsic nearest position and non-simple token roots proved.
   Arbitrary statement/atom brace balance and arbitrary block-prefix splitting
   are proved under H31. All statement roots, including contextual simple/revert, are distinguished
   under the original precedence contract. Token-level association remains in progress.
   The former Q-ATOM hold is resolved.
3. Parse/yield: recursive block/control completeness and actual yield uniqueness
   proved; fixed-Boolean/empty-for compound coverage proved. Broad uniqueness/
   profile completeness are refuted by SG-CEX-01/SG-CEX-02 and retained OPEN/REFUTED.
   General remaining statement composition is in progress under H31; no successful parse
   is assumed to discharge completeness.
4. All 45 kernel and pinned solc fixture controls pass with 40 constructor
   obligations. Per-checkpoint finder/skeptic reviews and sealed handoffs are
   complete through M. Full repository gates and whole-scope acceptance remain
   pending; the shared-roots gate fails until central integration.
Assigned block/list/fuel backfill has been strengthened through K–M, including
arbitrary width/depth, exact actual yields, balance and fragment uniqueness.
The complete original assignment is not accepted or marked done.

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


## Checkpoint I: fixed token-root discrimination

TokenRoot.lean proves statement_fixed_head for every non-simple intrinsic
statement root and arbitrary successful actual Syn.yield, layout and residual
layout. Expression subtrees remain opaque computations; the proof derives
heads from the existing stateful printer clauses via PrEnsures pure/bind
lemmas. The fixed-head map has 12 distinct tokens: left brace, if, for,
while, do, continue, break, try, return, emit, identifier "revert", assembly.
Its thirteenth/simple entry is none. Contextual revert is deliberately an
identifier, matching the frozen producer rather than inventing a keyword.

nonSimple_root_of_equal_prefix proves root equality for arbitrary intrinsic
contexts, layout choices/residuals and suffix tokens whenever the successful
yielded token prefixes plus suffixes agree. Its two non-simple hypotheses
are explicit restrictions of this proved fragment; they do not replace or
weaken the still-open original simple-root obligation. It proves root equality,
not subtree equality, expression uniqueness or whole-language uniqueness.
No expression-uniqueness or successful-parser premise is introduced.

All 12 fixed roots have inhabited actual successful yield controls, with an
exact constructor inventory checked against the control list. An arbitrary
suffix/layout break-versus-continue theorem rejects equal prefixes. A concrete
nonempty residual fragment layout and else suffix retain the fixed return
head. A simple expression named "revert" and an actual revert statement
both yield the identifier head; their complete displayed streams differ.
This negative control rejects first-token-only simple/revert discrimination,
not full-stream uniqueness. General simple-root comparison remains open.

| Gate | Outcome | Evidence directory |
| --- | --- | --- |
| runtime.py diag Solidity/Frontend/StatementGrammarH28/TokenRoot.lean | pass, final prefix theorem | /workspace/h28-statement-grammar-evidence/run-1793806842008128609 |
| runtime.py build Solidity.Frontend.StatementGrammarH28.TokenRoot | pass; 12.50s timed wall, RSS 538796 KiB | /workspace/h28-statement-grammar-evidence/run-1793806895558983375 |
| runtime.py diag tests/h28-sol/statement-grammar/TokenRootControls.lean | pass, final layout control | /workspace/h28-statement-grammar-evidence/run-1793807013740202989 |
| runtime.py gate Solidity/Frontend/StatementGrammarH28/TokenRoot.lean | pass, no warnings | /workspace/h28-statement-grammar-evidence/run-1793807027868193999 |
| runtime.py gate tests/h28-sol/statement-grammar/TokenRootControls.lean | pass, no warnings | /workspace/h28-statement-grammar-evidence/run-1793807052368259455 |

All seven public source theorem axiom sets are empty, as printed by the
actual build/gate. Control signatures/axiom sets are recorded in their gate
log. No new axiom, unsafe/native_decide, expression premise or heartbeat
raise was introduced. The layout control initially failed dotted-token
elaboration (run-1793806968171195222); explicitly naming Tok.kw fixed it.
The failed receipt is retained. Separate read-only finder and skeptic pass
source and controls, including the shared-head limitation, without
Lean/server/builds. The module is locally registered only.

Remaining original work includes arbitrary syntax/atom balance, mixed-list
token splitting, simple-root discrimination, token-level conditional
uniqueness/association, remaining universal compound fuel coverage, full
repository gates and whole-scope acceptance/reviews/handoff. SG-CEX-01
remains OPEN/REFUTED. The persistent goal remains active and incomplete.


## Checkpoint J: mixed self-delimiting block/control splitting

MixedSplit.lean strengthens balanced-block decomposition to arbitrary finite
mixed sequences of balanced braced blocks, unchecked braced blocks and empty
return/break/continue leaves. Chunk is a token-boundary predicate, not an AST.
IntrinsicItemChunks is indexed by existing intrinsic item lists and records
their exact successful yield/layout plus the boundary of every segment.
Its nil/cons construction threads the actual intermediate layout and uses
the existing list-yield composition theorem.

chunk_frame proves a deterministic suffix scanner returns the exact remainder
for every represented segment and arbitrary tail. This proves nonemptiness,
unique prefix/remainder splitting and arbitrary-length mixed token-segment
list uniqueness, including empty/nonempty list cases. intrinsic_mixed_split
transfers the segment conclusion to actual intrinsic item yields across
contexts/layouts. It does not conclude AST equality, parsing success or
general mixed statement-list completeness. Expression-bearing unbraced
statements remain outside this proved fragment; their original obligation
is still open, not replaced by a new exclusion or premise.

The inhabited control is an actual five-item indexed list containing an
empty return, nested block, unchecked block, break and continue. Its yield
is exact for arbitrary residual layout, and controls also exhibit a concrete
nonempty fragment layout and arbitrary suffix. All five boundary alternatives
are inhabited. No resegmentation into different Chunk segments is possible.
Early-close tokens and merged control statements are proved not one Chunk.
A valid valued return is explicitly outside this scanner's empty-return
fragment: its scanner none is not a Solidity grammar or parser refusal.
Both reviewers requested that wording correction and verified the fix.

| Gate | Outcome | Evidence directory |
| --- | --- | --- |
| runtime.py diag Solidity/Frontend/StatementGrammarH28/MixedSplit.lean | pass, final warning fix | /workspace/h28-statement-grammar-evidence/run-1793807614109706221 |
| runtime.py build Solidity.Frontend.StatementGrammarH28.MixedSplit | pass, final source | /workspace/h28-statement-grammar-evidence/run-1793807633409190259 |
| runtime.py diag tests/h28-sol/statement-grammar/MixedSplitControls.lean | pass, final wording | /workspace/h28-statement-grammar-evidence/run-1793807563037886302 |
| runtime.py gate Solidity/Frontend/StatementGrammarH28/MixedSplit.lean | pass, no warnings | /workspace/h28-statement-grammar-evidence/run-1793807646135234261 |
| runtime.py gate tests/h28-sol/statement-grammar/MixedSplitControls.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793807596879600409 |

The initial build took 0.75s timed wall and RSS 407336 KiB. Exact final timing,
RSS, input hashes and process samples are in the final run directory.
chunk_frame, chunk_nonempty and intrinsic_chunks_cons use propext;
intrinsic_chunks_nil has no axioms. chunk_split, mixed_chunks_unique and
intrinsic_mixed_split use propext and Quot.sound. Exact control axiom sets
and public signatures are in source/gate logs. No custom axiom, budget raise,
unsafe/native_decide, expression uniqueness or parser-success assumption was
introduced. The first source attempt used an unavailable List lemma name
(run-1793807355145339665); the actual core empty-append lemma fixed it.
The first control attempt left an empty-tail membership alternative
(run-1793807505258809796); explicit not_mem_nil/or_false fixed it.
The initial successful source gate retained an unused-binder warning; the
binder was renamed, then diagnostics/build/gate rerun without disabling any
linter. All prior receipts remain retained. Separate read-only finder and
skeptic pass source and inhabited controls without Lean/server/builds.
The module is registered locally only.

Remaining full scope: arbitrary syntax/atom balance, general mixed statement
splitting, simple-root discrimination, token-level conditional uniqueness/
association, remaining universal compound fuel coverage, full repository
gates, whole-scope reviews/acceptance and final handoff. SG-CEX-01 remains
OPEN/REFUTED. This is a completed backfill checkpoint, not whole-goal completion.


## Checkpoint K: recursive intrinsic block parser fuel and balance

NestedCoverage.lean extends the existing arbitrary-length empty-return,
break and continue lists with recursively nested ordinary block items and
intrinsically permitted unchecked block items. NestedItems is indexed by
existing Syn lists, concrete tokens and a syntax-derived depth budget.
Its six constructors are nil, the three leaf-cons forms, blockCons and
uncheckedCons. Ordinary nesting adds three to the child budget, unchecked
nesting adds two, and max joins child and tail budgets. This is a relation
on intrinsic syntax, not a replacement tree. leaf_to_nested includes every
previous LeafItems witness at depth zero.

nested_items_at proves actual manyAux success for every fuel at least d+3,
with arbitrary list lengths. Each child success is derived recursively;
no parser monotonicity or successful parse is assumed by the final coverage
statements. itemCount <= token length independently proves the existing
parser's token-derived many loop fuel sufficient, including its stopping
step. nested_block_coverage proves block success at n+d+4;
nested_block_stmt_coverage and nested_unchecked_coverage prove their wrappers
at n+d+5, for arbitrary excess n and suffix/layout/EOF state. These are
sufficient bounds, not claimed minimal. Internal token locations remain
synthetic zero; arbitrary source-position/lexer adequacy is not proved.

The same relation derives actual flattened list yields, exact block yields
for arbitrary layout, and brace balance. nested_block_boundary combines them
into the existing BlockBoundary relation. Thus concrete parser inputs come
from actual intrinsic yields; no successful parse is mocked or assumed.
Expressions and expression uniqueness are absent from this fragment.

Controls prove towers of arbitrary natural depth n have syntax budget 3*n
and successful block/unchecked-wrapper parses at the corresponding bounds.
An inhabited mixed tree combines a return block and an unchecked block
containing an ordinary block with break and continue, exercising all six
relation constructors and both intrinsic unchecked states. Exact actual
yield, balanced boundary, and nonempty else suffix/fragment layout/EOF15
are retained. Nested unchecked remains refused for every positive item fuel
and arbitrary tower depth. One nested block at fuel3 has a checked nesting
error; this is a specific underfuel example, not minimality of our bound.
The universal syntax lemmas cover arbitrary width as well as depth.

| Gate | Outcome | Evidence directory |
| --- | --- | --- |
| runtime.py diag Solidity/Frontend/StatementGrammarH28/NestedCoverage.lean | pass, final leaf bridge/yield/balance | /workspace/h28-statement-grammar-evidence/run-1793808260451720665 |
| runtime.py build Solidity.Frontend.StatementGrammarH28.NestedCoverage | pass; 2.66s timed wall, RSS 434764 KiB | /workspace/h28-statement-grammar-evidence/run-1793808277516743204 |
| runtime.py diag tests/h28-sol/statement-grammar/NestedCoverageControls.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793808338858253573 |
| runtime.py gate Solidity/Frontend/StatementGrammarH28/NestedCoverage.lean | pass, no warnings | /workspace/h28-statement-grammar-evidence/run-1793808368388471314 |
| runtime.py gate tests/h28-sol/statement-grammar/NestedCoverageControls.lean | pass, no warnings | /workspace/h28-statement-grammar-evidence/run-1793808393175860915 |

All 17 printed source theorem axiom sets are saved in the gate log.
leaf_to_nested, keyword_semi_balanced and nested_tokens_balanced have no
axioms. locatedInput_append uses propext. step_unchecked_of_coverage uses
Quot.sound. The remaining 12 use propext and Quot.sound. Control signatures
and axiom sets are also printed. No custom axiom, unsafe/native_decide,
heartbeat raise, producer change or expression premise was introduced.
Separate read-only finder and skeptic pass source and all controls, without
Lean/server/builds. No mathematical or scope finding remained.

Retained attempts: run-1793807897050297869 exposed indexed nil reduction and
nested monad composition; run-1793807951844514120 confirmed composition was
not definitional. The checked proof separately proves stmt/item results and
retains the stateful bind structure. run-1793808049281093695 needed explicit
nil observation equations. run-1793808155290987961 needed singleton-flatten/
append normalization for unchecked yield. run-1793808318123966475 needed
append_nil in the universal tower witness. All failures remain retained.
The module is locally registered; frozen/shared producer files stay unchanged.

This completes recursive block/control coverage and balance, strengthening
assigned backfill. All-syntax/atom balance, general mixed statement splitting,
simple-root discrimination, token-level conditional uniqueness/association,
remaining compound statement universal fuel coverage, full repository gates
and whole-scope reviews/acceptance remain unfinished. SG-CEX-01 remains
OPEN/REFUTED; the original persistent goal remains active and incomplete.


## Checkpoint L: actual-yield uniqueness of recursive block/control syntax

NestedUnique.lean proves unconditional yield uniqueness within the recursive
NestedItems fragment, independent of SOL-EU. Given two syntax witnesses with
depth budgets d and e, nested_items_token_unique gives both actual block
parser runs a common sufficient fuel d+e+4. The preceding coverage theorem
derives both successes from syntax; determinism of that actual parser then
recovers equality of the original intrinsic item lists. No successful parse
or expression uniqueness is assumed in the final statement.

nested_block_toks proves the canonical actual token yield.
nested_block_derives_iff characterizes the existing Syn.Derives relation
exactly: its words equal the witness's braced tokens. The proof accounts for
the preserved residual layout, so complete toks success requires empty
layout. nested_block_prefix_unique combines balanced-brace splitting with
the common-fuel proof to recover both tree equality and suffix equality,
for arbitrary nested fragment prefixes. nested_block_yield_unique transfers
this to two actual Derives witnesses of one token stream.

These are tree-equality results for the declared recursive control/block
fragment, rather than only root or segment equality. They make no claim
about expression-bearing statements, general dangling-else token association
or whole-language uniqueness. SG-CEX-01 remains independently OPEN/REFUTED.
No original theorem premise or exclusion has been weakened or replaced.

Controls contain an inhabited nonempty nested/unchecked mixed tree and its
actual positive derivation. A universal control recovers that tree from any
represented candidate deriving its tokens. A nonempty else suffix is also
recovered. Separate return and break lists have positive actual derivations
and universally cannot share a yield. Two actual state-threaded yields retain
different residual layouts, while a nonempty residual layout is proved to
make toks return none. Thus neither the positive controls nor the uniqueness
claims depend on an empty or false relation.

| Gate | Outcome | Evidence directory |
| --- | --- | --- |
| runtime.py diag Solidity/Frontend/StatementGrammarH28/NestedUnique.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793808604360768527 |
| runtime.py build Solidity.Frontend.StatementGrammarH28.NestedUnique | pass; 0.54s timed wall, RSS 402776 KiB | /workspace/h28-statement-grammar-evidence/run-1793808640321070746 |
| runtime.py diag tests/h28-sol/statement-grammar/NestedUniqueControls.lean | pass, final negative layout control | /workspace/h28-statement-grammar-evidence/run-1793808745156538439 |
| runtime.py gate Solidity/Frontend/StatementGrammarH28/NestedUnique.lean | pass, no warnings | /workspace/h28-statement-grammar-evidence/run-1793808758438462086 |
| runtime.py gate tests/h28-sol/statement-grammar/NestedUniqueControls.lean | pass, no warnings | /workspace/h28-statement-grammar-evidence/run-1793808768513010504 |

All five public source theorems use only propext and Quot.sound, as printed
in the gate log; exact signatures and all control axiom sets are saved.
No custom axiom, unsafe/native_decide, budget raise, producer interface change
or expression premise was introduced. The negative layout control rewrite
already closed its goal; run-1793808711098957163 rejected the redundant rfl,
which was removed. The failed receipt is retained. Separate read-only finder
and skeptic pass all source/control statements, without Lean/server/builds.
Registration is local only.

Remaining original scope includes all-syntax/atom balance, general mixed
statement splitting, simple-root discrimination, token-level conditional
uniqueness/association, remaining universal compound statement fuel coverage,
full repository gates and whole-scope reviews/acceptance. Recursive block/
control yield uniqueness is now proved, but it is not whole-language
uniqueness. The original persistent goal remains active and incomplete.


## Checkpoint M: Boolean compound coverage with recursive block bodies

BoolCompound.lean proves actual parser equations for explicit Boolean literal
atoms followed by rparen or semi at sufficient expression fuel n+5. This is
a fixed-atom parser observation, not expression uniqueness or general
expression coverage. It then derives syntax-fuel coverage for while,
do-while, empty-header for, and both if alternatives, with arbitrary
NestedItems braced bodies. It preserves loop/unchecked indices, arbitrary
suffix/layout/EOF and the existing zero internal location convention.

The sufficient fuel for while/do/empty-for/no-else-if is n+d+6. For if with
else, the two independently derived body budgets give n+d+e+6. Every child
parser success is discharged by fixed Boolean atom equations or the proved
recursive block coverage; final statements assume no successful parse.
The empty for header covers exactly absent init/condition/update. Compound
bodies are the previously proved recursive block/control fragment, not a
recursive closure containing arbitrary if/loop nodes.

NoFollowingElse states the exact necessary token observation for preserving
a no-else prefix: the next located token is not else. eat_else_false derives
the operational result from that observation. A checked inhabited control
shows why it cannot be dropped: if(true){} followed by else{} parses to the
some alternative, and the supposed none result preserving else{} is proved
false. This records the existing grammar boundary, not an added exclusion
or a presumed successful parse. Then/else bodies are braced, so no new claim
about unbraced dangling-else token association is made.

All five covered forms also have exact actual yield equations for arbitrary
layout. A helper handles the existing some/block statement yield. Thus the
concrete Boolean/header/body inputs correspond to actual existing printer
clauses, rather than mocked parser successes or replacement syntax.

Controls quantify over both Boolean values and arbitrary excess fuel/state.
Their mixed loop body has break, continue and an ordinary nested return
block. Both unchecked states, nonempty else suffix, fragment layout and
EOF19 are represented. Empty if bodies exercise both alternatives, a close
brace supplies a no-else boundary, and explicit capture/inequality controls
prove the following-else restriction necessary. Actual while and if-some
yield controls preserve residual layout. All five alternatives are covered;
general expression atoms and other for headers remain pending.

| Gate | Outcome | Evidence directory |
| --- | --- | --- |
| runtime.py diag Solidity/Frontend/StatementGrammarH28/BoolCompound.lean | pass, final some/yield additions | /workspace/h28-statement-grammar-evidence/run-1793809310619069974 |
| runtime.py build Solidity.Frontend.StatementGrammarH28.BoolCompound | pass; 5.05s timed wall, RSS 432304 KiB | /workspace/h28-statement-grammar-evidence/run-1793809357265997326 |
| runtime.py diag tests/h28-sol/statement-grammar/BoolCompoundControls.lean | pass, final necessary-boundary inequality | /workspace/h28-statement-grammar-evidence/run-1793809434739696766 |
| runtime.py gate Solidity/Frontend/StatementGrammarH28/BoolCompound.lean | pass, no warnings | /workspace/h28-statement-grammar-evidence/run-1793809462301044777 |
| runtime.py gate tests/h28-sol/statement-grammar/BoolCompoundControls.lean | pass, no warnings | /workspace/h28-statement-grammar-evidence/run-1793809482644479811 |

All 15 public source axiom sets are printed in the source gate. The two
Boolean atom equations and while_bool_prefix have none; eat_else_false uses
propext; the remaining 11 use propext and Quot.sound. Exact signatures and
control axiom sets are saved. No custom axiom, unsafe/native_decide,
heartbeat raise, expression uniqueness premise or producer change was added.
The one failed source diagnostic (run-1793809141571783009) needed explicit
Located/Tok types in the token observation; those were made explicit.
The failed receipt is retained. Statement equations unfold stmt only once
instead of recursively simplifying every parser branch. No speedup claim
or existing implementation refactor is made.

Separate read-only finder and skeptic pass source and all controls, without
Lean/server/builds. Both verified the exact no-else boundary countercontrol
and restricted fixed-atom/body scope. Registration remains local only.

Remaining full assignment: all-syntax/atom balance, general mixed statement
splitting, simple-root discrimination, token-level conditional uniqueness/
association, general compound expression/header/body fuel coverage, full
repository gates and whole-scope reviews/acceptance. SG-CEX-01 remains
OPEN/REFUTED. The original persistent goal remains active and incomplete.


## Scope hold Q-ATOM: ownership of missing opaque-atom proofs

Stable question ID: Q-ATOM. Sources: original G11 queue 2–3, the instruction
"Expression subtrees are read-only atoms", and the prohibitions on weakening
premises or changing producer interfaces. This hold is a scope interpretation
question, not a failed Lean proof or an approval to add assumptions. The
original goal and all original theorem obligations are preserved.

Question: Does treating expression subtrees as read-only atoms permit this
lane to prove local boundary/head/fuel lemmas by inspecting immutable existing
expression/type/argument Syn and Print/Parser clauses, without expression
uniqueness or producer changes, or must an owning lane supply a pinned proved
atom interface before general statement composition resumes?

Options (no recommendation or assumed approval):

- Local proof-only boundary/fuel work: permit those lemmas inside the existing
  H28 namespace, with immutable producers, all existing premises preserved and
  SOL-EU still excluded. This permits the dependent general work to continue.
- Keep expression atoms opaque: coordinator/owning lane supplies a proved,
  pinned delimiter/head/structural-fuel API, then H28 resumes composition.
  Dependent general results remain open while that API is unavailable.

Two independent read-only audits found no existing API that removes this
choice. Parser.lean defines expr/binary/unary/postLoop and token-count fuel,
but proves no general structural fuel sufficiency. Print.lean defines yield,
toks and Derives but no atom balance/head theorem. Prec.lean's proved
prec_root extracts the node contract, not token boundaries. Check.lean's
parseExpr_derives requires an already successful parse; using it as a
completeness premise would violate the assignment. ExprExamples provides
finite coverage only. docs/feature-work/frontend-parse.md lines 435–438 and
587–589 explicitly leave general expression completeness/unambiguity open.
Static inference and JSON-decoder theorems concern other judgments.
Both audits used no Lean/server/builds and inferred no human authorization.
Their exact scope evidence is saved in scope-audit-q-atom.json.

The completed permitted backfill is committed and sealed through M; no
expression-level induction, producer interface or new assumed atom contract
was introduced during this hold. Remaining general balance/simple-root/
compound fuel and token-association work stays explicitly unfinished.
Questions or explanations alone do not authorize either option.

Independent light static checks at 6a8d86b07d8c833c456842b8ebeaaa961c525736:

| Command | Outcome | Evidence |
| --- | --- | --- |
| bash scripts/check-doc-paths.sh | pass, 11.13s, RSS 7076 KiB | static-scope-audit-1793810048961335110/doc-paths.log |
| bash scripts/check-trust.sh | pass, 13.23s, RSS 337256 KiB; 3732 sources, 285 inventoried sites, 0 findings | static-scope-audit-1793810048961335110/trust.log |
| node scripts/check-layers.mjs | pass, 0.40s, RSS 182548 KiB; 559 core modules, 0 forbidden reaches | static-scope-audit-1793810048961335110/layers.log |
| bash scripts/coord-tools/register.sh --check | fail, 0.10s; stale shared roots missing H28 imports | static-scope-audit-1793810048961335110/roots.log |

All paths above are under /workspace/h28-statement-grammar-evidence.
The local registration manifest enumerates all 60 new source modules.
Shared/generated roots remain unchanged as explicitly required; the failed
roots gate is retained for central integration, never reported as PASS.
These static checks are not the unrun full repository/Lean final gate.
An earlier static timing setup failed because this host lacks /usr/bin/time;
no gate ran in that attempt. Its failure record is sealed, and the actual
checks use OS wait4 timing/RSS instead. Lean checks still use the established
bounded Docker runtime and its /usr/bin/time, without changing proof budgets.


## H31 resolution of Q-ATOM

Human decision H31, received from the coordinator on 2026-11-04:
"permit local proof-only inspection of the read-only expression/type/argument
atoms in the boundary/fuel lemmas, with expression uniqueness excluded.
Do not change producer APIs or theorem statements."

This selects local proof-only boundary/fuel work. Q-ATOM is resolved; its
prior hold and audits remain historical evidence, not an active dependency.
Work resumes in the same VM/branch under the original goal. All prior
premises, exclusions, statement obligations and proof budgets are preserved.
No producer file/API or expression-uniqueness implementation is authorized.


## Checkpoint N: H31 arbitrary syntax brace balance and block splitting

BalancePr.lean, BalanceAtoms.lean and SyntaxBalance.lean prove curly-brace
balance of every successful existing Syn statement yield and its complete
expression/type/argument/Yul dependency closure. This uses H31's permission
for local proof-only atom inspection. No producer, original theorem
statement, premise, exclusion or expression-uniqueness claim is changed.
BalanceCat selects only the required intrinsic categories and their list/opt
closures; the public expression_yield_balanced and statement_yield_balanced
statements require no atom-balance or expression-uniqueness premise.

The exhaustive induction covers all 79 constructors in this closure, including
all 13 statement roots, all three simple forms, both catch forms, all block/
item/list/option alternatives, every expression/type/parameter/argument
constructor and every Yul constructor. The exact category-to-constructor
inventory, file identities and public names are in inventory-n.json. Excluded
unit/top/part declaration categories are not needed to state these theorems;
they are not replacement syntax or a new statement exclusion.

The proof threads actual Pr input/output layouts through successful binds.
Scalar helpers account for every operator/type token, identifier path,
fragmented string literal and function-type visibility/mutability ordering.
Literal payload bytes remain inside atomic string tokens, so brace bytes are
not punctuation delimiters. Attribute balance is explicitly proved for the
empty modifier list used by function types; no arbitrary modifier claim is
assumed. Every conditional/optional yield clause is balanced for all outcomes.
The new theorem proves brace-token balance, not uniqueness or balance of
other delimiter kinds.

arbitrary_block_boundary and successful_block_boundary derive balanced
contents for any successful intrinsic block yield. arbitrary_block_prefix_split
then recovers common token contents and the exact suffix from equal arbitrary
braced prefixes, across different contexts/layouts. It requires no expression
premise and does not conclude tree equality. This removes the earlier arbitrary
atom/balance gap in braced-block splitting. General mixed statement splitting,
simple-root discrimination, token-level else association and fuel remain
separate original obligations.

Controls contain an inhabited actual yield with a function type, explicit
attribute order, call options, string bytes123/125 and an unchecked return
block. They preserve arbitrary residual layout. Invalid duplicate attrs and
wrong fragment lengths still fail. A string closing-brace payload successfully
yields a neutral string token. A universal negative control proves no arbitrary
statement can successfully yield an unmatched closing-brace punctuation token.
The distinct-tree SG-CEX-01 flag collision remains explicitly balanced and
has its same actual yield, preventing a balance-to-uniqueness overclaim.
These are kernel printer controls, not new solc acceptance claims; the prior
45 external solc fixtures remain separate.

| Gate | Outcome | Evidence directory |
| --- | --- | --- |
| runtime.py diag Solidity/Frontend/StatementGrammarH28/BalancePr.lean | pass, final helpers | /workspace/h28-statement-grammar-evidence/run-1793817522488562384 |
| runtime.py diag Solidity/Frontend/StatementGrammarH28/BalanceAtoms.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793817089471835499 |
| runtime.py diag Solidity/Frontend/StatementGrammarH28/SyntaxBalance.lean | pass, final corollaries | /workspace/h28-statement-grammar-evidence/run-1793817709489959711 |
| runtime.py build Solidity.Frontend.StatementGrammarH28.SyntaxBalance | pass; 4.57s timed wall, RSS 479544 KiB | /workspace/h28-statement-grammar-evidence/run-1793817739393455280 |
| runtime.py diag tests/h28-sol/statement-grammar/SyntaxBalanceControls.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793817917798299560 |
| runtime.py diag tests/h28-sol/statement-grammar/BalancePublicAxioms.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793817986826067885 |
| runtime.py gate Solidity/Frontend/StatementGrammarH28/BalancePr.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793818029194269624 |
| runtime.py gate Solidity/Frontend/StatementGrammarH28/BalanceAtoms.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793818035513912723 |
| runtime.py gate Solidity/Frontend/StatementGrammarH28/SyntaxBalance.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793818042215660926 |
| runtime.py gate tests/h28-sol/statement-grammar/SyntaxBalanceControls.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793818060838635610 |
| runtime.py gate tests/h28-sol/statement-grammar/BalancePublicAxioms.lean | pass, all45 public theorem signatures/axioms | /workspace/h28-statement-grammar-evidence/run-1793818075432211356 |

All 45 public theorem signatures and kernel axiom sets are enumerated by the
explicit BalancePublicAxioms audit. 34 have no axioms, ten use propext and
Quot.sound, and one uses propext. axioms-n.json maps every name to its actual
printed output. No custom axiom, sorry/admit, unsafe/native_decide or raised
heartbeat limit is introduced. The three new source modules are locally
registered; frozen shared roots and producer input hashes remain unchanged.

Retained failed runs: run-1793816911121507914 used a reserved Lean binder;
run-1793817361395340424 exposed a second reserved binder and ambiguous
inferred postconditions. These were made explicit. run-1793817462334681963
exposed dependent optional match elaboration and a mapping equation issue;
the optional token computation was separated from its proof witness.
run-1793817560041981557 exhausted the unchanged 200000-heartbeat limit during
broad mapping equation expansion. The final proof splits the two existing
MapKey constructors and uses their precise equations; no budget was raised.
run-1793817836958203840 found a malformed NumLit.dec control and stopped when
MCP auto-setup tried rebuilding an import without explicit -j1. The hard guard
was retained, the control uses the actual numeric constructor, and the existing
FlagCounterexample import was prebuilt serially before the passing recheck.
No failed gate is relabeled PASS or removed. This is new proof work, not a
speed-motivated producer refactor, and no speedup percentage is claimed.

Separate read-only finder and skeptic pass the full closure and inhabited
controls without Lean/server/builds. Their confirmed stale active Q-ATOM
wording finding is fixed; the historical hold remains preserved. An incorrect
missing-bitOr review finding was withdrawn after reread; the branch was
already present and required no edit. reviews-n.json records both verdicts.

H31 resolves Q-ATOM, so no scope question remains. The full original assignment
is still incomplete: general mixed statement token splitting, simple-root
discrimination, token-level conditional uniqueness/association, general
compound expression/header/body fuel, full repository gates and whole-scope
reviews/acceptance remain. SG-CEX-01 stays OPEN/REFUTED. No goal is created,
reset or marked complete by this checkpoint.


## Checkpoint O: H31 leading tokens and complete raw root-collision cases

HeadPr.lean and SyntaxHead.lean prove nonempty first-token invariants for
all existing expression, type, parameter, variable-declaration, simple,
call-argument and named-argument constructors. SafeStart contains an actual
first token and excludes exactly the 11 fixed hard statement starts. The
contextual identifier "revert" is deliberately not classified as hard.
Successful literal chunks are proved nonempty even when fragment length is
zero; empty bytes and absent tokens are different. No successful parse or
expression-uniqueness premise is introduced.

syntax_head_invariant has substantive SafeParts conclusions for precisely
those seven categories; its explicit True fallback makes no head claim
about other categories. expression_yield_safe_start, type_yield_safe_start
and simple_yield_safe_start have unconditional substantive conclusions for
every successful corresponding yield. The induction covers all 42 constructors
in those categories. Arbitrary payloads/layouts and all operator cases are
handled by local proofs over immutable producer equations, as H31 permits.
No replacement AST, producer API or original theorem statement changes.

RootHead.lean composes this with the proved fixed heads. For arbitrary
contexts, layouts, residual layouts and suffixes, actual simple-statement
yields cannot share a prefix with any of the 11 hard roots. The universal
statement_root_collision_cases theorem enumerates the complete raw-yield
possibilities: equal roots, simple/revert, or revert/simple. It has no root
exclusion, expression premise or assumed parser success. It classifies roots,
not subtrees. It deliberately does not claim the contextual pair impossible;
discharging that pair under the existing precedence/path contract remains
an original obligation.

An inhabited raw control shows why unconditional raw root injectivity would
be false: a revert with tuple target and a simple nested call both successfully
yield revert(E)(); and have different roots. The revert candidate has prec=false,
while the simple candidate has prec=true. The actual existing stmt parser,
with sufficient fixed-tree fuel n+20 and arbitrary suffix/state, chooses the
simple tree. This control demonstrates the necessity of the existing contract;
it does not refute root discrimination under that contract or introduce a
new exclusion. SG-CEX-01 remains independently OPEN/REFUTED.

HeadConstructorControls checks actual successful yields with empty residual
layout and a nonempty safe head for all 42 constructor witnesses, with exact
Ctor inventories in seven typed collections. It separately checks all five
literal variants, including zero-byte and fragmented literals. These are
existing indexed Syn witnesses, not an untyped replacement representation.
RootHeadControls supplies the raw collision, actual parser/precedence facts,
universal arbitrary-simple versus return separation, empty-string positive
and invalid empty-fragment-choice negative controls. These kernel yield/token
controls are not new solc semantic-acceptance claims; the prior external
fixtures remain separate.

| Gate | Outcome | Evidence directory |
| --- | --- | --- |
| runtime.py diag Solidity/Frontend/StatementGrammarH28/HeadPr.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793819782178386900 |
| runtime.py diag Solidity/Frontend/StatementGrammarH28/SyntaxHead.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793819941157239481 |
| runtime.py build Solidity.Frontend.StatementGrammarH28.SyntaxHead | pass; 2.04s timed wall, RSS 427672 KiB | /workspace/h28-statement-grammar-evidence/run-1793820007085729837 |
| runtime.py diag Solidity/Frontend/StatementGrammarH28/RootHead.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793820057021954810 |
| runtime.py build Solidity.Frontend.StatementGrammarH28.RootHead | pass; 0.65s timed wall, RSS 403136 KiB | /workspace/h28-statement-grammar-evidence/run-1793820162923990875 |
| runtime.py diag tests/h28-sol/statement-grammar/RootHeadControls.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793820244280825550 |
| runtime.py diag tests/h28-sol/statement-grammar/HeadConstructorControls.lean | pass, all42 constructors/all5 literal variants | /workspace/h28-statement-grammar-evidence/run-1793820435991614260 |
| runtime.py diag tests/h28-sol/statement-grammar/HeadPublicAxioms.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793820537960475507 |
| runtime.py gate Solidity/Frontend/StatementGrammarH28/HeadPr.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793820591772134611 |
| runtime.py gate Solidity/Frontend/StatementGrammarH28/SyntaxHead.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793820597336132004 |
| runtime.py gate Solidity/Frontend/StatementGrammarH28/RootHead.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793820604521827993 |
| runtime.py gate tests/h28-sol/statement-grammar/RootHeadControls.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793820612379768659 |
| runtime.py gate tests/h28-sol/statement-grammar/HeadConstructorControls.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793820618437329885 |
| runtime.py gate tests/h28-sol/statement-grammar/HeadPublicAxioms.lean | pass, all19 public theorem signatures/axioms | /workspace/h28-statement-grammar-evidence/run-1793820624703387266 |

All 19 public source theorem signatures and actual axiom sets are enumerated
by HeadPublicAxioms and axioms-o.json: seven have no axioms and twelve use only
propext and Quot.sound. Constructor/source identities are in inventory-o.json.
No custom axiom, sorry/admit, unsafe/native_decide, budget raise, producer
change or expression-uniqueness premise was introduced. The three modules
are locally registered only. Separate read-only finder and skeptic pass
source and all controls, without Lean/server/builds; reviews-o.json records
both verdicts and the exact scope boundary.

Retained failures: run-1793820207606655257 needed the existing BlockLeafCoverage
import for locatedInput; it was imported and prebuilt serially.
run-1793820407733515050 exposed a tuple-grouping error in a call-argument
fixture; the corrected list has exactly two argument witnesses and the
checked total count is 42. Both failed receipts remain retained, not PASS.

Published update: origin/master was fetched and verified at
89373e34cdfd6bb5db7054b1c204d01edffc5fa7, with pinned-base ancestry verified.
The coordinator-reported integrated ElsePosition and NearestElse modules
exactly match this branch. New ExecutableAst.Shared.Boundary/Translate APIs
serve Json-to-RawExpr/RawStmt translation, not the checked Syn token parser,
so they do not replace this token-boundary work. No merge/reset, producer
duplication, goal reset or VM replacement occurred. Read-only API hashes and
assessment are saved in published-89373e34.json. Other committed lane work is
not claimed integrated by that publication.

Remaining full scope: contextual simple/revert discrimination under the
existing contract, general mixed statement splitting, token-level conditional
uniqueness/association, general compound expression/header/body fuel, full
repository gates and whole-scope reviews/acceptance. The original objective
is not complete. H31 remains the only atom-proof authorization, and SOL-EU
remains excluded.


## Checkpoint P: all statement roots under the original contract

PairPr.lean and SyntaxPair.lean derive the required two-token facts locally
under H31. An expression/type yield cannot begin with an identifier followed
by another identifier or colon; it is nonempty whenever that nonemptiness is
needed for concatenation. Call-argument yields start with a left parenthesis.
The framing lemma explicitly requires a real separator and obtains atom
nonemptiness from the previously proved SafeParts invariant. All 36 constructors
of these three substantive categories are covered; other categories receive
only the explicit trivial PairInvariant fallback, not an atom claim.

ContextPr.lean and RootContract.lean then distinguish all three simple forms
from path-qualified revert. Declaration heads can create two leading identifiers
only where an initializer assignment or semicolon follows. Expressions and
tuple declarations cannot acquire the conflicting prefix. Valid revert path
yields start with an identifier and then either a member period or argument
parenthesis, so their first three tokens disagree with simple statements.
All these facts are framed over arbitrary suffixes and actual input/output
layouts. Existing isPathExpr supplies the path premise directly from revert's
existing precNode contract; no new semantic premise is assumed.

statement_root_unique_node_contract proves root equality for equal successful
token prefixes under the existing node conditions. statement_root_unique derives
the original full prec=true/layout version using Syn.prec_root. This completes
root discrimination across all 13 statement roots for arbitrary intrinsic
syntax, contexts, atoms, layouts and suffixes. There is no root exclusion,
expression-uniqueness or successful-parser premise. The conclusion is Root
equality only, not full syntax-tree equality or whole-language uniqueness.
No producer API or original theorem statement is changed.

RootContractControls has inhabited positional, qualified and named revert
forms with successful actual yields and precedence. It distinguishes a simple
declaration's semicolon from revert's parenthesis/member period, proves a
universal simple/revert prefix refusal, and recovers the revert root of every
contract-valid matching candidate. A valid named argument begins identifier/
colon and is explicitly retained outside the expression/type atom-pair claim.
PairConstructorControls reuses the same typed fixture data as O to check the
stronger properties for all 36 relevant constructors, all five literal variants,
nonempty actual yields and empty residual layouts. Exact Ctor inventories and
counts are kernel checked; no predicate-only/vacuous fixture inventory is used.

### SG-CEX-02: ASCII intrinsic-guard completeness is false

ContextualDeclCounterexample.lean contains the inhabited statement
simpleStmt(declVar(varDecl(userType("revert"), none, "E"), none)). Its exact
successful yield is the tokens of revert E;. The actual checked lexer accepts
the ASCII bytes and produces those tokens. The tree has prec=true and
InProfile. Nevertheless, for every positive fuel n+2, the existing stmt parser
returns expected '(' at the semicolon; fuel0/fuel1 also fail. The all-fuel
proof covers arbitrary token locations, suffix states, output states and target
trees. No larger structural fuel can recover this intrinsic declaration.

This is an additional OPEN/REFUTED roundtrip-completeness target under the
stated intrinsic guards. It does not refute RootContract: no valid revert tree
shares the declaration's semicolon prefix. It is not rejection of solc-accepted
source or a solc divergence. The pinned compiler also rejects the unqualified
contextual declaration, consistent with the checked parser's frozen dispatch.
The missing intrinsic-image restriction is not added as a new premise,
exclusion or producer change. SG-CEX-01 remains separately OPEN/REFUTED.

The new six-case contextual-revert-fixtures manifest records three exact
ParserError2314 refusals (contract-type declaration, value-type declaration,
initialized declaration) and three accepted AST controls (qualified declaration,
ordinary declaration and error revert). The lexical identifier rule explicitly
admits revert. The positive qualified/ordinary declarations and actual error
revert prevent an empty all-refusal test relation. The external compiler is
still 0.8.38+commit.1835d247.Emscripten.clang with the original SHA256 pin.
The exploratory observations are retained separately from the subsequent
pinned-expectation gate. All source/input/output hashes are sealed.

contextual-revert-solc.mjs verifies all six source hashes, compiler identity,
exact errors and accepted statement/declaration-path AST fields. It seals setup
and case failures and copies its own source/manifest. runtime.py changes only
its exact solc runner allowlist to admit this second fixed path; all memory,
no-swap, CPU, headroom, serial Lean, wall and failure-cleanup guards stay unchanged.
The original45 fixtures and runner are unchanged and were rerun successfully.
These are external compiler tests, not premises or evidence replacing the
kernel proofs. No semantic solc acceptance is claimed for raw kernel-only trees.

| Gate | Outcome | Evidence directory |
| --- | --- | --- |
| runtime.py diag Solidity/Frontend/StatementGrammarH28/PairPr.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793821238782375771 |
| runtime.py diag Solidity/Frontend/StatementGrammarH28/SyntaxPair.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793821381822991130 |
| runtime.py diag Solidity/Frontend/StatementGrammarH28/ContextPr.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793821637197432185 |
| runtime.py diag Solidity/Frontend/StatementGrammarH28/RootContract.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793821866656976278 |
| runtime.py build Solidity.Frontend.StatementGrammarH28.RootContract | pass; 1.75s timed wall, RSS 446320 KiB | /workspace/h28-statement-grammar-evidence/run-1793822012190190520 |
| runtime.py diag Solidity/Frontend/StatementGrammarH28/ContextualDeclCounterexample.lean | pass, exact lexer/all-fuel equations | /workspace/h28-statement-grammar-evidence/run-1793822566829758878 |
| runtime.py build Solidity.Frontend.StatementGrammarH28.ContextualDeclCounterexample | pass; 0.75s timed wall, RSS 449480 KiB | /workspace/h28-statement-grammar-evidence/run-1793822650089152080 |
| runtime.py diag tests/h28-sol/statement-grammar/RootContractControls.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793822774544714542 |
| runtime.py diag tests/h28-sol/statement-grammar/PairConstructorControls.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793822824148070802 |
| runtime.py diag tests/h28-sol/statement-grammar/ContractPublicAxioms.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793823312657256898 |
| runtime.py gate Solidity/Frontend/StatementGrammarH28/PairPr.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793823547601599660 |
| runtime.py gate Solidity/Frontend/StatementGrammarH28/SyntaxPair.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793823553666548053 |
| runtime.py gate Solidity/Frontend/StatementGrammarH28/ContextPr.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793823560939358464 |
| runtime.py gate Solidity/Frontend/StatementGrammarH28/RootContract.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793823566564296226 |
| runtime.py gate Solidity/Frontend/StatementGrammarH28/ContextualDeclCounterexample.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793823573263007215 |
| runtime.py gate tests/h28-sol/statement-grammar/RootContractControls.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793823579194180195 |
| runtime.py gate tests/h28-sol/statement-grammar/PairConstructorControls.lean | pass | /workspace/h28-statement-grammar-evidence/run-1793823585209052888 |
| runtime.py gate tests/h28-sol/statement-grammar/ContractPublicAxioms.lean | pass, all43 public theorem signatures/axioms | /workspace/h28-statement-grammar-evidence/run-1793823591478678202 |
| runtime.py solc tests/h28-sol/statement-grammar/solc-fixtures.mjs | pass, original45 expectations unchanged | /workspace/h28-statement-grammar-evidence/run-1793823597759694237 |
| runtime.py solc tests/h28-sol/statement-grammar/contextual-revert-solc.mjs | pass, all6 new exact expectations | /workspace/h28-statement-grammar-evidence/run-1793823603941886168 |

All43 public source theorem signatures/axiom sets are enumerated by
ContractPublicAxioms and axioms-p.json. 26 have no axioms, 14 use propext and
Quot.sound, and three use propext. All36 atomic constructor/source identities,
all13 root scope and six fixture records are in inventory-p.json. The five
new source modules are locally registered only. No custom axiom, sorry/admit,
unsafe/native_decide, heartbeat raise, expression uniqueness or producer change
is introduced. Exact commands/exits/timing/RSS and recursive input hashes are
in every run receipt, alongside process samples and immutable checksums.

Two failed counterexample diagnostics remain retained: run-1793822395213499066
needed the actual Lexer import; run-1793822465683997957 could not synthesize
generic Except equality for decide. The unchanged exact lexer-success equation
is instead proved by kernel rfl. Its statement and guards were not weakened.
The independent bounded compiler exploration is at
contextual-solc-probe-1793822236046042570 and is labeled observations, not a
pinned expectation PASS. Later fixture gates enforce the recorded expectations.

Separate read-only finder and skeptic pass all five proof modules, both control
modules, the exact counterexample applicability, six source fixtures and test
runner/resource change. Neither used Lean/server/solc/builds. Both confirmed
that the counterexample does not claim solc-accepted-source rejection or a
failure of the root theorem. reviews-p.json records the scoped verdicts.

Remaining original work: general mixed statement token splitting, token-level
conditional association/uniqueness where meaningful independently of SOL-EU,
additional true structural-fuel fragments versus explicitly refuted intrinsic
completeness targets, full repository gates and whole-scope reviews/acceptance.
Root discrimination under the existing contract is now proved, including the
previous contextual pair. The original assignment is not marked complete;
SG-CEX-01 and SG-CEX-02 stay OPEN/REFUTED with no new exclusion or premise.

## Checkpoint Q: atom semicolon absence and actual mixed-list segmentation

Implementation and VM proof validation are complete for this bounded increment.
H35 cache delivery remains pending; this checkpoint is not reported done before
that requirement is resolved. The original full queue remains partial.

H31 permits proof-only inspection of immutable expression/type/argument atoms.
NoSemiPr and NoSemiAtoms establish semicolon-free token concatenation, literal
fragments, type attributes and operator combinators. SemiFree is a token
predicate, not an AST, and admits real empty and nonempty token sequences.
SyntaxNoSemi proves it for all seven atomic categories and recursive list/opt
wrappers: 42 substantive constructors plus nil/cons/none/some, exhaustively.
Categories outside that closure have a false category guard; no absence claim
is made for statements or blocks. All literal payload bytes remain inside
tokens, including semicolon bytes and zero-length successful fragments.
There is no expression uniqueness assumption, producer change or parser premise.

SemicolonSplit derives actual yield shapes for simple, continue, break,
return, emit and revert statements. Arbitrary successful yields of any two
of those roots have unique complete token prefixes and residual suffixes.
First-semicolon framing intentionally does not describe do-while: its body
can contain an earlier semicolon. The checked inhabited negative control
demonstrates this boundary; no original theorem statement or exclusion changes.

FramedStatementList proves all successful statement yields are nonempty.
It combines the six semicolon boundaries with arbitrary successful block
boundaries, using the existing raw root collision classification. Its mixed
list theorem requires the seven-root fragment only on the source list;
the matching target list is arbitrary. Actual yield decomposition retains
each intermediate layout. The conclusion equates actual token segments,
not syntax trees, expressions, layout states or parsed results. In particular,
arbitrary compound and unchecked contents may occur inside its block segments.
General compound statement/item boundaries remain unfinished.

NoSemiControls checks actual successful nonempty yields for all42 substantive
constructors, all five literal variants, literal semicolon payloads and the
four list/option constructors. It retains negative punctuation-semicolon,
empty fragment-choice and wrong layout-choice controls. FramedListControls
checks 12 actual variants spanning all six semicolon roots, plus an inhabited
seven-segment mixed list with a conditional inside its block. Its seven-root
inventory observes that real syntax list, rather than counting a literal list.
A universal control applies the list theorem against any matching target list.
SemicolonPublicAxioms checks and prints all49 new public theorem signatures
and axiom sets, with no custom axiom or sorry/admit/unsafe/native_decide.
inventory-q-v2.json and axioms-q.json retain exact source identities and scope.

The five new source modules have a local registration manifest only.
Read-only producers and frozen shared roots are unchanged. This increment
adds proofs, not a producer refactor or speed claim, and raises no budget.
All Lean work remains explicit -j1 in the same 12 GiB/no-swap runtime with
4 GiB VM headroom. No external solc fixture changed; the earlier 51 pinned
external expectations remain separate from these kernel proofs.

H35 validation also rechecked checkpoint P on this VM: all five P owned
module builds, all43 public theorem audits and both control suites passed.
The actual container Lake cache was recovered at /home/ubuntu/.cache/lake
and matched to the owned module traces. The H35 preparation contains all71
then-owned modules, 213 real artifacts and 71 input mappings. It ran the
unmodified scripts/coord-tools/ship-cache.sh with SHIP_ALLOW_HEAD=1 and an
explicit prepared LAKE_CACHE_DIR. Collection succeeded with zero unresolved
traces, but transport exited1 because this worker lacks coordinator
/home/agent/.local/state/cloudvm-coord/poll-state.json. No fabricated lane,
catalog, credentials or transport were configured and no delivery PASS is
claimed. The initial archive is /workspace/h35-cache-1793830946459497122.tar.gz;
its receipt, mapping/artifact inventory, logs and checksums are under
/workspace/h28-statement-grammar-evidence/h35-cache-1793830946459497122.

Q-H35-TRANSPORT [H35; scripts/coord-tools/ship-cache.sh]: How should the verified
worker cache be delivered when coordinator-only lane/catalog/transport state
is absent here? Option A: coordinator retrieves the prepared archive, using
the saved actual cache and receipt without installing coordinator transport
on the worker. Option B: coordinator supplies a worker-compatible shipping
command/configuration, which is then run on this VM with a saved delivery
receipt. Neither option is assumed authorized by silence. Proof work continues
independently; checkpoint delivery is pending.

Remaining original obligations: general compound/item token boundaries,
token-level conditional association/uniqueness independently of SOL-EU,
remaining true structural-fuel coverage versus SG-CEX-01/02 OPEN/REFUTED,
full repository gates, scope-complete acceptance and whole-scope reviews.
No persistent goal was created, reset or marked complete.

Q review correction: independent finder and skeptic both found stale checkpoint O
witness-symbol keys in the first inventory-q.json. Constructor values and counts
were already correct. inventory-q-v2.json names the actual *SemiWitnesses Q
controls and records the correction; the original inventory remains retained.

| Q gate | Outcome | Evidence directory |
| --- | --- | --- |
| runtime.py diag NoSemiPr.lean | pass | run-1793831052027716872 |
| runtime.py build NoSemiPr | pass | run-1793831069023255982 |
| runtime.py diag NoSemiAtoms.lean | pass | run-1793831074825537175 |
| runtime.py build NoSemiAtoms | pass | run-1793831087678602802 |
| runtime.py diag SyntaxNoSemi.lean | pass | run-1793831093257515323 |
| runtime.py build SyntaxNoSemi | pass | run-1793831160626686369 |
| runtime.py diag SemicolonSplit.lean | pass | run-1793831184961638100 |
| runtime.py build SemicolonSplit | pass | run-1793831262233128156 |
| runtime.py diag FramedStatementList.lean | pass | run-1793831412200866640 |
| runtime.py build FramedStatementList | pass | run-1793831479084220188 |
| runtime.py diag NoSemiControls.lean | pass | run-1793831635330130933 |
| runtime.py diag FramedListControls.lean | pass | run-1793831673827620942 |
| runtime.py diag SemicolonPublicAxioms.lean | pass | run-1793831682179764548 |
| runtime.py gate SemicolonPublicAxioms.lean | pass, all49 signatures/axioms | run-1793831699131661534 |
| check-doc-paths.sh / check-trust.sh / check-layers.mjs | pass | static-q-precommit-1793831785447820938 |
| register.sh --check | fail, frozen roots lack lane imports | static-q-precommit-1793831785447820938 |

All paths above are under /workspace/h28-statement-grammar-evidence. Each
runtime receipt includes exact command, exit, wall/RSS, input hashes, process
samples and no-swap/headroom checks. The final exact-head gate and cache
receipts are in the sealed handoff; H35 cache transport is not yet passing.

Retained failed diagnostics: run-1793831324092392533 required the actual
SyntaxBalance import and explicit predicate reduction; run-1793831353837696486
required the actual core append_eq_nil_iff name and recursive guard equation;
run-1793831380943820735 resolved the guard by its equation theorem. Controls
run-1793831493775876917 corrected Tok.str spelling; subsequent preflight
run-1793831523045102863 refused a stopped runtime. The same container was
restarted. run-1793831561186026424 and run-1793831644405690338 required
recursive fixture equations instead of an unavailable Decidable reduction.
No theorem signature, premise, exclusion, budget or producer was changed.


H35 control-axiom audit completion: in addition to all49 public source lemmas,
NoSemiControls and FramedListControls now print axioms for all21 of their
new kernel-control theorems. No control theorem statement or proof changes.
inventory-q-v3.json retains v2 witness-name corrections and adds these exact
control-theorem identities (70 source/control theorem audits total). The
earlier source inventory revisions remain saved. This audit-only follow-up
is revalidated at its own committed head before another delivery attempt.

## H41: checkpoint Q cache receipt and amended delivery policy

The coordinator reports receipt statement-grammar-cache-received-20261105T020412Z.json
at $XDG_STATE_HOME/cloudvm-coord/receipts/ and confirms its
SHA256 verification. The worker independently recomputed the saved pack SHA:
17559f6df217563456007fb5ec2ce5ce33e3f6ec90eb65f9bbf96fcf4f593e3b.
The pack remains /workspace/h35-q-final-cache-1793832269544630195.tar.gz.
This resolves Q-H35-TRANSPORT and checkpoint Q delivery. The receipt's remote
path is coordinator-reported, not claimed locally read. The saved worker
record is h41-q-received.json. Original queue obligations remain unfinished.

H41 amends H35: leave verified packs on this VM, record absolute path and SHA,
mark new delivery coordinator-pending and continue. Never run ship-cache.sh
on this VM again. No transport credentials or coordinator state are needed.
Earlier failed shipment evidence remains immutable historical evidence.


## Checkpoint R: continuation heads and both intrinsic item constructors

BoundaryHeadPr and BoundaryHead prove successful atom yields have a real first
token distinct from actual else/catch/unchecked keywords. All42 constructors
in the seven substantive categories are covered; other categories receive
no head claim. Same-spelled identifiers/string payloads remain atoms. This
does not add a lexical/parser restriction or alter original head theorems.

FramedItemList lifts that result to all13 statement roots with arbitrary
contexts/layouts/suffixes. It is a continuation-boundary prerequisite, not
general token-level nearest-else association. Item/list/block splitting handles
both intrinsic item constructors: source stmtItems retain Q's seven-root
FramedStatement fragment; source uncheckedItems contain arbitrary intrinsic
blocks. All target items/lists remain arbitrary. Exact intermediate layouts,
token segments and suffixes are preserved. No AST equality, SOL-EU, assumed
successful parse or general compound framing is claimed; SCtx stays intrinsic.

BoundaryHeadControls checks actual successful nonempty yields for all42 atom
constructors, all5 literals and all13 roots, plus keyword/identifier negatives
and universal suffix refusal. FramedItemControls observes both item constructors
in an eight-segment yield with a conditional inside unchecked, try/catch inside
a block, literal semicolon/brace payload bytes and nonempty residual layout.
Universal controls recover item/block segments against arbitrary targets;
do-while is an inhabited source-fragment negative. Kernel checks do not claim
solc acceptance. No external fixture changed from the51 pinned cases.

ItemPublicAxioms checks/prints all20 source theorem signatures/axioms; the
controls print all21 new control theorem axiom sets. inventory-r.json records
exact identities, axioms-r.json all41 sets:22 none and19 propext/Quot.sound.
Wrapped output whitespace is normalized. No new axiom, sorry/admit, unsafe/
native_decide or heartbeat raise occurs. All3 modules are registered locally
only; shared roots and producers stay frozen. This adds proofs, not a
producer refactor or speed claim.

| R gate | Outcome | Evidence directory |
| --- | --- | --- |
| runtime.py diag BoundaryHeadPr.lean | pass | run-1793844384527293533 |
| runtime.py build BoundaryHeadPr | pass | run-1793844426182417921 |
| runtime.py diag BoundaryHead.lean | pass | run-1793844436597586127 |
| runtime.py build BoundaryHead | pass | run-1793844496241022247 |
| runtime.py diag FramedItemList.lean | pass | run-1793844541688283935 |
| runtime.py build FramedItemList | pass | run-1793844585465134315 |
| runtime.py diag BoundaryHeadControls.lean | pass | run-1793844693715353004 |
| runtime.py diag FramedItemControls.lean | pass | run-1793844772104751324 |
| runtime.py diag ItemPublicAxioms.lean | pass | run-1793844781770041836 |
| runtime.py gate BoundaryHeadControls.lean | pass | run-1793844855911377761 |
| runtime.py gate FramedItemControls.lean | pass | run-1793844861559296866 |
| runtime.py gate ItemPublicAxioms.lean | pass | run-1793844867557033586 |

Evidence paths are under /workspace/h28-statement-grammar-evidence, with exact
commands/exits, wall/RSS, input hashes and process samples. Lean remains serial,
explicit -j1,12GiB/no swap and4GiB VM headroom. Final exact-head validation,
versions, permitted KeySort and H41 pack path/SHA are in the sealed handoff.
New delivery is coordinator-pending; ship-cache.sh is never run on this VM.

Retained failures: run-1793844512352093685 corrected actual uncheckedItem
parameters and singleton normalization; run-1793844720914885102 corrected
the doWhile control's l/u parameters. run-1793844745667940933 refused the
stopped runtime; the same container was restarted. No original premise,
signature, exclusion, budget or producer changed.

H41 resolves Q-H35-TRANSPORT; no R scope question remains. Remaining original
work: general compound boundaries, conditional token association/uniqueness
independently of SOL-EU, remaining true structural-fuel coverage, full final
repository gates, whole-scope acceptance and reviews. SG-CEX-01/02 remain
OPEN/REFUTED. The persistent objective is not reset or marked complete;
get_goal is unavailable, so the existing frozen objective continues.


## Checkpoint S: all-constructor parenthesis balance and actual header splitting

ParenBalance defines a token balance predicate and a structural suffix scanner.
The actual header consumer requires an opening parenthesis and returns exactly
the suffix after its matching close. ParenPr and ParenAtoms prove the existing
printer combinators preserve balance. SyntaxParenBalance covers all79
constructors in the same complete statement dependency closure as N, including
lists/options, tuple-declaration holes, function-type attributes and returns,
assembly flags, unchecked blocks, both catches and every Yul constructor.
Braces and token payload bytes are neutral to this parenthesis invariant.
Categories outside that closure receive no balance claim.

Universal actual-yield corollaries give matching expression-header token/suffix
splits and exact scanner consumption at arbitrary layouts and suffixes. They
do not equate expression trees, invoke SOL-EU or assume successful parsing.
This is a compound-boundary prerequisite, not yet general statement framing
or token-level nearest-else association. Bracket balance is not claimed.
Original brace/head theorems, producer APIs, premises and exclusions are unchanged.

ParenBalanceControls packages existing Syn values as Sigma c:Cat,Syn c×choices;
the intrinsic index remains, so this is test packaging rather than a new AST.
Actual successful yields cover79 distinct constructors, exactly matching the
universal proof's79 cases and N's declared closure.77 are nonempty; nil/none
are valid empty controls. Additional variants cover all5 literals, parenthesis
payload bytes, assembly flags/Yul calls, nested function-type attributes and
returns. Negative controls reject standalone delimiters and malformed headers,
while an unmatched delimiter in the returned suffix is correctly preserved.
Universal controls apply actual-header and content/suffix splitting lemmas.
None of these kernel controls substitutes for external solc acceptance.

ParenPublicAxioms checks/prints all48 public source theorem signatures/axioms;
controls print all16 control theorem axiom sets. inventory-s.json and
axioms-s.json record the exhaustive64 theorem identities and exact source
hashes. No new axiom, sorry/admit, unsafe/native_decide or budget raise occurs.
The4 new modules use local registration only. This adds local proof modules;
it is not a producer refactor or speed claim. External51solc fixtures are unchanged.

| S gate | Outcome | Evidence directory |
| --- | --- | --- |
| runtime.py diag ParenBalance.lean | pass | run-1793845883218776418 |
| runtime.py build ParenBalance | pass | run-1793845945647278586 |
| runtime.py diag ParenPr.lean | pass | run-1793845772092934639 |
| runtime.py build ParenPr | pass | run-1793845953536147451 |
| runtime.py diag ParenAtoms.lean | pass | run-1793845783924670581 |
| runtime.py build ParenAtoms | pass | run-1793845958556009537 |
| runtime.py diag SyntaxParenBalance.lean | pass | run-1793845963752940225 |
| runtime.py build SyntaxParenBalance | pass | run-1793845978897790887 |
| runtime.py diag ParenBalanceControls.lean | pass | run-1793846275589352143 |
| runtime.py diag ParenPublicAxioms.lean | pass | run-1793846288037311534 |
| runtime.py gate ParenBalanceControls.lean | pass | run-1793846334090109972 |
| runtime.py gate ParenPublicAxioms.lean | pass | run-1793846341252683679 |

All evidence paths are under /workspace/h28-statement-grammar-evidence and
contain actual commands/exits, wall/RSS, input hashes and process samples.
Lean remains serial, explicit-j1,12GiB/no swap with4GiB VM headroom.
Retained failed control diagnostic run-1793846219014701012 corrected a nested
fixture parenthesis by adding an explicitly typed array helper; the intended
function-type/layout assertion is unchanged. The same bounded runtime was
restarted, without a heartbeat increase or a weakened theorem.

Final exact-head module builds/controls/all64axiom audits/KeySort, tool versions,
static gates and H41 verified pack path/SHA are in the sealed handoff. Delivery
is coordinator-pending; no VM ship-cache.sh command is run. Remaining original
work: general compound statement/item framing and conditional token association/
uniqueness independently of SOL-EU, remaining true structural-fuel coverage,
full repository final gates, whole-scope acceptance/reviews. SG-CEX-01/02 remain
OPEN/REFUTED. The original persistent goal is not reset or marked complete.


## Checkpoint T: published adoption and Gate G0 observer repair

The coordinator withheld FixtureData because kernel-evaluated Syn matches violate
Gate G0. The owned branch adopted published8495f1deb0a95dd6b9301822d8649ab76b217681
without reset or conflict in merge9a0f4ef8c1d7a13319d1459b88d6a797a3a00802.
Original base6f3eedf0788ee1f8a3bcf230558c712ecdca04d5 remains an ancestor.
All7 pinned Checked/Source inputs are byte-identical. Incoming master changes
are coordinator-authored adoption; repair edits stay in the3 exclusive paths.
No cache freshness or whole producer/lane completion is inferred from adoption.

Independent finder and skeptic confirmed12 computational declarations:
FixtureData's4 observers (including its nested optional body elimination),
Shape.root, BlockLeafCoverage.itemCount/itemsAsList, FramedStatements,
FramedItem/FramedItems, and the2 test inventory observers. All are repaired.
G0List uses Syn.casesOn with category-generalising motives and typed result
families for list cells/projections, with structural recursion. Root/item
results dispatch by Cat, returning only PUnit outside their relevant categories.
The fixture observers retain fuel64, exact name-f selection and actual body
node observations. Nat/Option/FnName matches remain parameter-only. Guards
fold over typed ordinary lists. No alternate AST, fabricated successful
relation, producer change, new premise/exclusion or budget raise is introduced.

Explicit rfl constructor equations preserve public observer contracts. Existing
theorem statements are unchanged; dependent proof bodies use these equations
instead of unfolding indexed matches. All45 fixture definitions and original
inventory tail are byte-identical from statementFixture0 onward. The source/
Lean/manifest synchronization check still covers45cases and40constructor
obligations. The corrected observations retain actual acceptance/refusal
checks rather than mocking successful parses.

G0ObserverControls checks exact typed-cell/count/guard equations, arbitrary
zero fuel, genuine constructor observations at fuel0/1/2, actual f-body
selection versus g refusal, and the original contract/unit64budgets.
G0ElaborationAudit records9 private eliminators plus4result families from
the actual environment. Independent reviewers inspected the emitted
generalised casesOn/brecOn/below terms and found no indexed-match helper or
Eq.rec/Eq.ndrec cast in these bodies. The audit is elaboration-time evidence,
not an object-language correctness theorem or a scanner-policy exception.
Proof-producing spineOfOpen/slotOfOpen and their isOpen proofs are Prop
inhabitants with no computational result extraction; this applicability
distinction is not a new G0 exemption.

The warned refactor has matched before/after VM measurements:3rounds of all45
fixture kernel checks plus5affected controls per side, same order/wrapper,
-j1/12GiB/no swap/4GiB VM headroom. Median aggregate user+system CPU:
81.54s before,78.74s after (-3.43%). The largest individual median increase
is5.77%; no target crosses10%. Before rounds:81.87/81.54/79.29s. After:
78.74/80.92/77.71s. Original logs are immutable. Two stdout PASS lines
interleaved into GNU time stderr; their exact timing values were recovered
by removing only those gate lines, without rerunning checks or changing code.
This is evidence for this measured workload, not a universal speed claim.

Both timing phases identify committed9a0, because repair sources were then
uncommitted. g0-measured-source-identities.json records exact before/after
Lean hashes from the immutable runtime inputs and links them to this repair.
Do not confuse equal head IDs with equal measured sources. The final committed
head receives its own complete VM validation before checkpoint completion.

Evidence under /workspace/h28-statement-grammar-evidence:
- g0-repair-setup-1793848768897341152: fetch, ancestry, protected inputs,
  published policy and adoption receipts.
- g0-before-1793849302056445273 and g0-after-1793851683702714898:
  all300kernel checks, exact commands/exits/CPU/wall/RSS and process samples.
- g0-performance-detail.json: per-target medians and10%threshold check.
- inventory-t-g0.json and axioms-t-g0-precommit.json: all repaired source
  identities,94public theorem audits,13observer definitions and controls.
- run-1793852325587304623: observer controls PASS.
- run-1793852331164482421: actual elaborated term audit PASS.
- run-1793852337953538618: public signatures/axioms PASS.

Retained failed checks: run-1793851186880623093 stopped the same container
when MCP setup tried to rebuild stale BoundaryHeadPr without explicit-j1.
Its0Lean errors did not count as a runtime PASS. After serial prebuilds,
the bounded check passed. run-1793851323180751968 required explicit root
constructor equations in unchanged control assertions. run-1793851461817450340
corrected the audit's String.endsWith API. Guards and budgets were never relaxed.
The84th module is locally registered; authored repair changes no shared root,
central module map, trust inventory or frozen Source/Core file.

H41 remains in force: verified packs are left on the VM with path/SHA and
delivery coordinator-pending; never run ship-cache.sh here. Original remaining
work is unchanged: general compound statement/item framing, conditional token
association/uniqueness independently of SOL-EU, remaining true structural-fuel
coverage, full repository final gates and whole-scope acceptance/reviews.
SG-CEX-01/02 remain OPEN/REFUTED. This repair does not complete the full lane
or reset/complete the persistent objective.


## Checkpoint U: recursive Boolean loop coverage

Adopted published master `9584f9e7df09f638d9e0cb8930501d1660aa4b2f`
with merge `3e0ea4659da07306967e7dad2ea193ee5e13a2fc`, preserving all
owned files and seven pinned inputs byte for byte. The adoption receipt is
`/workspace/h28-statement-grammar-evidence/adopt-9584f9e7-1793871795805005608/receipt.json`.
The integration packet includes three prior statement-grammar modules; this
adoption does not claim completion of G11 or cache freshness.

`LoopCoverage.lean` adds the intrinsic `BooleanLoops` relation, with exactly
four constructors: block over any existing `NestedItems` witness; Boolean
while; empty-header for; and Boolean do-while. The last three recurse on a
statement in the existing loop-enabled context. Its Nat budget is inherited
from the block witness and increases by one per loop, independently of width.
`boolean_loops_coverage` proves actual Checked.stmt success at every
`n + d + 6`, preserving arbitrary suffix, layout and EOF state. No successful
parse is a premise. `boolean_loops_yield` computes the actual printer for
arbitrary layout lists, and `boolean_loops_token_unique`,
`boolean_loops_derives_iff` and `boolean_loops_yield_unique` connect the
printer to equality through a common sufficient structural fuel budget.
These five public theorems are unconditional inside the inhabited indexed
fragment, with no expression uniqueness assumption. Expressions are fixed
Boolean atoms. No general expression, conditional, compound framing or
whole-language uniqueness result is asserted.

`LoopCoverageControls.lean` covers every relation constructor: an arbitrary
Nat-depth while tower in either unchecked context; mixed while/do/for nesting
over a block with break, continue and empty return; arbitrary excess fuel and
suffix; actual yield and uniqueness; and negative controls for excluded
conditionals, zero fuel, and a do-while missing its final semicolon. The
parameter-only Except result observation does not match on Syn. The two
computational tower functions recurse on Nat, not an indexed syntax family.
No existing implementation, theorem, proof budget or producer API changed.

Source diagnostic passes: run-1793872298011108453; importing controls pass:
run-1793872331106793398. Initial failures are retained in
run-1793872066056059064 (explicit fuel normalization and yield equations),
run-1793872133975162949 (one final pure equation), and
run-1793872264803787016 (controls used unavailable Except.isError and an
unavailable Decidable syntax equality). All were repaired without changing
the statements or heartbeat limit. The owned container stopped on failures
and was restarted unchanged. No failed check is counted as a pass.

Separate read-only finder and skeptic reviews pass with no findings; neither
used Lean, servers, builds or solc. Final committed-head evidence is retained
in `/workspace/h28-statement-grammar-evidence/checkpoint-u-validation.json`,
with commands, process exits, timings, RSS and source identities linked to
individual immutable runtime records. The source signature/axiom audit is
`LoopPublicAxioms.lean`; controls also print their nine theorem axioms.
H41 cache packs remain on this VM, delivery coordinator-pending; no
ship-cache.sh invocation is authorized or performed.

Original queue remains partial. General compound/item framing, conditional
token association, remaining true structural-fuel coverage, whole-scope
acceptance and repository final gates/reviews remain open. SG-CEX-01 and
SG-CEX-02 remain OPEN/REFUTED. This checkpoint neither weakens those targets
nor completes or resets the persistent objective. Local registration alone
is added; shared generated roots and module maps remain coordinator-owned.


## Checkpoint V: recursive conditionals and exact token frames

Adopted remote-verified published `b86ae4568cef6d6226f4d170360bbb089debe3fb`
at merge `fef2b237ad409cc0958c9d9efffe593cce953d7f`, preserving all owned
files and seven pinned inputs. Receipt:
`/workspace/h28-statement-grammar-evidence/adopt-b86-locations.json`.
Balance and YieldSplit are now integrated; no integrated proof was duplicated.

ConditionalPrefix, ConditionalCoverage and ConditionalYield add an intrinsic
six-constructor BooleanStatements relation: existing BooleanLoops; if without
else; if with else; while; empty-header for; do-while. Recursive bodies use
existing Syn contexts. Conditions remain Boolean literals. The if-with-else
constructor retains exactly `then.openIf = false`, proved equivalent to the
immutable `precNode = true` contract, with no new expression assumption.
StatementFrame requires either a closed statement or a suffix whose next token
is not else. This necessary token boundary is explicit; it is not a successful
parser premise. No existing theorem, premise, exclusion or budget was changed.

The universal coverage theorem derives `n + d + 6` fuel from the syntax
witness, with one budget unit per unary wrapper and summed branch budgets plus
one for an else-bearing if. Both branches receive proved sufficient fuel.
Arbitrary excess fuel and suffix/layout/EOF states are retained. Open bodies
of do-while are followed by the immutable while token and therefore receive a
valid internal frame; the outer do-while is closed and preserves an arbitrary
suffix, even an else. Actual printer yields preserve all layouts. Public token
and Derives uniqueness use common sufficient fuel, independently of SOL-EU.
Framed prefix uniqueness additionally recovers the existing intrinsic tree and
both token suffixes from equality of concatenated token streams. This is proved
for this inhabited fragment, not for arbitrary statement syntax.

ConditionalCoverageControls covers every relation constructor. Controls include
an arbitrary Nat-depth if tower, while/for bodies containing matched ifs, an open
else branch, and do-while around an open if with an arbitrary else suffix. The
dangling-else positive and wrong-association trees have the same actual tokens;
the wrong tree fails the existing precedence node contract and cannot inhabit
the relation. Another actual parser equation shows an open if capturing a
following else when its required frame is absent. No general-expression
uniqueness or whole-language completeness is claimed. Internal token locations
are zero as in earlier coverage; arbitrary suffix locations are preserved.
These kernel token-parser proofs do not prove string lexing or source validity.

The public axiom/signature audit lists all eleven source theorems, six relation
constructors and StatementFrame. Controls print all eighteen theorem axioms.
No new computational indexed-family match was introduced: tower construction
recurses on Nat, option/list observations are existing producer computations,
and the new indexed inductions/cases construct proofs only. No producer API,
Source/Core file, generated root, shared map or trust registry was authored.

Per-file diagnostics pass at the unchanged heartbeat limit. Initial failures
remain immutable: run-1793882612075873590 (explicit Prec import needed),
run-1793882645762970222 (Boolean negation parentheses),
run-1793882794044773933 (explicit optional-statement yield equation), and
run-1793883078630214996 (the lambda form of List.map_id). The owned runtime
stopped on failures and was restarted unchanged; none counts as a passing gate.
Final source diagnostics: run-1793883122484848524; original controls diagnostics:
run-1793882956468356276. Final committed-head gates, current source hashes,
exact commands/exits/timing/RSS, reviews and cache receipt are linked from
`/workspace/h28-statement-grammar-evidence/checkpoint-v-validation.json` and
`/workspace/h28-statement-grammar-evidence/checkpoint-v-locations.json`.

Separate read-only source finder and skeptic reviews passed; neither used Lean,
a server, builds or solc. Final acceptance additionally requires review of the
committed-head controls and exact evidence, recorded in the external handoff.
The skeptic caught a premature final-review claim, corrected before commit.
H41 delivery remains coordinator-pending after
local byte/hash verification; never run ship-cache.sh on this VM.

Original queue remains partial: general compound/item token framing, nearest
else and uniqueness beyond this fixed-atom fragment, remaining true parser
coverage, full repository final gates and whole-scope acceptance/reviews remain
open. SG-CEX-01/02 stay OPEN/REFUTED; SOL-EU remains excluded. Existing frozen
persistent objective is neither reset nor completed by this checkpoint.


## Checkpoint W: arbitrary-width conditional item decomposition

Adopted remote-verified published `8bf8321873befa3f35ca31e97e5339a1baee93e6`
at merge `c1419c5bc066d80630ca44f0393ae39980b4c6d4`. All owned files and seven
pinned inputs are byte-identical across adoption. Receipt:
`/workspace/h28-statement-grammar-evidence/adopt-8bf-locations.json`.

ConditionalList introduces a two-constructor Prop relation BooleanItemList on
existing `Syn (.list (.item k))` and per-statement token segments. Nil and cons
are inhabited; cons carries an existing BooleanStatements witness. No untyped
AST or computational indexed-family match is introduced. Both compared lists
must inhabit this relation. It excludes unchecked items and statements outside
the existing fixed-Boolean fragment; this result is not unrestricted item
uniqueness and does not add an exclusion to any original target.

Every represented statement's tokens are nonempty and cannot start with else.
Thus the following represented item supplies the preceding open-if frame. The
empty tail uses an explicit safe terminal state. Recursion on the intrinsic
list witness applies V's proved prefix theorem to obtain head-tree and tail
token equality, then actual yields recover all per-statement segments.
Actual yields preserve arbitrary layout lists. The Derives theorem identifies
the complete actual token stream and supports unconditional tree/segment
uniqueness inside this inhabited fragment, without an expression-uniqueness or
assumed-successful-parser premise.

The existing universal syntax brace-balance theorem supplies balanced list
contents. Combining balanced block splitting with list segmentation recovers
intrinsic block contents, each statement's tokens and arbitrary token suffixes.
This is actual printer/token decomposition, not a new block parser completeness
or fuel theorem. Remaining parser-fuel obligations stay open; no existing
coverage statement, premise, exclusion, interface or proof budget changed.

ConditionalListControls covers both relation constructors and an arbitrary
Nat-width family of consecutive open ifs in every intrinsic context, with all
layout lists. It checks actual list and block yields, Derives uniqueness and
block-prefix suffix recovery, plus a next-if frame control. Negative controls
reject an else-only token list and an empty statement segment. No new external
solc fixture is asserted; V's unchanged pinned45+6 external cases remain
separate evidence, not universal kernel proofs or source-validity results.

All eleven public source theorems and both constructors have exact signature
and axiom audits; controls audit all nine theorems. Initial diagnostics are
retained: run-1793894577422334155 (fixed-index induction alternative binders)
and run-1793894617555948939 (stmtItem printer is an identity). Both were repaired
without changing statements or budgets; failed checks stopped the same runtime
and are not counted as passes. Final source diagnostics:
run-1793894745172102998; controls: run-1793894793720235572.

Separate read-only finder and skeptic source reviews passed without findings;
neither used Lean, servers, builds, solc or writes. Final acceptance also needs
committed-head gate/evidence review. Results and immutable commands, exits,
timing/RSS, hashes, final reviews, H41 receipt and sealed handoff are linked from
`/workspace/h28-statement-grammar-evidence/checkpoint-w-validation.json` and
`/workspace/h28-statement-grammar-evidence/checkpoint-w-locations.json`.
Cache delivery remains coordinator-pending after local verification. Never run
ship-cache.sh here. Shared generated roots/maps/trust registries are untouched.

The original G11 goal remains partial: general compound/item framing and
association/uniqueness beyond this fragment, remaining true structural-fuel
parser coverage, full repository final gates and whole-scope acceptance/reviews
remain open. SG-CEX-01/02 remain OPEN/REFUTED and SOL-EU remains excluded.
This checkpoint neither resets nor completes the existing persistent objective.


## Checkpoint X: constructive list and block parser fuel

Adopted published `3ad22f66d8fc6431378c22e71823436c79dede7f` at merge
`3bed59f4e76cc0aee2a9c4858f58eddf94beb4f9`, verifying remote ancestry and
preserving every owned file and seven pinned inputs. Receipt:
`/workspace/h28-statement-grammar-evidence/adopt-3ad-locations.json`.

ConditionalFuel adds BooleanListBound, a Prop relation over existing intrinsic
item-list syntax, actual token segments and a natural budget. Nil has budget
zero. Cons takes the maximum of the head statement's structural budget plus
seven and the tail budget. Every existing BooleanItemList witness constructs
such a bound; no successful parse or external fuel oracle is a premise.
The relation forgets to BooleanItemList and remains inhabited by both nil and
arbitrarily wide/deep cons lists. No untyped AST or computational indexed
syntax observer is introduced, and no previous theorem or relation is changed.

The actual blockLeafStep item equation is derived from the existing recursive
statement coverage. Its proof retains the parser's two nested Except binds
through stmtItem and some, rather than assuming they are definitionally one
bind. Represented token heads ensure that neither unchecked dispatch nor block
termination is taken at an item. The next represented item provides the open-if
frame, and the final closing brace provides the last frame.

ItemsAt uses the maximum nesting budget independently of width. List-loop fuel
is separately derived from intrinsic item count and actual token nonemptiness,
including the stopping step. The actual parser's token-length repetition budget
is therefore sufficient. For bound b and arbitrary excess n, block coverage is
at `n + b + 1`, block-statement coverage at `n + b + 2`, and an unchecked item
wrapper at `n + b + 2` in its existing permitted context. All preserve arbitrary
suffix/layout/EOF state. The public completeness theorem constructs a b for
every old BooleanItemList witness and proves success for every excess/suffix.
It is completeness for that inhabited fixed-Boolean fragment, not general
statement/unchecked syntax, expression uniqueness or whole-language parsing.

ConditionalFuelControls checks all relation constructors and entry points:
arbitrary positive width of open ifs with constant nesting budget eight;
arbitrary conditional depth with its derived budget; all intrinsic contexts;
block, block-statement and unchecked parsing; a closing brace preserving an
external else; empty block at fuel one; and actual zero block-fuel and zero
many-loop-counter refusals. The twelve control theorems and all nine source
theorems/two relation constructors have public axiom/signature audits.
No new external solc fixture is claimed; previous pinned external tests remain
separate from these universal kernel token-parser proofs and source validity.

Initial failed checks remain immutable. run-1793897681667089197 had wrapper
elaboration errors and was stopped by the unchanged VM headroom guard; the
container peak was below1GiB while VM memory accounting was dominated by file
cache. run-1793897760876666389 showed the exact two-bind mismatch. The task-only
POSIX_FADV_DONTNEED advice receipt resource-cache-advice-1793897760687633281.json
records current memory12148416512 to10818916352 bytes, releasing cached pages
from this task's evidence/archive files only, without modifying bytes, global
drop_caches, swap or resource/proof limits. run-1793897935298655335 needed the
final unchecked-wrapper rfl. None of these failures counts as a passing gate.
Final source diagnostics: run-1793897990902814240; controls diagnostics:
run-1793898105131616279. Serial build has no new warnings.

Separate read-only finder and skeptic source reviews passed without findings;
neither used Lean, a server, builds, solc or writes. Final acceptance additionally
requires committed-head controls, axiom/build/KeySort gates and evidence review.
Exact commands/exits/timing/RSS, source identities, final reviews, cache receipt
and sealed handoff are linked from
`/workspace/h28-statement-grammar-evidence/checkpoint-x-validation.json` and
`/workspace/h28-statement-grammar-evidence/checkpoint-x-locations.json`.
H41 verified cache delivery stays coordinator-pending; never run ship-cache.sh
on this VM. No producer, shared root/map/trust registry or budget was changed.

Original G11 remains partial: general compound/item framing and association
outside this fragment, remaining true parser coverage, full repository gates
and whole-scope acceptance/reviews remain open. SOL-EU remains excluded and
SG-CEX-01/02 remain OPEN/REFUTED. This checkpoint neither resets nor completes
the existing frozen persistent objective.


## Rebase onto e6849d3b

Coordinator-requested rebase adopted published
`e6849d3bdf516099d20c33d3581d523449764018` before the next authored commit.
The pre-rebase head was `32cb2d35df071147888d5e63a8401f7fcc648f6d`; the
rebased source head is `e8f53d3729dcaac17f0c4e070438e3847e69233f`.
All26 replay input commits touched only owned paths. The sole conflict was
FixtureData: its authored checkpoint version was restored, and the later G0
repair replayed. Final direct Git comparison and all189 owned-file hashes
matched the pre-rebase snapshot, including the repaired observer. Seven pinned
inputs are unchanged, published master is an ancestor, and the final delta
from master contains only the three owned paths. No proof, premise, exclusion,
producer interface, resource limit or heartbeat budget was changed.

Old checkpoint IDs and immutable evidence remain historical records. The old
head is retained at `refs/backup/statement-grammar/pre-e6849d3b`, with a verified
incremental recovery bundle. Its seven prerequisite commits are all retained
by that ref and are ancestors of the published master; the bundle is not
standalone. Prerequisite IDs, replay/conflict records, range-diff and before/after
source hashes are under
`/workspace/h28-statement-grammar-evidence/rebase-e6849d3b-1793899528150148986/`.
The exact rebase receipt is linked by
`/workspace/h28-statement-grammar-evidence/rebase-e684-locations.json`.
No older gate/cache receipt is relabeled as evidence for the new head.

Separate read-only finder and skeptic rebase reviews passed without source
findings. The skeptic's incremental-bundle caveat is recorded above, with
prerequisite ancestry/retention verified. Final acceptance additionally requires
fresh committed-head builds, axiom/control/KeySort gates, exact-evidence review
and an H41 cache receipt. Those are linked from
`/workspace/h28-statement-grammar-evidence/rebase-e684-validation.json` and
`/workspace/h28-statement-grammar-evidence/rebase-e684-final-locations.json`.
No reviewer used Lean, servers, builds, solc or writes. H41 delivery remains
coordinator-pending after local verification; never run ship-cache.sh here.

The existing frozen G11 objective remains partial and was not reset or replaced.
General compound/item framing, broader true coverage, repository final gates
and whole-scope acceptance/reviews remain pending. SOL-EU stays excluded and
SG-CEX-01/02 remain OPEN/REFUTED. Shared generated roots/maps/trust inventories
remain coordinator-owned.


## Moved lane (2026-11-05)

The lane moved from the idle Codex VM to a Claude cloud VM with the same
scope (handoff `.handoff/statement-grammar.md` on `cloud/moved4-prompts`,
`997382550989229ccd97f1821365b9a8af1e62aa`). It starts from master
`aec9adf1ad8666a7e591e42a537069a93dc858cb`, which already contains every
lane path of Codex head 70845978. The Codex evidence under `/workspace/…`
and its caches are not reachable from this VM; nothing below cites them.
Validation is re-run fresh with the Lean MCP server (per-file diagnostics)
and `./run-lean.sh`.

The Codex lane kept publishing to master in parallel (its checkpoints Y–AE
below, from `ControlFreePr` to `BlockHeaderBoundary`). Its letters collide
with this lane's, so this lane's sections are headed "Moved-lane
checkpoint …". The moved lane builds on the Codex modules where they apply
(`CatchCoverage`, `CatchListCoverage`, `BlockHeaderBoundary`) and changes
none of them.

## Moved-lane checkpoint Y: Gate G0 node twin for the fixture observers

The held review finding: the fixture observers evaluated by `decide +kernel`
in `FixtureControls/Case00..44` still reached an indexed-family `match`.
Checkpoint T had already moved FixtureData's own four observers to
`Syn.casesOn` with category-generalising motives, but `optionalBodyCtorsAt`
read the body through `Syn.nodes` (`Source/Ctor.lean`), a generated
`match` on `Syn` (Gate G0 condition 1). Source is read-only for this lane.

Repair: `G0Nodes.lean` defines `nodeCtorsAt`, a twin of
`Syn.nodes ·|>.map Node.ctor` over all 112 `Syn` constructors, by
`Syn.casesOn (motive := fun _ _ => List Ctor)` with structural recursion
(the same form as `G0List`), generated mechanically from the `Syn.nodes`
block so the preorder and constructor names match. The public
`g0NodeCtors` is linked to the Source observer by
`g0NodeCtors_eq_nodes : g0NodeCtors s = s.nodes.map Node.ctor` (induction,
axioms `propext`). `optionalBodyCtorsAt` now reads `g0NodeCtors body`.
No fixture, statement, required-constructor list or budget (fuel 64, name
`f`) changed; the observation is equal by the link theorem.

The profile half of the same observer (`statementFixtureCheck` compares
`u.rejections.isEmpty` with the fixture's `profile`) also reached indexed
matches: `Syn.rejections = s.nodes.filterMap Node.excl`, with `Syn.excl`,
`Syn.placeholders` and `isLiteralBase` (finder Y-1, below). `G0Rejections.lean`
adds their twins (`g0Nodes`, `g0Placeholders`, `g0IsLiteralBase`,
`g0Rejections`, plus the typed views `g0OptValue`, `identAt`, `litAt`), all by
`Syn.casesOn` with generalising motives, linked by `g0Nodes_eq`,
`g0Placeholders_eq`, `g0IsLiteralBase_eq` and `g0Rejections_eq`
(`g0Rejections s = s.rejections`; axioms `propext`). FixtureData reads
`(g0Rejections u).isEmpty`; `statementFixtureCheck_profile` states that this
is the old observation.

Residual, not repaired: an `assembly` node's exclusion still calls Source's
`isRethrow`, an indexed `match` with string-literal patterns. Lean 4.24
cannot generate equation lemmas for its matcher ("failed to generate
equality theorems for `match` expression `isRethrow.match_1`"), and a twin
could not be linked to it here (a link by exhaustive case analysis on the
string tests was attempted and abandoned); an unlinked twin was written, proved sound, and
removed rather than kept without its link. It is evaluated only on
`assembly` nodes, i.e. on the four accepted assembly fixtures
(`statementFixture` sources at FixtureData lines ~179–199, one of them the
canonical rethrow). The producer's `parse` (the system under test,
read-only here) also matches on indexed syntax. Neither is a Gate G0
exemption: the held finding is closed for the lane's observers except
`isRethrow` on those four fixtures.

Checks (Lean MCP, severity error, fresh on this VM): `G0Nodes`,
`G0Rejections`, `FixtureData`, all 45 `FixtureControls/Case00..44` (each
closes by `decide +kernel`, axioms `[propext]`; re-run after the rejections
twin), `tests/…/G0ObserverControls` (`g0_node_ctors_twin_actual_body` and
`g0_rejections_twin_actual` by `decide +kernel` on the twins only),
`G0PublicAxioms`, `G0ElaborationAudit` (target list now 20 entries: 15
private eliminators and 5 result families; the audit asserts only the
inventory size and logs the terms, so the absence of matchers rests on
inspection).

Warned refactor: the twins replace `match`-compiled observers by the
`casesOn` form Gate G0 prescribes. A matched before/after timing was not
taken on this VM (no `lean` in Bash under the repository settings); it is
listed as a limitation.

## Moved-lane checkpoint Z: expression-atom conditional framing

Queue item 2 asks for compound framing and nearest-else association outside
the Boolean fragment, with expression subtrees as read-only atoms and any
needed expression assumption exposed exactly.

`AtomConditional.lean` exposes the atom premise

    ExprAtomRparen e es a :=
      ∀ n s, expr (n + a) (locatedInput (es ++ [)]) s) = .ok (e, punctBefore ) s)

(the atom's tokens parse back to exactly `e` before `)`, leaving `)`
unread, at every fuel of at least `a`). It is proved for Boolean literals and
identifiers (`bool_atom_rparen`, `ident_atom_rparen`, budget 5) and is
otherwise a premise: expression parser completeness and SOL-EU stay with the
expression lanes. `AtomStatements` extends `BooleanStatements` (embedded by
its first constructor) with `if`/`if-else`/`while`/`do` over atom
conditions and the empty-header `for`. Proved: header equations
(`if_atom_prefix`, `while_atom_prefix`, `do_atom_tail`), coverage at every
excess fuel and framed suffix (`atom_statements_coverage`, budget additive
in the atom budgets), the precedence contract (`atom_statements_node`),
nearest else (`atom_statements_nearest_else`) and token uniqueness inside the
fragment (`atom_statements_token_unique`, from the parser being a function).

`AtomNested.lean` generalises to arbitrary nesting with mutual relations
`AtomStmt`/`AtomItems` over the existing indexed syntax: blocks of any
width and depth whose items are atom statements, empty return, break and
continue in their intrinsic loop contexts, `return e;` (premise
`ExprAtomSemi`, plus the token side condition `NoSemiHead`: nonempty and not
starting with `;`), `unchecked { … }` items only in an unchecked-free context
(the type index forbids nesting; the actual parser refusal is checked), the
atom conditionals, and `for (; c; u)` with an empty initialiser and optional
atom condition and update (`OptAtom`, `for_atom_step`; initialiser statements
are not covered). Coverage is proved by mutual structural recursion
(`atom_stmt_coverage`, `atom_items_at`), with budgets computed from the
witness (`max (d + 7) b` per item, `+2` per unchecked wrapper) and loop
fuel from the actual token length (`atom_items_count_le`); no successful
parse is assumed. Also: block and unchecked coverage, the precedence
contract and nearest else, token uniqueness and prefix/suffix uniqueness
(`atom_stmt_prefix_unique`). Control-leaf lists embed
(`atom_items_of_leaf_items`). All axioms are within `propext`/`Quot.sound`.

Controls (`tests/…/AtomConditionalControls.lean`,
`AtomNestedControls.lean`): every constructor of `AtomStatements`,
`AtomStmt`, `AtomItems` and `OptAtom` inhabited (all four `for` header
shapes, the last also by a kernel `rfl` at fuel 17); identifier
conditions in every position; dangling else `if (x) if (y) {} else {}`
parsed to the inner association (kernel `rfl` at fuel 18) and unique; the
outer association excluded by the contract; closed loops preserving an
`else` suffix; a block closing an open if before a following `else`;
arbitrary width (n × `return x;`, constant budget) and arbitrary depth;
a three-item block with `while`/`if-else`/`break`/`continue`/`return z;`/
`unchecked`. Negative: the atom premise names the parsed expression
(`ident "y"` refused for token `x`), refuses extra tokens and an
insufficient budget; `NoSemiHead` refuses `[]` and `[;]`.

"Arbitrary" conditions means arbitrary expressions satisfying the exposed
premise; only single-token atoms (identifiers, Boolean literals) are shown to
satisfy it here.

Not claimed: yield/`Derives` uniqueness for the atom fragments (it needs
the atoms' yields, i.e. a printer premise), `for` initialisers,
simple/expression statements, emit/revert/try/
assembly, and any expression-level fact beyond the stated premises.

### Reviews of checkpoints Y and Z

Separate read-only finder and skeptic reviews (no Lean server, no builds) of
commits `cffc480d..5694e8e0`. Skeptic verdict PASS-with-fixes. Confirmed
findings and their fixes:

- Y-1 (finder): `statementFixtureCheck` kernel-evaluated `u.rejections`
  (indexed matches in `Syn.nodes`/`Syn.excl`); the doc misnamed it as
  producer code. Fixed by `G0Rejections.lean` (above); the `isRethrow`
  residual is recorded.
- Z-1 (both): "every constructor inhabited" was false for `AtomStmt.forLoop`
  and `AtomStmt.doLoop`. Fixed: `for_do_relation`, plus the new `forAtom`
  shapes.
- Z-2 (both): `simp_all` in `atom_items_of_leaf_items`. Replaced by
  `simp only`, with the statement restated as a budget bound `b ≤ 7`.
- Y-2 (both): the G0 control kernel-evaluated `Syn.nodes` in a second
  conjunct. Dropped; the link theorem covers it.
- Y-3 (skeptic): eliminator count in the doc. Corrected above.
- Z-3 (both): misleading docstring on `loopBody` and the name
  `outer_block_actual_parse` (an instance, not a computed parse). Fixed
  (`outer_block_at_fuel_32`); kernel-computed parses are
  `ident_nearest_actual_parse` and `for_header_both_kernel`.
- Suspected, addressed in wording: "arbitrary" conditions (only single-token
  atoms are shown to satisfy the premise); "above `a`" → "at least `a`";
  the parser's own matches are not a G0 exemption.

### Round-2 reviews (for headers, rejections twin)

Finder and skeptic, read-only, on `a850a62e..290f1d78`. Finder: no
confirmed findings. It compared all 112 `nodesAt` and `placeholdersAt` cases
with Source by script, hand-checked every exclusion and the `for` token
list and budgets, and confirmed that no indexed `match` beyond the documented
`isRethrow` and `parse` is reached. Skeptic: PASS-with-fixes, wording only.
The closure claim must name the `isRethrow` exception and its four assembly
fixtures, and "cannot be linked" becomes "could not be linked here". Both
were fixed in `20dd3435`. A note left as is: `forAtom .none .none` and
`forLoop` describe the same tree. That is harmless, because uniqueness is
about trees.

## Moved-lane handoff (2026-11-05)

Queue accounting (handoff `.handoff/statement-grammar.md`):

| Item | State |
| --- | --- |
| 1. Gate G0 repair of the fixture observers | Done for every lane observer except Source's `isRethrow` on the four accepted assembly fixtures, which could not be linked (checkpoint Y, `G0Nodes`, `G0Rejections`). All 45 cases still close by `decide +kernel`. |
| 2. Compound/item framing and nearest else outside the proved fragment | Extended to arbitrary expression conditions under an exposed atom premise, arbitrarily nested blocks, `return e;`, `unchecked` items and `for (; c; u)` (checkpoint Z). Still open: `for` initialisers, simple/expression statements, emit/revert/try/assembly bodies. |
| 3. Parser coverage with syntax-derived fuel | Covered for the `AtomStmt`/`AtomItems` fragment by mutual structural recursion. Budgets are computed from the witness, with loop fuel from the token length. Same open constructors as item 2. |
| 4. Positive uniqueness independent of SOL-EU | Token and prefix uniqueness inside the atom fragments, from the parser being a function. Yield/`Derives` uniqueness for the atom fragments is not proved, because it needs a printer premise on the atoms. |
| 5. SG-CEX-01/02 | Unchanged: OPEN/REFUTED. |
| 6. Full repository gates | See the CLOUD-RESULT of this session: `./run-lean.sh`, `register.sh --check`, `check-orphans`, doc paths, trust, axiom pins. |
| 7. Acceptance, reviews, handoff | Two rounds of finder and skeptic reviews, recorded above. This section is the handoff. |

Gate notes. `check-doc-paths.sh` fails on one reference that predates this
lane (`docs/feature-work/after-roadmap-va1.md` cites a Mathlib test path),
and the lane adds no failure. `check-axiom-pins.mjs` reports drift only for
other lanes' pins: the lane has no `#guard_msgs` pins, and none of the
reported lines is in `StatementGrammarH28`. `check-trust.sh`: 0 findings.

Full gate on `e08557db` (run after a container restart, Lake 4.24.0):
`./run-lean.sh` printed "Build completed successfully (5828 jobs)", with no
Lean errors (wall time 54 min, warm partial cache). It then exited 1 in its
last step, `scripts/check-solkey.sh` (`solkeycheck: 167 mismatch(es)`,
unknown tokens and sorts and unannotated reads in solkey storage taclets).
The branch changes nothing that step reads: its diff from
`aec9adf1` touches only `Solidity/Frontend/StatementGrammarH28/**`,
`tests/h28-sol/statement-grammar/**`, this document, the module map and the
generated root. The failure predates this lane and belongs to the solkey
annotation owners.

## Moved-lane checkpoint AA: simple statements and `for` initialisers

This checkpoint follows the coordinator's follow-up order (2026-11-06), item 1.
`AtomSimple.lean` exposes the premise on the existing `simple` parser:

    SimpleAtom x ss a :=
      ∀ n s, simple (n + a) (locatedInput (ss ++ [;]) s) = .ok (x, punctBefore ; s)

It is proved for identifier expression statements (`ident_simple_atom`,
budget 6, by `rfl`; the parser's `declHead` attempt fails and backtracks).
Otherwise it is a premise, as with the expression atoms. The first token
must satisfy `simpleHead`: it is not a statement keyword, `else`,
`unchecked`, `{`, `}`, `;` or the identifier `revert`. This is a
conservative set, not an exact one. `else` reaches `simpleStmt` but fails
there, and `;` is excluded for the `for` header's `eat ;`. `revert` followed
by a non-identifier also reaches `simpleStmt`.

The following are proved:

- `stmt_simple_dispatch`: a `simpleHead` token reaches `simpleStmt`. It is
  proved by cases on the token. The string test on `revert` is discharged
  by unfolding the matcher `stmt.match_7` and splitting its `dite`.
- `simple_stmt_coverage`.
- `simple_item_step`: the block-loop step.
- `simple_no_else` and `simple_eat_semi`: the frame and header facts.
- `for_header_prefix`, and in `AtomNested`, `for_init_step`.

`AtomStmt` gains two constructors. `simpleS` has budget `a + 1`. `forInit`
is `for (init; c; u) body` with optional atom condition and update, and has
budget `d + a + ca + va + 1`. Coverage, the item step, the no-else lemma,
nearest else, and token and prefix uniqueness extend to both.

Controls (`AtomNestedControls`) cover:

- a block `{ x; for (y; z; ) { w; } }` at derived budget 33, with coverage
  and token uniqueness;
- a kernel `rfl` parse of `x;` at fuel 13;
- refusals of `simpleHead` on `if`, `else`, `unchecked`, `{`, `}`, `;`,
  `revert` and the empty list;
- the premise naming the parsed tree.

A kernel `rfl` on the whole block exceeded the elaboration heartbeat budget.
It was dropped, not given more heartbeats.

Not claimed: any `simple` parse beyond the premise (declarations, tuple
declarations and compound expressions are covered only through it), and
the contextual `revert`-headed simple statements.

## Moved-lane checkpoint AB: `emit` and `revert`; `try` not covered

This is coordinator item 2. `AtomCall.lean` exposes two premises:

- `PathAtom e ps`: `pathExpr` reads `ps` as `e` and stops at the
  argument list's `(`.
- `ArgsAtom args as b`: `callArgs` reads `as` as `args` before `;`.

They are proved for identifiers (`ident_path_atom`) and for the empty
positional list (`empty_args_atom`, budget 1). The steps are `emit_step`
and `revert_step`. For `revert`, the dispatcher's string test on the
literal reduces, and the path must start with an identifier, which is
exactly the dispatcher's own condition.

`AtomStmt` gains `emitS` and `revertS`, both at budget `b`. Each takes the
precedence contract `e.isPathExpr = true` as a premise, because
`Syn.precNode` of `emit` and `revert` is exactly that.

Controls cover:

- `{ emit E(); revert Err(); }` at budget 8, with coverage;
- a kernel `rfl` parse of `revert Err();`;
- contextual `revert;` and `revert();`, which reach `simpleStmt` and are
  read as expression statements;
- the precedence refusal of a non-path event.

`try` is not covered. Its expression is followed by `{`, and the expression
parser's call-options check looks past that brace. Probes show that `f {}`
and `f() {}` both parse, leaving `{ }`. With a variable suffix, neither the identifier
instance nor the call instance closes by `rfl`, because `postLoop` looks
two tokens past `{` for `ident :`. A premise with that lookahead frame
would probably work, since no statement starts with `ident :`. The real
blocker is the catch-clause loop, which needs a "no following `catch`"
frame that the statement-level frame does not carry. `try` was therefore
not completed. The partial code was removed, and `try` stays in
limitations.

## Moved-lane checkpoint AC: yield and `Derives` uniqueness for the atom-condition fragment

This is coordinator item 3. The printer premise can be stated without a scope
decision:

    AtomYield c cs := ∀ L, c.yield L = some ([cs], L)

It says the existing printer yields exactly `cs` for `c`, for every layout
state. It is proved for identifiers and Boolean literals.
`AtomYields` (`AtomYield.lean`) mirrors `AtomStatements` with these
premises; Boolean witnesses embed. The following are proved:

- `atom_yields_yield`: the tree yields exactly its tokens.
- `atom_yields_derives_iff`: `x.Derives w ↔ w = ts`.
- `atom_statements_yield_unique`: two trees that have parse and print
  witnesses and derive the same words are equal.

Controls (`AtomConditionalControls`) cover:

- the dangling-else tree `if (x) if (y) {} else {}`: its print witness, its
  derivation, and that it is the only fragment tree deriving those words;
- the wrong association printing the same tokens (`rfl`), which is excluded
  by the precedence contract and not by the printer;
- the printer premise naming the printed tokens.

Not done: the same for the mutual `AtomStmt`/`AtomItems` fragment. It would
need printer premises for `simple`, path and argument atoms, a yield
relation parallel to the mutual pair, and a yield proof for blocks and
lists. No scope decision is needed; this is left as further work.

### Reviews of checkpoints AA–AB

The skeptic gave PASS-with-fixes and confirmed:

- the premises are confined to the sub-parsers `simple`, `pathExpr` and
  `callArgs`, never `stmt`, `item` or `block`;
- no earlier theorem statement changed;
- imports are acyclic.

Fixes:

- The `simpleHead` set is described as conservative, not exact.
- The `try` reason is softened, with the catch frame named as the blocker.
- The module-map row for `AtomNested` was stale and has been updated.

The finder found no soundness or coverage bugs. It confirmed the same
`simpleHead` wording issue, fixed in the Lean docstring as well. It also
found that `revert_needs_identifier` checked only token consumption; the
control now checks the root constructors through the G0 twin
(`simpleStmt`, `exprStmt`, `ident` or `call`). Two premises are noted as
redundant but harmless, and are kept as stated: the `(` head of
`emitS`/`revertS` follows from `ArgsAtom`, and `isPathExpr` follows from
`PathAtom`.

Final gate on `6bcbf5d7`. `./run-lean.sh`: "Build completed successfully
(5831 jobs)". The new modules were replayed from artifacts whose Lake traces
match the current sources. The script exits 1 only in the same solkey step,
which predates this lane (`167 mismatch(es)`). `check-orphans`:
5815 reachable, 0 orphaned. `check-trust`: 0 findings. Axiom pins: no lane
entries. Doc paths: the same reference that predates this lane, and nothing
new.
## Checkpoint Y: global atom continuation-token absence

H55-H58 file reservations are honored: all edits stay in the original exclusive
statement-grammar paths; no reserved Yul file or producer was edited and no HOLD
was entered. Existing frozen goal and original base are retained. Work starts
from integrated master `70845978ab616a63b13d0dee8b31b28893ccf591`.

ControlFreePr, ControlFreeAtoms and SyntaxControlFree prove that successful
expression/type/argument/parameter/declaration/simple yields contain no actual
else, catch or unchecked keyword tokens anywhere, strengthening the earlier
head-only fact. The existing boundaryToken predicate and SemiFreeCat footprint
are reused unchanged. The universal induction covers all 42 atom constructors
and recursive nil/cons/none/some wrappers over existing Syn. Only successful
actual yields and the existing category footprint are premises; no successful
parse, expression uniqueness or new source/precedence restriction is assumed.
The three keywords are excluded throughout every flattened token segment,
including arbitrary expression subtrees and successful layout choices.

ControlFree is a token-list Prop relation with inhabited empty/token/append
constructors, not an untyped AST. Literal fragment guards and function-type
attribute arrangements are the existing printer computations. The generic
keyword lemma states its exact boundaryToken=false side condition, discharged
for every scalar producer keyword. Punctuation is neutral, including semicolon;
this distinguishes the new property from SemiFree. Existing semicolon proofs,
producers, interfaces and budgets were not refactored or changed. New indexed
syntax induction constructs proofs only; new computational controls match only
on parameter-only yield options, never on Syn.

ControlFreeControls enumerates actual successful nonempty yields for all 42
constructors with exact Ctor inventories, all 5 literal classes, four generic
list/option wrappers, both mapping-key forms, optional array/location/name/init
fields, empty arguments/tuples and both function-attribute orders. Real else,
catch and unchecked tokens are negative controls. Identifiers with those
spellings and fragmented literal payload bytes remain data. An actual inhabited
if/else yield contains a control keyword and is rejected by ControlFree; invalid
fragment/layout choices remain refused. This proves token absence, not lexical
validity, general statement segmentation, parser completeness or whole-language
uniqueness. No new external solc fixture or compiler correctness claim is made.

The committed audit inventory is self-contained:

| Committed source | Explicit audit entries |
|---|---:|
| [ControlFreePr.lean](../../Solidity/Frontend/StatementGrammarH28/ControlFreePr.lean) | 21 source theorems |
| [ControlFreeAtoms.lean](../../Solidity/Frontend/StatementGrammarH28/ControlFreeAtoms.lean) | 18 source theorems |
| [SyntaxControlFree.lean](../../Solidity/Frontend/StatementGrammarH28/SyntaxControlFree.lean) | 4 source theorems |
| `ControlFree.empty`, `.token`, `.append` | 3 relation constructors |
| `ControlFreeParts` | 1 predicate definition |
| [ControlFreeControls.lean](../../tests/h28-sol/statement-grammar/ControlFreeControls.lean) | 23 control theorems |
| Total | 70 constants: 43 source theorems, 3 constructors, 1 definition, 23 control theorems |

[ControlFreePublicAxioms.lean](../../tests/h28-sol/statement-grammar/ControlFreePublicAxioms.lean)
lists every source signature and axiom query. The control file lists its own
axiom queries and kernel-checked constructor inventories: 29 expression,
5 type-name, 2 call-argument, 1 named-argument, 1 parameter, 1 variable-declaration
and 3 simple-statement constructors, totaling 42. Nil, cons, none and some are
four additional generic closure cases. These committed declarations and tests
are the inventory; reviewing it does not require a VM-only JSON file.

At checkpoint head `1b1391e3fa6ff56edd3ef8e5fad7ef64eca1c3c5`, all 96 VM checks
passed (93 owned builds, controls, public audit and KeySort). The complete audit
reported 56 constants without axioms, 5 using `propext`, and 9 using `propext`
and `Quot.sound`. Lean was 4.24.0 and Lake 5.0.0-src+797c613. A line-oriented
evidence collector initially rejected one wrapped axiom printout; the complete
multiline output was then parsed against all 70 expected names without changing
source, rerunning passed checks or relabeling a failed Lean gate.

On the prepared task VM, reproduce the focused checks with:

```sh
python3 tests/h28-sol/statement-grammar/runtime.py build Solidity.Frontend.StatementGrammarH28.ControlFreePr
python3 tests/h28-sol/statement-grammar/runtime.py build Solidity.Frontend.StatementGrammarH28.ControlFreeAtoms
python3 tests/h28-sol/statement-grammar/runtime.py build Solidity.Frontend.StatementGrammarH28.SyntaxControlFree
python3 tests/h28-sol/statement-grammar/runtime.py gate tests/h28-sol/statement-grammar/ControlFreeControls.lean
python3 tests/h28-sol/statement-grammar/runtime.py gate tests/h28-sol/statement-grammar/ControlFreePublicAxioms.lean
python3 tests/h28-sol/statement-grammar/runtime.py gate Solidity/KeySort.lean
```

The following run IDs and `/workspace` paths locate historical execution
receipts on that VM. They supplement the committed inventory above.
Per-file source diagnostics pass: run-1793932818689100266,
run-1793932857929873010 and run-1793932917015203868. Final controls diagnostics:
run-1793933442590916776. Builds have no new warnings and maxHeartbeats is unchanged.
Initial setup run-1793932748629497010 failed before any source edit/check because
the documented temporary lock directory was absent after restart. The directory
was recreated; all subsequent writes/checks acquired the same documented lock.
That failed setup is retained and never counted as a proof pass.

Separate read-only finder and skeptic source reviews pass with no findings;
neither used Lean, servers, builds, solc or writes. Final acceptance additionally
requires exact committed-head VM builds/controls/axiom/KeySort gates and evidence
review. Results, exact commands/exits/timing/RSS, hashes, cache receipt and sealed
handoff are linked from
`/workspace/h28-statement-grammar-evidence/checkpoint-y-validation.json` and
`/workspace/h28-statement-grammar-evidence/checkpoint-y-locations.json`.
New modules have only local registration rows; no generated roots, shared maps
or trust inventories are authored. H41 packs stay on the VM for coordinator
pull with path/SHA; never run ship-cache.sh here.

Original G11 remains partial: general compound/item framing and association,
remaining true parser coverage, full repository gates and whole-scope acceptance
remain open. SOL-EU remains excluded and SG-CEX-01/02 remain OPEN/REFUTED.
Existing shared inventory/full-build holds remain separate. No goal was created,
reset, replaced or marked complete by this checkpoint.


## Checkpoint Z — inline-Yul continuation boundaries

Adopted published master `38d38d87e74376d6b95daf9b792fa884333f20b3`
by verified fast-forward, preserving the owned branch and its original base.
This checkpoint is additive: no existing implementation or proof was refactored,
no protected Yul helper file was edited, and no budget or premise changed.

[The source](../../Solidity/Frontend/StatementGrammarH28/YulControlFree.lean)
proves `yul_yield_controlFree` for every existing `Syn c` whose category is
Yul statement, expression or case, with arbitrary nested list/option closure.
`yul_yield_no_continuations` extracts absence of the exact three Solidity
keyword tokens selected by `boundaryToken` from every actual successful yield.
`assembly_yield_controlFree` covers arbitrary EVM flags, flag strings and Yul
bodies under the immutable printer. The result does not require parser success,
expression uniqueness, lexical validity, valid assembly flags or execution
adequacy. Identifier/string payload spellings remain data. SG-CEX-01 is retained:
this token-absence property does not establish flag injectivity or round-trip.

The exhaustive constructor inventory is 11 Yul statements (`yulBlock`, `yulLet`,
`yulAssign`, `yulExprStmt`, `yulIf`, `yulFor`, `yulSwitch`, `yulLeave`, `yulBreak`,
`yulContinue`, `yulFun`), three expressions (`yulPath`, `yulCall`, `yulLit`),
and one `yulCase`, plus `nil`, `cons`, `none`, `some` closure. The scalar literal
proof covers all five `YulLit` alternatives: decimal, hexadecimal, string,
hex string and Boolean. No constructor is represented by an empty relation.

[Kernel controls](../../tests/h28-sol/statement-grammar/YulControlFreeControls.lean)
have 10 theorems: exact constructor inventory; all 15 inhabited successful
nonempty yields; all five literal alternatives; absent initializer/default and
empty call/function alternatives; actual four list/option yields; atomic keyword
payload spellings; all four EVM/nonempty-flag combinations; rejection of real
Solidity continuation keywords; rejection of the Solidity-statement category;
and the arbitrary-Yul-tree three-keyword corollary. The public source has four
theorems and one category definition. [Public audit](../../tests/h28-sol/statement-grammar/YulControlFreePublicAxioms.lean)
prints all five source signatures and axiom sets; controls print all 10 theorem
axiom sets. Only standard `propext`/`Quot.sound` are permitted; no new trust.

Reproduction in the prepared bounded VM, serially:

```sh
python3 tests/h28-sol/statement-grammar/runtime.py build Solidity.Frontend.StatementGrammarH28.YulControlFree
python3 tests/h28-sol/statement-grammar/runtime.py gate tests/h28-sol/statement-grammar/YulControlFreeControls.lean
python3 tests/h28-sol/statement-grammar/runtime.py gate tests/h28-sol/statement-grammar/YulControlFreePublicAxioms.lean
python3 tests/h28-sol/statement-grammar/runtime.py gate Solidity/KeySort.lean
```

Initial per-file diagnostics and build passed. Separate read-only finder and
skeptic source reviews found no proof defects. Finder caught a premature receipt
claim in this paragraph; it was corrected before commit. Acceptance still requires
exact committed-head gates, cache, final review and seal receipts in the checkpoint
handoff. External solc
results are unchanged historical fixture evidence, not evidence for this universal
kernel theorem. Original G11 remains partial: general compound framing, remaining
parser coverage and final whole-repository acceptance are still outstanding.


## Checkpoint AA — universal list measures and iteration budgets

Rebased onto published `c61eac233747385d1b76aff6c9af72eb7923f43b`.
The coordinator cherry-picked Z as `bc417f403bd7c26b52c0a9dc924e49269302bd24`;
owned files were verified byte-identical before Git skipped duplicate `dcbe2ebf`.
The recovery ref `refs/backup/statement-grammar/pre-c61eac233` preserves that head.
Z's root registration is now integrated. This checkpoint adds a module and local
registration only; no old proof or implementation was refactored.

[ListMeasures](../../Solidity/Frontend/StatementGrammarH28/ListMeasures.lean)
contains exactly nine public theorems:

| Theorem | Exact scope |
| --- | --- |
| `list_length_values` | Every intrinsic list has the same G0 length and typed-values length. |
| `list_yield_length` | Every successful list yield has exactly one output chunk per element, for every category. |
| `list_yield_chunks_nonempty` | Under the explicit universal nonempty-element-yield premise, each actual output chunk is nonempty. |
| `nonempty_chunks_token_bound` | The number of nonempty token chunks is bounded by flattened token length. |
| `list_yield_token_bound` | The generic premise yields the intrinsic list-count bound. |
| `statement_list_yield_token_bound` | The premise is discharged for arbitrary statement syntax in every context. |
| `item_list_yield_token_bound` | The premise is discharged for arbitrary item syntax, including unchecked blocks. |
| `item_list_many_iteration_budget` | Token-count bound: item count plus one is at most located-input token length plus one (the `many` counter in Parser.lean); the link to `many` is not stated in Lean. |
| `statement_list_many_iteration_budget` | The corresponding universal statement-list iteration bound. |

These are universal structural measures, not parser-success assumptions.
The final inequalities establish the loop counter's capacity only; they do not
establish the per-element parser's success, nesting fuel or general completeness.
The exact generic premise is necessary: a present optional expression containing
`none` yields one empty chunk. The statement/item specializations use existing
unconditional nonempty-yield theorems, covering all 13 statement constructors and
both item forms without expression uniqueness or a framed-root restriction.
Existing G0 list observers supply all computational measures; indexed cases are
proof-only. Budgets and immutable producers are unchanged.

[Controls](../../tests/h28-sol/statement-grammar/ListMeasuresControls.lean)
contain exactly 10 theorems. They enumerate and inhabit all 13 statement roots
in an actual successful list and all 14 corresponding statement/unchecked items;
exercise attribute and fragment layouts; reject missing layout; prove actual
yields/count/budget for arbitrary natural-number width; check both empty lists
and one stopping iteration; and retain the inhabited generic empty-chunk
counterexample and its failed nonempty check. All four list/option constructors
occur in controls. The generic arity theorem still applies to that negative
example; only the nonempty-derived bound is unavailable.

[Public audit](../../tests/h28-sol/statement-grammar/ListMeasuresPublicAxioms.lean)
prints all nine signatures and axiom sets. Controls print all 10 theorem axiom
sets. Per-file diagnostics and the initial owned build passed. Separate finder
and skeptic source reviews found no defects. Exact committed-head gate, final
review, cache and seal receipts remain acceptance requirements in the handoff;
this text does not claim they already exist.

```sh
python3 tests/h28-sol/statement-grammar/runtime.py build Solidity.Frontend.StatementGrammarH28.ListMeasures
python3 tests/h28-sol/statement-grammar/runtime.py gate tests/h28-sol/statement-grammar/ListMeasuresControls.lean
python3 tests/h28-sol/statement-grammar/runtime.py gate tests/h28-sol/statement-grammar/ListMeasuresPublicAxioms.lean
python3 tests/h28-sol/statement-grammar/runtime.py gate Solidity/KeySort.lean
```

This is assigned block/list decomposition and fuel backfill. It does not close
the remaining general compound framing, structural parser coverage or final
whole-repository acceptance obligations. SG-CEX-01/02 stay explicit and SOL-EU
remains excluded. External solc fixture results are separate historical evidence.

Coordinator merge review (2026-11-06): finder and skeptic found no blocker.
The `#print axioms` lines in ListMeasures* are unpinned (no `#guard_msgs`), and
the `*_many_iteration_budget` theorems are token-count bounds that do not
mention `many`.


## Checkpoint AB — constructive catch-clause coverage

Adopted published `b6b4d158ddc1ef9092c62c5b984033fde6f2d885`, preserving
the coordinator's AA documentation qualification. AA Lean sources and controls
were byte-identical to the reviewed checkpoint before duplicate rebase skipping.
The recovery ref `refs/backup/statement-grammar/pre-b6b4d158d2` retains `cd21f8f3`.
AA's root registration is integrated. This checkpoint is additive and makes no
change to old statements, budgets, immutable producers or reserved Yul files.

[CatchCoverage](../../Solidity/Frontend/StatementGrammarH28/CatchCoverage.lean)
proves both actual `catchClause` branches. `catch_plain_prefix` exposes the exact
remaining block-parser call at fuel `n+1`. `catch_signature_prefix` exposes the
call at fuel `n+6` after a header with one Boolean parameter, arbitrary optional
clause name and arbitrary optional parameter name. Parameter type is exactly
`.elem .bool`, data location exactly `none`, and remaining parameters exactly
`nil`; arbitrary type/argument coverage is not asserted.

Bodies use the existing recursive `BooleanItemList`/`BooleanListBound` fragment,
including arbitrary finite width and nesting, with the existing open-if contract.
The sufficient catch fuels are `n+b+2` and `n+b+6`, derived from the syntax body
bound, for every excess `n` and suffix state. `boolean_catch_clauses_complete`
constructs the existential body bound from syntax; no successful parse is assumed.
The result concerns the grammar parser, not Solidity catch-signature semantic
validity: a Boolean parameter is intentionally a fixed grammar atom and is not
claimed to be a semantically valid Error/Panic payload in solc.

`BooleanCatch` is a two-constructor inhabited relation indexed by existing
`Syn (.catchClause k)`, actual tokens and sufficient structural fuel. It is not
an alternate syntax tree. `boolean_catch_coverage` proves actual parser success;
`boolean_catch_yield` preserves arbitrary remaining layouts;
`boolean_catch_token_unique` uses a common proved fuel to establish equality of
fragment trees. `boolean_catch_derives` witnesses the actual grammar derivation,
and `boolean_catch_actual_yield_unique` extracts uniqueness from successful
actual yields inside this fragment. This is restricted catch uniqueness, not
whole-statement or whole-language uniqueness. SOL-EU remains excluded.

The exhaustive public inventory is 12 source theorems: two prefix equations,
two coverage specializations, two actual-yield equations, fragment coverage,
fragment yield, token uniqueness, existential completeness, derivability and
actual-yield uniqueness. [Public audit](../../tests/h28-sol/statement-grammar/CatchCoveragePublicAxioms.lean)
prints signatures and pins axiom messages with `#guard_msgs` for all 12 plus both
relation constructors. [Controls](../../tests/h28-sol/statement-grammar/CatchCoverageControls.lean)
have 12 theorems and pin every theorem's axiom message. These local pins address
the coordinator's unguarded-message observation without changing older audits
or shared trust inventories. Only standard `propext`/`Quot.sound` are permitted.

Controls prove actual parsing at arbitrary natural-number body width/depth and
excess fuel, both inhabited catch constructors, all four optional-name combinations,
following catch/else/unchecked suffix preservation, actual derivations, rejection
of empty parameter lists, wrong headers, missing braces, zero fuel and insufficient
plain-clause fuel. These are token-level kernel controls, not new solc semantic
acceptance fixtures. The previously checked solc fixture suites remain separate.

Initial diagnostics passed after two source proof-elaboration repairs (StateT
bind exposure and list flattening) and one control arithmetic repair (`max a a`).
Raw failed iterations remain in immutable evidence; no premise/budget changed.
Exact committed-head gates, final finder/skeptic reviews, cache and sealed handoff
remain acceptance requirements, not claims already established by this prose.

```sh
python3 tests/h28-sol/statement-grammar/runtime.py build Solidity.Frontend.StatementGrammarH28.CatchCoverage
python3 tests/h28-sol/statement-grammar/runtime.py gate tests/h28-sol/statement-grammar/CatchCoverageControls.lean
python3 tests/h28-sol/statement-grammar/runtime.py gate tests/h28-sol/statement-grammar/CatchCoveragePublicAxioms.lean
python3 tests/h28-sol/statement-grammar/runtime.py gate Solidity/KeySort.lean
```

Original G11 remains partial: whole try-statement/catch-list coverage, arbitrary
catch parameter types/lists, general compound boundary framing and remaining
parser coverage/final whole-repository acceptance are open. SG-CEX-01/02 remain
explicit; no exclusion or premise has been approved or weakened here.


## Checkpoint AC — actual catch-list many coverage

Continues the sealed AB checkpoint without changing its statements or source.
[CatchListCoverage](../../Solidity/Frontend/StatementGrammarH28/CatchListCoverage.lean)
connects intrinsic clause-list syntax to the actual `manyAux` and `many`
combinators. `catchStep` names the step expression in the immutable try branch;
the existing `catchClause` remains the sole clause parser implementation. This is a parser equation,
beyond the AA token-count inequalities, whose coordinator qualification remains
unchanged.

`BooleanCatchList` is indexed by existing clause-list syntax, actual token
segments and a structural maximum of the represented `BooleanCatch` budgets.
Both nil and cons are inhabited. `boolean_catch_list_many_aux` proves success
for one counter step per clause plus stopping, with arbitrary excess counter.
`boolean_catch_list_many` supplies the actual parser counter from the proved
nonempty-yield/token-count bound and arbitrary suffix length. Clause parser fuel
is the maximum of syntax-derived bounds; no successful parse is assumed.
Actual yields preserve layouts and common sufficient fuel proves list-tree
uniqueness from flattened token equality inside the fragment.

The terminal frame `NoFollowingCatch s` is the exact token-head observation that
the catch loop stops. A following catch is greedily consumed: a checked control
shows two plain clauses returned when one is supplied as the suffix. Omitting
the frame would give a false stopping equation. This is not an approved source
exclusion or a weakening of any prior theorem. `statement_no_following_catch`
discharges the frame for **every actual following statement yield**, using the
existing unconditional continuation-head theorem, without a root-fragment or
expression-uniqueness restriction. Catch-list coverage remains restricted to
AB's clause fragment; arbitrary parameter-type and whole-try coverage are open.

The complete source inventory is 13 theorems: universal following-statement
frame; catch-step stop, fragment head, step start and concrete step success;
actual fragment list yield; universal arbitrary-catch yield head, nonemptiness
and list token bound (reusing AA); fragment count bound; actual manyAux and many
success; fragment list token/tree uniqueness. The three universal catch-yield
results are unrestricted in header atoms/body syntax, while parser coverage is
not. Existing G0 typed-list observations supply all computed syntax measures.

[Controls](../../tests/h28-sol/statement-grammar/CatchListCoverageControls.lean)
contain exactly 13 theorems: arbitrary mixed plain/signature pair-list bounds,
counts, actual many and manyAux equations; empty-list parsing; preservation of
non-catch keyword suffixes; consumed greedy catch suffix and its failed terminal
frame; zero/insufficient counter refusal; malformed/underfuelled clause refusal;
an actual non-Boolean string/memory/fragmented-literal catch yield head; both
list relation constructors inhabited; and an actual following return-statement
frame. These controls distinguish universal yield framing from restricted parser
coverage and exercise both existing catch constructors plus list nil/cons.
[Public audit](../../tests/h28-sol/statement-grammar/CatchListCoveragePublicAxioms.lean)
pins all 13 source theorem axiom messages plus both relation constructors;
controls pin all 13 of their theorem messages. Thus 28 declarations are audited.

Initial source diagnostics exposed incorrectly named indexed-induction binders
and a beta-reduction rewrite issue. The former caused cascading type errors and
a 200000-heartbeat timeout; all raw failures remain evidence. Correcting binders
and exposing the proposition fixed the proofs without raising any budget or
changing any statement. Source and control diagnostics and the preliminary
controls gate passed. Finder and skeptic both caught a duplicated nested axiom
guard introduced while pinning a shared name prefix; the trailer was rebuilt
with exactly one guard per query before commit. Exact committed-head checks,
final reviews, cache and seal
remain acceptance requirements in the checkpoint handoff.

```sh
python3 tests/h28-sol/statement-grammar/runtime.py build Solidity.Frontend.StatementGrammarH28.CatchListCoverage
python3 tests/h28-sol/statement-grammar/runtime.py gate tests/h28-sol/statement-grammar/CatchListCoverageControls.lean
python3 tests/h28-sol/statement-grammar/runtime.py gate tests/h28-sol/statement-grammar/CatchListCoveragePublicAxioms.lean
python3 tests/h28-sol/statement-grammar/runtime.py gate Solidity/KeySort.lean
```

Whole G11 remains partial. Whole try-statement header/composition coverage,
arbitrary catch parameters, general compound framing and final whole-repository
acceptance remain unfinished. SG-CEX-01/02 and the SOL-EU exclusion are unchanged.
No solc semantic catch-validity claim follows from these kernel token-parser
proofs; previous external fixture results remain separate evidence.


## Checkpoint AD — concrete try-statement composition

Rebased onto published `c460b20c15fd99d207a1297b49eb340608a129ee` after verifying
original-base ancestry and byte-identical owned Lean/tests. The recovery ref
`refs/backup/statement-grammar/pre-c460b20c` preserves `528be0a5`. AB/AC sources are now published, but their central imports remain pending;
the new try module also awaits central registration. No old proof or implementation is refactored.

[TryCoverage](../../Solidity/Frontend/StatementGrammarH28/TryCoverage.lean)
proves the actual statement parser on a restricted, inhabited try fragment:
exactly an identifier call with empty positional arguments; no return parameters;
an empty success block; a required first `BooleanCatch` and arbitrary finite
`BooleanCatchList` tail. Catch bodies retain the earlier recursive Boolean item
fragment. Identifier names are arbitrary token payload strings. This does not
cover arbitrary calls, nonempty success blocks or return-parameter variants.

Two exact prefix equations expose the actual expression/header/block composition
before catch parsing. The fixed `f() {}` header followed by a catch has definite
lookahead, so the expression parser does not consume the success block as call
options. The generalized prefix permits any locations on that following catch.
`boolean_try_coverage` then composes the actual proved catch-list `many` result
and existing typed-list inverse. Sufficient statement fuel is
`n + max firstClauseBound tailBound + 10`, for every excess `n` and suffix state
satisfying the exact `NoFollowingCatch` greedy terminal frame. No successful
parse is assumed; clause bounds are constructed from syntax in AB/AC. Existing
universal following-statement framing discharges the terminal frame when used
before any actual statement yield.

`BooleanTry.attempt` is an inhabited relation indexed by existing statement
syntax, actual tokens and the arithmetic bound. It introduces no alternate AST.
`boolean_try_fragment_coverage` and `boolean_try_fragment_yield` expose actual
parser/yield equations; common sufficient fuel proves fragment token/tree
uniqueness. `boolean_try_derives` and `boolean_try_actual_yield_unique` concern
actual derivations/layouts within the fragment. Expressions are fixed call
atoms here; SOL-EU is neither assumed nor proved. Grammar parsing of a call or
Boolean catch signature does not establish Solidity semantic try validity.

The exact source inventory is nine theorems: two prefix equations; direct
coverage/yield; fragment coverage/yield; token uniqueness; Derives; actual-yield
uniqueness. [Public audit](../../tests/h28-sol/statement-grammar/TryCoveragePublicAxioms.lean)
checks all nine signatures plus the relation constructor and pins all 10 axiom
messages with `#guard_msgs`. [Controls](../../tests/h28-sol/statement-grammar/TryCoverageControls.lean)
have 14 theorems with 14 individual axiom pins, for 24 audited declarations total.

Controls construct arbitrary natural-number catch-body depth and clause-list
width, prove actual parsing and layout-preserving yields, exercise both plain
and signature first clauses (including arbitrary optional names), plain-only
and multi-clause tries, preserve a real following return statement, and establish
an inhabited actual grammar derivation. Negative controls reject a missing catch,
missing success block, empty catch parameters and insufficient fuel. A concrete
try consumes two clauses when a second catch is supplied as suffix, retaining
the necessity of the greedy terminal frame. These are kernel token-parser
controls, not new solc semantic acceptance fixtures.

Initial diagnostics required a syntax indentation fix, explicit flattening in
the many rewrite and an explicit intrinsic context in a control helper. Raw failed
iterations remain evidence; no theorem/premise/exclusion/budget changed. Source,
controls and preliminary control gates passed. Exact committed-head gates,
final finder/skeptic reviews, cache and seal remain handoff acceptance requirements.

```sh
python3 tests/h28-sol/statement-grammar/runtime.py build Solidity.Frontend.StatementGrammarH28.TryCoverage
python3 tests/h28-sol/statement-grammar/runtime.py gate tests/h28-sol/statement-grammar/TryCoverageControls.lean
python3 tests/h28-sol/statement-grammar/runtime.py gate tests/h28-sol/statement-grammar/TryCoveragePublicAxioms.lean
python3 tests/h28-sol/statement-grammar/runtime.py gate Solidity/KeySort.lean
```

Whole G11 remains partial. General try calls/success bodies/return parameters,
arbitrary catch parameter types/lists, general compound boundary framing and
remaining general parser coverage/final whole-repository acceptance remain open.
SG-CEX-01/02 and all original exclusions/budgets are retained. Historical solc
fixture evidence is separate from these universal restricted kernel proofs.


## Checkpoint AE — universal block/call-options boundary

Adopted remote-verified `812aeb301f27d70dad4acc3b3bd92d1c41d7c948`, preserving
`65f7735f` under `refs/backup/statement-grammar/pre-812aeb301`. Owned Lean/tests
were byte-identical before the rebase. Direct inspection of the published root
confirmed imports for CatchCoverage, CatchListCoverage and TryCoverage; that
statement is based on the root contents, not inferred merely from publication.
This increment adds one owned module and local manifest row, without producer
or earlier theorem changes.

[BlockHeaderBoundary](../../Solidity/Frontend/StatementGrammarH28/BlockHeaderBoundary.lean)
proves a universal token boundary for arbitrary existing syntax under the
existing precedence contract. Named call options require an identifier followed
by a colon immediately after their opening brace. A precedence-selected block's
item list cannot have that prefix. An empty block retains its closing brace,
so even an arbitrary continuation cannot manufacture the pair.

`namedArgStart` is a token lookahead predicate, not an AST. `NoNamedFrame ts`
quantifies over every token continuation. The proof reuses the existing universal
expression/type atom-pair invariants, without expression uniqueness. All three
simple alternatives are handled, including identifier-led type/name declarations
and tuple declarations. Revert uses precisely the existing root path contract;
the other fixed roots start in non-identifiers. `statement_no_named` takes only
the existing `precNode` condition. The all-node projection and item/list lifting
then derive `block_yield_no_named_header` from a successful arbitrary block yield
and its existing full `Syn.prec` predicate, for arbitrary layouts and contents.
No new source exclusion or expression/type/argument validity premise is added.

The final two theorems concern the actual parser:
`postLoop_no_named_lookahead` proves stopping at an opening brace whose next two
located tokens are not an identifier/colon pair. `postLoop_yielded_block` derives
those observations from **every** actual precedence-valid block yield and proves
`postLoop (n+1)` preserves the supplied expression, entire block and arbitrary
suffix state, at every positive fuel. This is lookahead discrimination; it does
not establish expression uniqueness or general statement parser completeness.

The exhaustive source inventory has 13 theorems: atom-pair exclusion;
non-identifier framing; declaration-head framing; simple/revert/all-statement
framing; statement all-node root projection; item and item-list framing; block
item framing; block-yield lookahead; generic postfix stopping; yielded-block
postfix stopping. There are five public token/predicate definitions.
[Public audit](../../tests/h28-sol/statement-grammar/BlockHeaderBoundaryPublicAxioms.lean)
checks/pins all 18 declarations. [Controls](../../tests/h28-sol/statement-grammar/BlockHeaderBoundaryControls.lean)
have 17 theorem pins, for 35 inventoried declarations total.

Controls enumerate all 13 statement constructors, all three simple alternatives,
both item forms, the block constructor and nil/cons through arbitrary width.
They check actual successful precedence/yield/postfix behavior for every root,
attribute and fragmented-literal layouts (plus a missing-layout refusal), atomic
colon payloads, arbitrary-width yields and parser stopping, and arbitrary-depth
block precedence. Positive call-options input is actually consumed; its named
pair fails the block frame. Empty-block closing braces prevent continuation
capture. A colon supplied after an empty block exercises the non-identifier branch even
when the second lookahead is a colon. Zero postfix fuel is rejected, and an invalid revert path is shown to
fail the existing contract. That last control is not a counterexample to the
boundary outside the contract; no such stronger conclusion is asserted.

Checking-cost evidence: an initial attempt to try trivial roots before recursive
simplification gave matched MCP wall times 151.296 and 151.721 seconds, so the
original proof was restored. A second, targeted change unfolds `Syn.all` exactly
once per nontrivial root, then projects Boolean conjunctions. Matched fresh CLI
compilations of the same 13-theorem module took 147.43 seconds / 146.96 user
seconds / 584272 KiB peak RSS before, and 1.74 seconds / 1.55 user seconds /
463280 KiB after. Source outside that one proof was verified byte-identical;
imports, statements, toolchain, single-thread configuration and proof budgets
were unchanged. The one-step proof is retained; no >10% slowdown occurred.
Raw plans, both source versions and exact command/resource logs are preserved.
No earlier speed-motivated producer change was undone.

Initial diagnostics exposed implicit printer-predicate inference, Boolean
conjunction projection and list-map normalization issues; a control induction
needed the correct Boolean normal form. All were fixed without theorem/premise
or budget changes. The bounded CLI module build and per-file controls passed.
Exact committed-head gates, final read-only reviews, cache and seal remain
acceptance requirements in the handoff.

```sh
python3 tests/h28-sol/statement-grammar/runtime.py build Solidity.Frontend.StatementGrammarH28.BlockHeaderBoundary
python3 tests/h28-sol/statement-grammar/runtime.py gate tests/h28-sol/statement-grammar/BlockHeaderBoundaryControls.lean
python3 tests/h28-sol/statement-grammar/runtime.py gate tests/h28-sol/statement-grammar/BlockHeaderBoundaryPublicAxioms.lean
python3 tests/h28-sol/statement-grammar/runtime.py gate Solidity/KeySort.lean
```

Whole G11 remains partial. General try call/success-body/return-parameter parser
composition, arbitrary catch headers, remaining general compound framing and
parser coverage, and final whole-repository acceptance remain open. Existing
SG-CEX-01/02, SOL-EU exclusion, premises and budgets are unchanged. Kernel
lookahead proofs are separate from historical external solc fixture evidence.


## Moved-lane checkpoint AD: `try` and catch clauses in the mutual fragment

Follow-up item 1 (2026-11-06). Merged master `5af89dce` first. `AtomTry.lean`
states four sub-parser premises, each stopping at the next block's `{` (or,
for `ExprAtomReturns`, at `returns`):

- `ExprAtomBrace e es a`: `expr` reads `es` as `e` before a success block
  whose body is not headed by `ident :` (`NoNamedFrame`, the call-options
  lookahead of `postLoop`; Codex `BlockHeaderBoundary`). Proved for
  identifiers (`ident_expr_brace`, budget 5) with `postLoop_no_named_lookahead`.
- `ExprAtomReturns e es a`: `expr` stops at `returns` (identifiers, by `rfl`).
- `RetsAtom rets rs r` on `returnsOpt` (empty, `returns (bool)`).
- `ParamsAtom ps pts a` on `paramsParen` (`(bool)` and `(bool x)`).

`try_step` and `catch_sig_step` are the actual parser equations from those
results; `catches_many` turns the catch loop's token-length counter into the
recursive count. The catch loop is greedy, so a `try` must not be followed by
`catch`. Requiring that of every statement would weaken the earlier coverage
theorems, so the frame is conditional, like the else frame: `catchOpen`
marks the statements whose last sub-statement is a `try` (`try`, and `if`,
`while`, `for` through their last body), and `CatchFrame x s :=
catchOpen x = false ∨ NoFollowingCatch s`.

`AtomStmt` gains `tryS` (no return parameters; side condition
`BlockBodyParts parts` on the success block) and `tryRets`. The mutual block
gains `AtomCatch` (`plain`, `sig`) and `AtomCatches` (lists), with coverage
by mutual structural recursion (`atom_catch_step`, `atom_catches_many_aux`).
Budgets: `a + b + f + g + 2` (expression, success block, first clause, tail
list), `+ r` with return parameters; a clause has `b + 2` or `a + b + 2`.

Changed statements, all in this lane's own moved-lane modules:
`atom_stmt_coverage` takes the extra `CatchFrame x s`, and
`atom_stmt_prefix_unique` takes catch frames for both suffixes;
`atom_stmt_token_unique` is unchanged. The general coverage theorem is
slightly weaker: a tree without `try` must now discharge the new frame too,
and no lemma did so in general (superseded by
`catch_frame_of_no_try` in checkpoint AH). Every earlier control discharges it by
computation (`Or.inl rfl`, or `Or.inl (by cases n <;> rfl)` for the
arbitrary-depth family). `simpleHead` now also excludes `catch`, which is
needed for the no-catch lemma. The dispatch lemma's statement is unchanged
in form, but its `simpleHead` premise is stronger by `catch`; the parser
never reads a `catch`-headed simple statement. `catchOpen` matches on the
indexed family; it is a proof-level frame, reduced only by `rfl` in
controls, and is not on the kernel-observer (fixture) path.

Controls (`tests/…/AtomTryControls.lean`): a try with a plain and a signature
catch at derived budget 37 (coverage at every catch-free suffix, token
uniqueness), a try with `returns (bool)`, a try inside a block followed by a
statement (any suffix), `if (c) try …` (catch-open through the then-branch),
and kernel `rfl` parses of `try f {} catch {}`. Negative: with a second
`catch` as suffix the actual parser reads both clauses (`try_greedy_catch_kernel`),
a `catch` suffix fails the frame, and a success body starting with `x :` fails
`BlockBodyParts` and is read by the actual expression parser as call options
(`named_body_call_options`, kernel).

## Moved-lane checkpoint AE: assembly, and the `isRethrow` link

Follow-up item 2.

**Gate G0 link.** `G0Rejections` now defines `g0IsRethrow`, a twin of
Source's `isRethrow` reading the Yul body through five `Syn.casesOn` views
(`listViewAt`, `yulExprStmtAt`, `yulCallAt`, `yulPathAt`, `yulLitAt`) and
the `Cat`-indexed result family `listViewResult`. Lean 4.24 still generates no equation lemmas for
`isRethrow.match_1`, but the link does not need them. The twin inspects the
tree in the matcher's own preorder (head statement, call name, arguments,
`add` arguments, path, literal, `mload`, the remaining tails, the outer
tail), so `g0IsRethrow_eq : g0IsRethrow b = isRethrow b` is proved by case
analysis in that order: each mismatched constructor reduces both sides
(`rfl`), and each failed string or number test (`revert`, `add`, `32`,
`mload`) is discharged by `delta isRethrow isRethrow.match_1` and
`dif_neg`. Axioms: `propext`, `Quot.sound`. The proof names the
auto-generated matcher `isRethrow.match_1`, so a toolchain re-pin must
recheck it. The node twin's assembly
exclusion calls `g0IsRethrow` (link `excl_assembly`), so the fixture
observers no longer reach `isRethrow`. The four accepted assembly fixtures
(Cases 22, 23, 24, 27) and `FixtureData` re-check by `decide +kernel`. The
elaboration audit lists the six new views (26 targets).
`G0ObserverControls.g0_rethrow_twin_actual` evaluates the twin by the kernel
on the canonical body, on a different path, name and offset, on a trailing
statement and on the empty body, and through `g0Rejections` on assembly.
This closes the residual recorded in moved-lane checkpoint Y: no lane
observer reaches an indexed-family `match`. The producer's own `parse` is
the system under test and is out of scope, as before.

**Assembly statements.** `AtomAsm.lean` states `YulBodyAtom` on `yulBody`
and `FlagsAtom` on the flag list `sepBy1 (strArg "assembly flag")` before
`)`; the `"evmasm"` dialect is data (`evmToks`). `AsmFlags` is the optional
parenthesised list. `asm_step` is the actual `assembly` branch. Instances:
the empty body, the single flag `"memory-safe"`. An elaborator `rfl` for the
rethrow body exceeded the heartbeat budget (not raised), so that body is
covered by a kernel parse of the whole statement in the controls
(`rethrow_asm_kernel`, which also checks through the linked twin that it is
not rejected). `AtomStmt.asm` has budget `a + 1`. The accepted assembly
fixtures' statements were therefore not covered by the `AtomStmt` relation
(superseded for the Case 24 rethrow statement in checkpoint AH; Cases 22,
23 and 27 have other Yul bodies and remain outside the relation). A refusal control covers an
unknown dialect string.

## Moved-lane checkpoint AF: revert-headed statements

Follow-up item 3. The dispatcher reads `revert` as a revert statement only
when the next token is an identifier; otherwise it falls back to
`simpleStmt`. `revertExprNext` names that side, and `revert_expr_dispatch`
proves the fallback for every non-identifier next token. `AtomStmt.revertExpr`
covers `revert …;` expression statements through `SimpleAtom` (budget
`a + 1`), next to the existing `revertS`. Controls: the block
`{ revert; revert Err(); revert(); }` (two `revertExpr` and one `revertS`),
and `revertExprNext` refusing every identifier, so the two forms never share
tokens.

## Moved-lane checkpoint AG: `Derives` uniqueness for the mutual fragment

Follow-up item 4: yield uniqueness among statements of the mutual fragment
that carry both a parse and a print witness. `AtomDerives.lean`
states the printer side of each atom as `Prints t parts` (the existing printer
yields `parts` and consumes no layout choice) or `PrintsTo t ts` (its yield
flattens to `ts`). The print relations `AtomStmtP`, `AtomItemsP`,
`AtomCatchP` and `AtomCatchesP` mirror the four parse relations with the same
token indices. Their printer premises sit on expressions, simple statements,
arguments, parameters, return parameters, Yul bodies and flags (as a token
equation), never on statements, items, blocks or clauses. Proved by mutual
structural recursion: `atom_stmt_prints` (and for items, clauses, clause
lists); then `atom_stmt_derives_iff : x.Derives w ↔ w = ts` and
`atom_stmt_yield_unique`: two trees with parse and print witnesses that derive
the same words are equal. Instances: identifiers, identifier expression
statements, empty arguments, `bool` parameters, empty lists.

Controls (`tests/…/AtomDerivesControls.lean`): a block holding a try with a
signature catch, `revert;`, `assembly {}` and an `unchecked` block, with both
witnesses, its `Derives` set, uniqueness against every tree with both
witnesses, and the printer's tokens computed by the kernel (the printer is
part of the system under test, like the parser); print witnesses for every
remaining constructor (loops, conditionals, `return e;`, all `for` headers,
a two-clause catch list, `try … returns`, flagged assembly, `revert Err();`,
`emit E();`); negative controls for other words, a wrong print premise, and
the outer dangling-else association, which has a print witness but no parse
witness (`outer_else_not_parsed`).

Not claimed: a derivation of `AtomStmtP` from `AtomStmt` plus atom printer
premises, and item- or clause-level uniqueness corollaries.

Not claimed: printer premises beyond the stated instances, and any
expression-level printing or parsing fact.

### Reviews of moved-lane checkpoints AD–AG

Read-only finder and skeptic reviews (no Lean server, no builds) of
`8c78af2a..a1003dd0`. Skeptic verdict: PASS-with-fixes. Neither review found a
soundness bug. Both confirmed that every new premise sits on a sub-parser or
sub-printer, that `catchOpen` covers every catch-open statement form, that
`g0IsRethrow` checks the same shape as `isRethrow` and is Gate-G0-compliant,
and that no lane observer still reaches `isRethrow`. They also confirmed that
`AtomStmtP` mirrors all 19 `AtomStmt` constructors and that every new parse
constructor is inhabited. Fixes:

- Finder: the module-map row for `G0Rejections` still named `isRethrow` as
  a residual; the `AtomAsm` docstring cited a nonexistent `asmFlags`. Both
  are fixed. Nits are fixed: view count, the `returns` stop, the
  `bool_rets_atom` instance, the arbitrary-depth frame.
- Skeptic 1: most `AtomStmtP` constructors had no control. Added
  `loops_print_relation` and the dangling-else pair
  `outer_else_print_relation`/`outer_else_not_parsed`.
- Skeptic 2: the item-4 claim was too strong. It is reworded to uniqueness
  among trees with both witnesses, and the non-claims are listed.
- Skeptic 3 and 4: the coverage theorem's weakening and the stronger
  `simpleHead` premise are now stated, not denied.
- Skeptic 5–7: the assembly fixtures are outside the relation; `catchOpen`
  is not on the observer path; `g0IsRethrow_eq` depends on the generated
  matcher name. All three are recorded.
- Skeptic 8, a possible "no goals" after `prints_simp`, was refuted: the file
  checks clean.

### Gates for moved-lane checkpoints AD–AG

Lean MCP per-file diagnostics, severity error, all clean:

- `AtomTry`, `AtomAsm`, `AtomCall`, `AtomSimple`, `AtomNested`, `AtomDerives`,
  `G0Rejections`;
- `FixtureControls/Case22`, `Case23`, `Case24`, `Case27`;
- `tests/…/AtomNestedControls`, `AtomTryControls`, `AtomDerivesControls`,
  `G0ObserverControls`, `G0ElaborationAudit`.

`#print axioms` for every new theorem is within `propext` and `Quot.sound`.

`./run-lean.sh` ran twice; neither run completed.

- First run (cold cache, 6003+ jobs, started at `a1003dd0`). Three modules
  outside the lane were killed with exit 137 (out of memory):
  `Checked/UnitExamples`, `Examples/Tactics/OpenLoops` and
  `TestSuite/Derived7`. No module failed with a Lean error.
- Second run (warm, at `1311182e`). Only `Checked/UnitExamples` was killed
  (exit 137). Every lane module built: `AtomNested`, `AtomDerives` and the
  four assembly fixture cases appear as built.

`Checked/UnitExamples` is unchanged by this lane and by the merged master.
While it built, the Lean language server held about 3 GB. Stopping the
server was refused by the session's permission policy. `check-solkey.sh`,
the script's last step, was therefore not reached in either run.

| Check | Result |
| --- | --- |
| `register.sh --check` | pass |
| `fragments.sh --check` | pass |
| `check-layers` | pass |
| `check-orphans` | 6384 reachable, 0 orphaned |
| `check-trust` | 0 findings |
| `check-doc-paths` | one missing reference, the same one that predates this lane (`after-roadmap-va1.md`) |

## Moved-lane checkpoint AH: coordinator follow-up (catch frame, rethrow body)

The coordinator asked for four more steps on 2026-11-06.

1. **General catch frame.** `catchOpen_false_of_no_try`: a statement with no
   `try` node (`Ctor.tryStmt ∉ x.nodes.map Node.ctor`) is not catch-open.
   It is proved by structural recursion on the statement. `catch_frame_of_no_try`
   states the same over the G0 node twin, so the hypothesis can be checked by
   the kernel. `atom_stmt_coverage_no_try` is coverage of a `try`-free
   statement under the else frame alone. Controls:
   `revert_block_coverage_no_try` (node inventory by `decide +kernel`) and
   `try_tree_has_try` (the lemma does not apply to a tree with a `try`). This
   removes the weakening recorded in checkpoint AD for abstract families:
   every `try`-free witness gets its catch frame from the lemma. For a
   concrete tree, `Or.inl rfl` on `catchOpen` remains the cheapest check: it
   looks only at the last-body spine, so it also succeeds for trees that hold
   a `try` inside a block. The lemma's hypothesis over all nodes is stronger
   than necessary; a spine-only version was not stated.
2. **Rethrow Yul body.** `rethrow_yul_body : YulBodyAtom … 6` proves the
   canonical body `{ revert(add(raw, 32), mload(raw)) }` at every fuel of at
   least 6 and every suffix. Heartbeats are not raised. Small `rfl` steps are
   composed by rewriting:
   - the two inner calls (`yul_add_call`, `yul_mload_call`);
   - the argument list (`rethrow_call_args`, through `sepByAux_comma` and
     `sepByAux_rparen`);
   - the outer call (`yul_call_prefix`, `rethrow_call_expr`);
   - the statement (`yul_stmt_call_prefix`);
   - the body loop (`yul_body_prefix`, `yulItemStep`, `many_aux_cons`).

   `AtomStmt.asm` now covers the accepted rethrow fixture's statement
   `assembly ("memory-safe") { … }` (`rethrow_asm_relation`, budget 7, with
   coverage at every suffix). Its tokens are copied by hand from the fixture
   source; they are not the lexer's output on `p24-canonical-rethrow.sol`. The note in checkpoint AE that this body is
   only a fixed-fuel kernel parse is superseded.
3. **`AtomStmtP` from `AtomStmt`: not derived, and why.** The parse premises
   (`ExprAtomSemi`, `SimpleAtom`, `ArgsAtom`, …) say that a sub-parser reads
   the tokens back to the tree. They say nothing about the printer. Deriving
   the print premises from them needs a printer-after-parser round trip for
   expressions, simple statements, arguments, parameters and Yul bodies. That
   round trip belongs to the expression lanes (it implies SOL-EU-type facts),
   so it is outside this lane. The two relations stay separate, and
   uniqueness needs both witnesses.
4. **Full gate:** below.

### Gates for moved-lane checkpoint AH

- Lean MCP per-file diagnostics, severity error, all clean: `AtomNested`,
  `AtomAsm`, `tests/…/AtomTryControls`, `AtomDerivesControls`.
- `#print axioms`: every new theorem is within `propext` and `Quot.sound`.
- `LEAN_NUM_THREADS=2 ./run-lean.sh` at `65f452c8`: "Build completed
  successfully (6400 jobs)". With two threads, no module was killed for lack
  of memory. The script still exits 1, in its last step: `check-solkey.sh`
  against the unpinned `../solkey` reports "167 mismatch(es)", as in earlier
  runs. That step reads nothing this lane changes.
- `SOLKEY_RULES=tests/migration/solkey/…/solidityProgramRules.key
  scripts/check-solkey.sh`, the pinned rules: "OK — annotations match",
  377 taclets.
- `register.sh --check`, `fragments.sh --check` and `check-layers`: pass.
- `check-orphans`: 6384 reachable, 0 orphaned.
- `check-trust`: 0 findings.
- `check-doc-paths`: one missing reference, the same one that predates this
  lane.

### Reviews of moved-lane checkpoint AH

Read-only finder and skeptic reviews of `1311182e..ec45eb58`. Skeptic verdict:
PASS-with-fixes. Neither review found a soundness issue. Both confirmed:

- `yulItemStep` is the parser's own loop step;
- `catchOpen_false_of_no_try` covers all 13 statement constructors;
- `rethrow_yul_body` holds at every fuel of at least 6 and every suffix, with
  no heartbeat raise;
- the gate reporting is accurate.

Fixes made:

- Stale "not covered" and "no lemma" sentences in checkpoints AD and AE now
  point forward to AH.
- The module-map row for `AtomAsm` names `rethrow_yul_body`.
- A no-op rewrite in `AtomAsm` was dropped; the file re-checks clean, and the
  change is a proof step only.
- The catch-frame claim was narrowed: `Or.inl rfl` stays the minimal check
  for concrete trees.
- The hand-copied fixture tokens are now stated.

The finder also noted that budget 6 is not tight; 5 suffices. The doc does
not claim tightness, so this is left as is.
