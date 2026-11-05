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
at /home/guilherme/.local/state/cloudvm-coord/receipts/ and confirms its
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
