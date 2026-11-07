# H28 G09 type-name grammar exactness

Status: **STOPPED by human H82 retirement; successor handoff pending integration**.
The original owned conditional proof/fixture scope is preserved. Per H67 the
current re-cut excludes all G07 inventory/fragment changes; reconciliation belongs
to a separate one-off job. Earlier pin-check results are historical, not current
candidate acceptance. Fresh full validation remains unperformed for this re-cut.
Successor: `solidity-sol2-20261104/numeric-literals`. No new proof work or automatic
continuation is authorized. See `tests/h28-sol/type-grammar/handoff/` for the
complete original rendered assignment, exact scope and full work/backfill queue.
The tool cannot set PAUSED: only complete/blocked goal outcomes are exposed.
The existing goal was not completed/reset; coordinator PAUSED transition remains.

## Frozen scope and source identities

Base: `6f3eedf0788ee1f8a3bcf230558c712ecdca04d5`.
Branch: `codex/solidity-h28-sol-20261104/type-grammar`.
Checkout: `/workspace/solidity-lean`.
The fetched `origin/master` and fetched exact published base both equal that
base at setup. The assigned branch was created at it from a clean checkout.
No push, admission/lowering change, producer implementation edit or lane-authored
shared-root change. The coordinator-authorized master adoption is recorded below.
Local central-integration manifest:
`Solidity/Frontend/TypeGrammarH28/registration.json`.

`tests/h28-sol/type-grammar/inventory.json` pins eight read-only inputs by
SHA-256. The grammar is Solidity 0.8.38, upstream commit
`1835d247de183f23e7b0e2bc4a50732af525b77c`; source rules 129–131,
358–369 and 547–551 are the parameter, type and mapping contracts. The
upstream grammar checker validates the repository-wide mapping separately.
SOL-QN name resolution and SOL-CB constant evaluation remain excluded.

## Complete constructor and field inventory

| Source constructor | Grammar / actual yield | Boundaries and layout consumption |
| --- | --- | --- |
| `elem e` | `elementaryTypeName[true]`; `Elem.toks` | No layout. `address payable` is two tokens; all other elementary constructors one. |
| `userType p` | `identifierPath`; nonempty token path `.ident head` followed by dot/identifier pairs | No layout. Strings themselves are not lexically validated by `Syn`. No name resolution. |
| `array t len` | `typeName [ expression? ]` | Base yield first, then length yield. Dynamic `.none`; static `.some e`. Length expressions are read-only syntactic atoms, including their layout. Arbitrarily many suffixes and arbitrarily nested base types. |
| `mapping key keyName value valueName` | `mapping ( mappingKeyType identifier? => typeName identifier? )` | Key is elementary with intrinsic `e ≠ addressPayable`, or a qualified path. Both names independent optional strings. Only the value's subtree consumes layout. No constant evaluation or key resolution. |
| `fnType params vis mu returns` | `function ( parameterList? ) attributes* (returns (parameterList))?` | Pops its attribute choice before parameter layouts, then return layouts. Empty return list means absence of the returns clause; parser refuses explicit `returns ()`. Both lists have unbounded length. |

All eight `Elem` constructors: `address`, `addressPayable`, `bool`, `string`,
`bytes`, `int signed bits valid`, `fixedBytes n valid`, `fixed signed dims`.
Integer signedness has two cases and widths range over multiples of eight in
8–256. Fixed bytes range 1–32. Fixed point has two signedness cases, `none`
(alias dimensions) or `some` dimensions with width a multiple of eight in
8–256 and decimal digits 0–80. Bounds and proof fields stay intrinsic.
No literal spelling or numeric value is collapsed by this lane.

Each `param` carries a recursively nested type, an optional location
(`memory`, `storage`, `calldata`), and an optional name. Parameters and return
parameters use the same constructor. The list constructors are `nil` and
`cons`; comma separators occur only between elements. No trailing comma in a
parameter list. Parameter names and locations are emitted after its type.

Visibility has all four source cases: `internal`, `external`, `priv` (`private`),
`pub` (`public`). Mutability has `pure`, `view`, `payable`. Syntactic grammar
support does not imply solc semantic admissibility of a function type.
For the two independently optional fields there are exactly five layout
shapes: `[]`, `[vis]`, `[mutab]`, `[vis, mutab]`, `[mutab, vis]`. `arrange`
requires every present slot exactly once and consumes no unrelated slots.
Parameter and return types may themselves be functions, mappings or arrays.

## Parser and fuel contracts

`typeName 0` fails. At successor fuel it dispatches on elementary, function,
mapping or identifier tokens, then always calls `typeSuffix` at predecessor
fuel. `typeSuffix 0` fails even at EOF; successor fuel consumes one suffix or
returns the unchanged base. A static suffix calls the existing `expr` parser
at predecessor fuel, then recursively consumes further suffixes.

`fnType` adds one fuel layer and calls `paramsParen`, `fnTypeAttrs 3` and
`returnsOpt`; `paramsParen` adds one and calls `param` for each comma-separated
element; `param` adds one and calls `typeName`. `mappingType` adds one and
calls `typeName` for the value. `returnsOpt` adds one and calls `paramsParen`
when the keyword is present. A second visibility ends a function attribute
run; a second mutability fails. The fixed three-step attribute fuel is not a
type nesting bound. List repetition uses the producer's existing parser
combinators; proving sufficient fuel also requires their boundary contracts.

`parseCatLocated` uses `16 * (tokenCount + 1)` fuel, requires EOF, exact yield
under all consumed choices, and `Syn.prec`. `parseType` projects its result.
Existing `parseType_derives` proves successful checked parses derive their
lexed tokens and satisfy precedence; it does not prove parser completeness
or type-name uniqueness. Existing `sameTree`/`parsesTo` controls compare nodes
and yields, not actual `Syn` equality. They cannot substitute for that theorem.

## Initial checkpoint proof boundary and preserved counterexample

`Layouts.lean` defines successful exact layout equivalence using a shared
successful token yield; two failures do not satisfy it. Symmetry and
transitivity are proved. Universal elementary and qualified-name lemmas show
their actual `yield` preserves every layout suffix, their empty canonical
layout succeeds, and any unused choice makes their exact `toks` fail.
These lemmas make no claims about non-atomic constructors.

`Counterexamples.lean` preserves the false raw-yield uniqueness claim using
two actual array type names with length syntax `(1 + 2) + 3` versus
`1 + (2 + 3)` (the parentheses here describe tree grouping, not emitted
tokens). Both emit `bool[1+2+3]` and the trees differ. The existing precedence
contract accepts the left-associated length and refuses the right-associated
one. No expression uniqueness theorem is proved or assumed. A future complete
type theorem must spell out the independent length-atom equality and boundary
contracts it uses, and cannot silently infer them from type uniqueness itself.

The passing build log records empty axiom signatures for eight declarations.
`elem_toks` and `userType_toks` depend on the standard Lean axiom `propext`;
no new axiom is declared. Earlier failed elaboration is preserved separately:
it emitted compiler recovery `sorryAx` diagnostics for two erroneous `rfl`
proofs. The source never introduced `sorry`; the proofs were corrected using
`List.append_nil`. A failed log is not acceptance evidence.

## Evidence and queue accounting

Evidence lives under `tests/h28-sol/type-grammar/evidence/`. Every bounded gate
writes its exact command, wall time, sampled aggregate RSS, exit, container
limits and OOM state. Docker limits are 12 GiB, memory+swap also 12 GiB (zero
swap), one CPU, `LEAN_NUM_THREADS=1`, and explicit `-j1`; the minimum of host availability and finite enclosing-VM cgroup headroom
reserves 4 GiB and a 600-second guard stops the owned container. No
heartbeat or proof budget was raised. An earlier proof-checking refactor has
matched before/after evidence below; subsequent local repairs make no speed claim.
MCP runs in its own 12 GiB/no-swap serial container with at most three files;
a lifetime heavy-runtime lock excludes builds, and its supervisor applies the
same host/enclosing-VM headroom guard. It is stopped before bounded build gates.
Call MCP diagnostics under the repository writer lock, as in the saved evidence. The direct compiler build confirms
new imports; per-file MCP diagnostics confirm the edited files.

Runtime gate: Lean 4.24.0 (commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`), Lake
5.0.0-src+797c613. `Solidity/KeySort.lean` passed under the actual bounded
runtime before `RUNTIME_GATE_PASS`. Runtime evidence:
`tests/h28-sol/type-grammar/evidence/h28-type-a7819be1b45c.log`.
Passing initial proof build:
`tests/h28-sol/type-grammar/evidence/h28-type-66f3e83d4f06.log`.
The inventory check is an external Python check, not a kernel proof.

| Queue item | Current status and remaining obligations |
| --- | --- |
| 1: inventory/source contracts | Complete: every constructor/field/clause, eight immutable source pins, local registration and all 29 fixtures enumerated; source reviews accepted. |
| 2: arbitrary-depth decomposition and exact yield uniqueness | Complete under explicit finite local length-atom contracts and frozen precedence: actual token prefix/remainder decomposition, AST identity and successful layout equivalence for every original constructor; original raw-yield false claim preserved. |
| 3: constructive parser converse/completeness | Complete under the same explicit local atom contracts: all original constructor/parameter/list clauses, positive constructive fuel within the unchanged frozen bound, actual raw/checked/source corollaries; source soundness has no atom premise. |
| 4: controls, solc fixtures, coverage/trust, reviews, handoff | Proof/control/fixture scope reviewed: all 18 modules and 444 statements, all constructor families, true nested/mixed inhabitants and refusals, 13,218 positive/23 negative cases, exact signatures and per-area reviews. Final full-project acceptance and final sealed handoff remain blocked/pending. |
| Backfill | Assigned list/suffix/canonical-layout lemmas implemented as needed. No whole-expression/unit uniqueness. |

The current full policy retry passes touched builds, trust, layers, doc paths,
axiom pins, TestSuite, corpus and strict automation. run-lean, roots and orphans
fail because shared Solidity.lean registration is reserved to the integration
owner. run-lean stops before its default-target/TestSuite build and sort check;
separate bounded execution of both unaffected commands now passes.
No failed gate is waived by the local manifest. The original persistent goal
remains unfinished. Later sections preserve chronological checkpoint history;
this table is the current queue accounting.

## Initial checkpoint review and handoff

Separate read-only finder `/root/inventory_finder` and skeptic
`/root/inventory_skeptic` used no Lean server. Both accepted this initial content
after corrections, explicitly leaving full-assignment acceptance open. Their
findings and resolutions are saved in
`tests/h28-sol/type-grammar/evidence/reviews-initial.json`.
The axiom-report error was fixed; guards now account for enclosing-VM cgroup
headroom and exclude heavy-runtime overlap. The inventory checker now checks
all five attribute-layout shapes exactly, including distinctness. Guard controls
exercise finite and unlimited cgroups and cross-process overlap refusal.

The first guarded MCP shutdown did not save its resource record before the
bridge's five-second shutdown window. The supervisor now stops only its owned
container with a one-second grace and saves its record in time. Diagnostics in
`mcp-reviewed-shutdown.json` exited zero. The separate resource record
`mcp-resource-88dacac6c284.json` records unchanged sources, no guard, minimum
headroom 15,018,897,408 bytes, and shutdown signal 15 followed by container exit
137. That 137 is an explicitly requested shutdown; it is not reported as a
passing diagnostic exit or as an observed OOM result.

Additional external checks passed: `bash scripts/check-trust.sh` (3674 sources,
285 inventoried sites, zero findings), `node scripts/check-layers.mjs` (559 core
modules, zero forbidden reaches), `node scripts/check-axiom-pins.mjs` (6343 pinned
theorems, zero errors/unrecorded changes), and
`bash scripts/check-doc-paths.sh` (all references resolve; 46 pre-existing
ambiguous references remain visible). Individual command, exit, timing and
output records are saved under the evidence directory. Global axiom pins do
not register these new local modules: their ten actual axiom signatures are
separately recorded by `#print axioms` in the passing target build.

This is a reviewable partial implementation checkpoint. A full library/final
build, roots/orphan integration (owned centrally), all-constructor/solc fixtures
and scope-complete acceptance are pending. The frozen persistent objective is
not completed or blocked by this checkpoint. Continue next with the explicit
array-atom boundary contract and arbitrary-depth type/list/suffix decomposition;
then independently supported parser completeness with constructive fuel.

## Compositional layout checkpoint

`Composition.lean` adds sixteen checked declarations over actual `Syn.yield`.
`YieldExact t choices items` means the chosen layout prefix produces exactly
those items and preserves every remaining choice suffix. The five type
constructor rules are `exact_elem`, `exact_userType`, `exact_array`,
`exact_mapping` and `exact_fnType`. List/parameter rules are `exact_params_nil`,
`exact_params_cons` and `exact_param`; optional length rules are
`exact_no_length` and `exact_some_length`.

The array rule requires independent `YieldExact` contracts for its base and
optional length. The static-length rule requires the length expression's own
suffix-stable yield; it does not prove expression uniqueness, balance, parsing,
constantness or evaluation. The function rule supports every attribute order
with an explicit successful `arrange` premise, and records its actual pre-order
choice before parameter/return choices. This premise is about the independent
attribute arrangement function, not the desired type-name uniqueness theorem.
No constructor or valid layout is removed to obtain these implications.

`params_cons_decompose` is a converse for any successful parameter-list cons
yield: it constructs the intermediate remaining choices, head item stream and
tail stream. It does not claim that the consumed choices have already been
proved a prefix of the input, nor that token commas are uniquely decomposed.
`exact_toks` discharges the producer's whole-layout check from `YieldExact`;
`exact_layout_equivalent` gives successful exact layout equivalence from the
same complete items. It does not assert syntax equality from equal tokens.

The inhabited controls are `exact_dynamic_depth`, a constructive theorem for
every natural-number depth of actual dynamic-array nesting;
`exact_empty_function`, showing an attribute choice is still required for an
empty function type; and `exact_nested_layout`, checking the exact token stream
and preserved arbitrary layout suffix for a mapping/function/array combination
with parameter location/name and mapping key/value names. These do not replace
the still-required full constructor/attribute/solc control suite.

The bounded composition build passed in 2.620 seconds, sampled aggregate RSS
306,589,696 bytes, cgroup peak 112,410,624 bytes, no guard/OOM, minimum observed
VM/host headroom 15,227,166,720 bytes, unchanged source hashes:
`tests/h28-sol/type-grammar/evidence/h28-type-c89e98d03c97.json` and matching log.
Host-sampled aggregate RSS and cgroup accounting are different measurements.
MCP diagnostics for the edited file passed with zero errors. Two earlier
case-elimination witness errors are retained in `composition-iteration1.json`
and `composition-iteration2.json`; only proof witnesses changed.

The sixteen new axiom signatures are nine empty signatures and seven
`[propext]`: `exact_params_cons`, `exact_array`, `exact_fnType`, `exact_toks`,
`exact_layout_equivalent`, `exact_dynamic_depth`, `exact_empty_function`.
All 26 local exact source theorem statements and observed axiom sets across the three modules
are inventoried in `tests/h28-sol/type-grammar/evidence/local-axiom-signatures.json`.
No new axiom, unsafe declaration, trust shortcut or raised heartbeat budget.

The original pinned inputs and exclusions are unchanged. The initial sealed
checkpoint is commit `e585bae41f851d8af888aa6d43ff8baaed51d85d` with immutable
artifacts at `/workspace/scratch/h28-type-grammar/checkpoint-e585bae41f85/`.
Universal delimiter/boundary decomposition, type-name syntax uniqueness,
independent parser completeness/constructive fuel, parseType corollaries,
all-constructor solc fixtures and final whole-assignment acceptance are still
open. Separate read-only finder and skeptic reviews accept this composition content; full-assignment acceptance remains open.

Composition review record: finder accepted proof content, requested refreshing the
queue-2 description and recording full type signatures rather than only names.
Both are fixed: queue 2 now distinguishes layout composition from token boundary
uniqueness, and the signature manifest now contains every exact source theorem
statement, module path and observed axiom set. Skeptic accepted without further
findings. Neither reviewer used Lean server or modified files. Trust and layering
checks were rerun after the new module: 3675 sources / zero trust findings;
559 core modules / zero forbidden reaches. Local inventory covers all three
task modules, in addition to the original eight source pins and complete type
constructor/field families. These are checkpoint gates; final full builds,
all-constructor fixture acceptance and scope-complete reviews remain pending.

## Arbitrary-depth token boundary checkpoint

`Boundaries.lean` imports only the read-only token definitions. `Balanced`
is an independent grammar generated by plain tokens and matched parentheses,
brackets and braces; `Region stop` additionally excludes a boundary at its own
depth, while permitting boundaries inside balanced groups. Neither relation
mentions `Syn.yield`, the type parser, type-name uniqueness or expression
uniqueness. They have constructive inhabited controls, including a theorem
for every list of nested delimiter kinds, not a bounded sample depth.

`cut` is a token-only proof device structurally recursive on the input. It is
not an operational type admission/lowering path and does not modify the frozen
parser. `balanced_cut` proves arbitrary balanced content at a nonempty stack
preserves scanning of every continuation. `region_cut` gives the corresponding
top-level composition law. `region_cut_boundary` constructs an exact split
when the continuation is EOF or begins with a boundary. `boundary_unique`
then proves equal input token lists have identical region prefixes and
boundary remainders. It assumes only the independent region derivations and
boundary-start facts, not the conclusion of type-name uniqueness.

`cut_suffix` independently proves every successful scan, from every starting
stack, consumes a prefix and retains exactly its remaining suffix. Region and
balanced concatenation lemmas support composition. Negative controls refuse
mismatched closes and unterminated groups; an explicit positive control keeps
nested commas inside the outer region. `arbitrary_nested_boundary` quantifies
over every list of all three delimiter kinds and every continuation.

The final minimized target build is
`tests/h28-sol/type-grammar/evidence/h28-type-08ba07ac82d1.json` and matching log:
exit zero, no warnings/guard/OOM, unchanged sources, 3.241 seconds wall time,
314,806,272 bytes sampled aggregate RSS, 118,951,936 bytes cgroup peak, and
14,821,847,040 bytes minimum enclosing-VM/host headroom. Fresh MCP diagnostics
in `mcp-Boundaries-minimized.json` report zero errors. The fresh supervisor
record is separate from the earlier editing-session record, which correctly
reports changed sources during interactive proof development. An intentional
supervisor shutdown exit is never counted as a passing diagnostic exit.

All 28 boundary theorem statements and actual axiom signatures are added to
the local inventory: nineteen empty signatures and nine `[propext]` signatures.
The initial target build exited zero with two unused-simp warnings and a
`Quot.sound` dependency in the prefix-composition helper; that log is retained.
The final helper uses direct congruence, the unused simp arguments are removed,
and the final signatures contain no `Quot.sound`. Four earlier diagnostic
failures and their corrections are retained in `boundaries-iteration*.json`.
There is no speed claim or production refactor; timing observations are raw
individual gate measurements, not a matched performance experiment.

At that generic-boundary checkpoint, actual type-name yield region membership was still open.
That integration still requires elementary/path token lemmas, all five type
constructor composition rules, list/parameter/return and attribute boundaries,
and an explicit independent balanced-length-atom contract. Token boundary
uniqueness does not imply expression identity. Type syntax uniqueness, parser
completeness/constructive fuel, parseType corollaries, full solc fixtures and
final scope-complete acceptance remain open. Separate checkpoint reviews
accepted this generic token-boundary content.

Coordinator publication: fetched `origin/master` now equals published commit
`b419c3cf4f642ae519b66bebc26cdf2f7cf93574`. The original branch/head were
preserved. The four frozen type-grammar inputs are unchanged between the
assigned base and that publication; the listed new producer APIs do not supply
this lane's missing grammar proofs. Publication/ancestry/input-diff evidence is
saved in `coordinator-publication-b419c3cf.json`. No merge/reset or transported
cache availability is assumed.

Boundary review follow-up: finder accepted the proofs and requested saving the
updated external signature check and clarifying its disclaimer. Skeptic accepted
the proofs but found that the checker did not bind current proof bytes to the
cited axiom evidence. The checker now requires a successful unchanged-source
gate and an exact SHA-256 match for each current module. A fresh bounded
`AxiomAudit.lean` imports all four current modules and prints all 54 theorem
axiom sets without adding declarations. Its gate
`h28-type-023b6776cc76.json` exited zero with unchanged sources and records the
current hashes, including the audit file. Every current signature record now
cites that fresh audit, including the older theorems. The original logs remain
visible; stale logs cannot satisfy current-source signature coverage. This is a
local declaration-axiom audit, not full compiler correctness or final lane
acceptance. Both separate read-only reviewers accepted this evidence-linkage correction; neither used Lean server or modified files.

Boundary checkpoint handoff: finder and skeptic separately accepted proof,
source-hash-linked evidence and documentation after the checker correction.
Their verdicts and retained findings are recorded in `reviews-boundaries.json`.
This adds a generic boundary proof component; the persistent goal remains
active, with actual type-yield integration and the rest of the full queue open.
Next work is to connect the independent region grammar to elementary/qualified,
array, mapping and function yields with explicit length-atom balance, and then
to discharge the remaining syntax/parser obligations. No excluded producer,
source semantics, H16/H22/H21 file or proof budget was changed.

## Actual type-yield boundary checkpoint

`Solidity/Frontend/TypeGrammarH28/TypeRegions.lean` proves actual producer-yield region membership for every
intrinsic type constructor, parameter and parameter list. The local coverage
matrix `type-regions-coverage.json` enumerates all five type constructors,
parameter/list clauses, fields, helper obligations, controls and exclusions.
Elementary/path/key token lemmas quantify over the full intrinsic data, and
`arrange_region` covers every successful attribute order. Parameter and return
lists have unbounded length. No supported constructor or layout is removed.

`LengthBalance len` is the independent atom contract: every successful actual
yield of that optional length has balanced tokens. It assumes neither expression
identity nor parsing, constantness or evaluation. `TypeAtomsBalanced`,
`ParamAtomsBalanced` and `ParamsAtomsBalanced` collect exactly those obligations
in the actual type tree; they do not traverse or reinterpret expression ASTs.
The inductive certificates have eight constructor iff lemmas, preserving all
clauses of the initial uncommitted recursive formulation. Dynamic lengths and
every numeric literal have inhabited contracts without constant evaluation.

`type_yield_region`, `param_yield_region` and `params_yield_regions` use the
mutual certificate induction recursors with nonrecursive, actual-yield
constructor lemmas. Thus the child-region results are induction hypotheses,
not assumed conclusions of the desired type-name uniqueness theorem.
`type_toks_region` covers whole-layout successful yields. `typeStop` handles
commas and all three closing delimiter kinds. `type_toks_boundary` constructs
an exact token split retaining the boundary; `type_token_boundary_unique`
proves equal inputs have equal type token prefixes and remaining suffixes.
`params_first_boundary` additionally decomposes the first item of an actual
nonempty parameter-list yield, preserving its comma or following boundary.
These are token decomposition/uniqueness claims, not syntax-tree identity.

Constructive controls cover every dynamic-array depth, every boundary
continuation, every numeric-literal atom, the existing nested mapping/function/
array type with names and data location, and actual refusal of missing,
incomplete or wrong-kind layouts. The raw-yield syntax counterexample remains
unchanged; token balance does not discharge expression identity or precedence.

Before the uncommitted certificate refactor, checking-time impact was announced
and three matched per-file checks were recorded. Median wall time changed from
4.545s to 2.078s (ratio 0.4572); the >10% slowdown stop was not triggered. Both
sets use the same runner/toolchain/CPU/thread/stack/memory/no-swap settings.
The old source snapshot and exact trials are retained in
`type-regions-wf-before.lean.txt` and `type-regions-matched-comparison.json`.
The final representation adds explicit iff clauses and constructor proof lemmas;
the comparison measures the complete edited file, not just one helper. No proof
budget was raised, no axiom allowlist widened, and no general speed claim is made.

The first uncommitted proof used well-founded recursion, produced unused-simp
warnings and depended on `Quot.sound`; that build and five failed diagnostic
iterations are retained. The final target build
`h28-type-0d67e4043652.json` exits zero without warnings/guard/OOM, with unchanged
source hashes: 3.186s wall time, 334,413,824 bytes sampled aggregate RSS,
136,933,376 bytes cgroup peak and 7,994,458,112 bytes minimum VM/host headroom.
The final target and the 108-theorem fresh axiom audit contain no `Quot.sound`
or `Classical.choice`. Fresh diagnostics for both the module and audit pass;
a fresh supervisor record binds the unchanged proof sources. Every current
statement/axiom record cites `h28-type-8d4b9101390d.log`, with matching current
proof-byte hashes enforced by the unchanged signature checker. The existing
`[]`/`[propext]` axiom acceptance was not broadened.

This completes actual-yield delimiter/region integration under the stated local
atom contract. Syntax-tree uniqueness with exact layout equivalence, independent
parser converse/completeness with constructive sufficient fuel, parseType
corollaries, full solc positive/negative fixture coverage and final scope-complete
gates/reviews remain open. Separate checkpoint reviews accepted the conditional actual-yield integration. Existing
SOL-QN/SOL-CB exclusions, intrinsic representations, frozen producer inputs and
other owners' files remain unchanged.

Actual-yield checkpoint handoff: separate read-only finder and skeptic accepted
all 54 new theorem statements and the explicit local atom premises. Both
confirmed all five constructors, all parameter/list/attribute clauses, the
unchanged original 38 statement signatures, eight clause-equivalence lemmas,
substantive inhabited/negative controls, current-source axiom linkage and the
matched checking-time guard. Neither used Lean server or modified files.
`reviews-type-regions.json` records their checkpoint-only verdicts. The 54 new
axiom sets are 28 empty and 26 `[propext]`; all 108 current local statements and
axiom sets are audited without widening the existing allowlist. The full goal
remains active; syntax identity, parser completeness, solc coverage and final
whole-assignment acceptance are not claimed by this handoff.

The first documentation-path check before staging the new module reported its
bare filename as missing: that checker resolves basenames only among tracked
files. The module was present but untracked at that check. Its documented
reference is now the full repository path, and a fresh post-tracking check is
saved separately. The initial failed result remains visible and is not counted
as a passing gate. Proof source bytes and all axiom/signature evidence are
unchanged by this documentation correction.


## Elementary parser and suffix checkpoint

`Solidity/Frontend/TypeGrammarH28/ParserBasics.lean` adds 18 statements.
Every elementary constructor has raw completeness at every fuel at least two,
for arbitrary locations, choice state and EOF offset. Located-list splitting
preserves actual positions. Dynamic suffix consumption handles every depth,
base type and located prefix and preserves the exact trailing state. Its
explicit terminal `eat '[' = false` premise prevents greedy suffix consumption
from being silently truncated. This is suffix completeness, not full rooted
array or static-length parser completeness. Zero fuel and insufficient one-fuel
elementary parsing have actual refusal controls. The artificial one-token
addressPayable raw input parses but cannot reproduce that token via actual
yield; the actual checked parser rejects it. This artificial input is not
claimed to be produced by the lexer.

`Solidity/Frontend/TypeGrammarH28/ParserChecks.lean` adds ten statements.
The generic checked-category converse/iff records all three frozen guards:
EOF, exact yield, precedence. It explicitly assumes a raw result. Elementary
completeness independently discharges that premise at the existing
16*(token-count+1) fuel; source parseType completeness and its elementary iff
retain only the independent successful lexical token contract. Elementary
yield injectivity follows from two proved raw parses at common fuel two,
using parser determinism rather than an assumed identity theorem. Successful
exact elementary layout equivalence is included; no equality of general
layout witnesses is inferred.

The MCP runtime initially lacked the shared local Lake artifact-cache mount
and selected the default config for setup-file. Import-only isolation showed
an unintended dependency rebuild without explicit -j1, stopped by the
unchanged 4 GiB headroom guard. The task shim now selects its alternate config
for both serve/setup-file and mounts the same existing cache as bounded builds.
No cache transport, producer edit, cap increase or budget increase occurred.
`mcp-check-import-runtime-repair.json` and failed resource records preserve the
observations. An initial hypothesis about a concrete proof was not the
confirmed cause. Full restored-file diagnostics now pass for both new modules
and the complete audit; import-only isolation is not acceptance evidence.

Two failed audit invocations are retained: direct `lake env lean` could not
resolve a cached dependency; then the dependency-aware `lake lean` needed its
documented `--` argument separator. The repaired invocation passes explicitly
with -j1 and stack 131072. Four provisional elementary completeness signatures
included Quot.sound from arithmetic automation. An explicit natural-number
bound removes it without weakening any statement. The fresh audit
`h28-type-7eb3da22354c.json` passes, source unchanged, 4.911s wall time and
300,503,040 bytes sampled aggregate RSS. All 136 statements have current-source
hash-bound signature records; the 28 new sets are 21 empty and seven propext.
The allowlist remains empty/propext only. Individual new-module builds,
fresh per-file MCP diagnostics, inventory, signature coverage and resource
guard controls pass. Earlier failures are not counted as passing gates.

Separate read-only finder and skeptic accepted this checkpoint with no
confirmed findings; neither used the Lean server. Their scope and verdicts are
saved in `reviews-parser-elementary.json`. These proofs establish elementary
completeness/identity and dynamic suffix consumption only. Qualified, mapping,
function, static-length and full rooted-array completeness, all-type identity,
solc grammar fixtures, final full gates and full-scope acceptance remain open.
The persistent goal remains active. No in-profile constructor is excluded.


## Qualified-name parser checkpoint

`Solidity/Frontend/TypeGrammarH28/ParserPaths.lean` adds 21 statements.
The locally named pathStep is definitionally the frozen idPath loop; actual
path_complete unfolds the producer and uses the independent loop proof.
Every IdPath depth and every actual located prefix is covered. The loop fuel
bound follows from the number of path segments and their token count, with no
assumed type completeness or identity premise. Prefix completeness explicitly
states both terminal recognizers (path segment and array suffix); EOF theorems
discharge them. Original choices and actual trailing token locations remain
unchanged. Checked completeness uses the frozen 16*(count+1) budget, and source
parseType completeness/iff require only the independent successful lexical
projection. Actual IdPath equality and successful exact layout equivalence
follow from genuine complete parses at common fuel two. These are syntax
claims; SOL-QN name resolution remains outside scope.

Negative controls leave lone periods and period/elementary pairs unconsumed,
and prove actual checked rejection of a trailing period at its real source
position. Universal positive contracts cover all qualified paths rather than
only fixed-depth samples. Neither grammar constructors nor valid path depths
are narrowed.

The fresh all-module audit `h28-type-df11c51667c0.json` passes with unchanged
source hashes, exit zero, no guard/OOM, 6.325s wall time and 332,431,360 bytes
sampled aggregate RSS. All 157 current statement signatures match that audit;
the 21 new sets are eight empty and thirteen propext. Inventory, resource
controls and fresh per-file MCP diagnostics for the module and audit pass.
No axiom allowlist or proof/resource budget changed.

One MCP request stalled after an import change while its worker was idle. The
owned runtime was explicitly stopped; that request exited with MCP server
exited and is not a pass. A fresh session returned actual proof diagnostics.
The local repairs normalized cons_append before a rewrite and used the exact
frozen fuel expression with explicit Located-list typing in the negative
control. No explicit sorry/admit/axiom was introduced. Exact failed-iteration
timings were not captured; `parser-paths-iterations.json` records this evidence
limitation rather than pretending those observations are measured gates.

Separate read-only finder and skeptic accepted this checkpoint, with no
confirmed finding and no Lean-server use. `reviews-parser-paths.json` records
the verdicts. Mapping/function/static-length/full rooted-array completeness,
all-type syntax identity/layout equivalence, solc grammar fixtures, final full
gates and whole-assignment acceptance remain open. The persistent goal stays
active and the original false raw-yield claim remains preserved.


## Rooted dynamic-array parser checkpoint

`Solidity/Frontend/TypeGrammarH28/ParserArrays.lean` adds 32 statements.
For every elementary or qualified base and every dynamic-array depth k,
actual typeName completeness is proved at k+2 and every greater fuel, with
arbitrary actual locations, choices and EOF offsets. Actual elementary token
spelling (including address payable) and qualified-path parsing are composed
with the earlier independent suffix theorem. Neither whole-type raw success
nor type identity is assumed. The frozen 16*(count+1) checked fuel is sufficient
by a constructive token-length bound. Actual yield, precedence and layout
consumption are proved separately; source parseType corollaries require only
the independent lexical projection. Same-family syntax identity and exact
successful layout equivalence follow from independently complete checked
parses, including different candidate depths. Unused layout choices fail.

Universal positive contracts are inhabited for every supported base/depth.
Universal negative controls prove suffix fuel k and root fuel k+1 fail at the
original EOF position after the k bracket pairs; this makes the sufficient
fuel result substantive. The mixed elementary/qualified equal-yield implication
is the disjointness case, whose two premises cannot both hold. It is not
presented as an inhabited equal-yield positive control. The same-family
identity theorems supply inhabited cases. Static lengths and dynamic arrays
over mapping/function bases remain open; this is an intermediate constructor
checkpoint and introduces no exclusion from the original task language.

The fresh audit `h28-type-3c1628ca2a29.json` passes with unchanged source hashes,
exit zero, no guard/OOM, 6.839s wall time and 343,445,504 bytes sampled aggregate
RSS (139,673,600 cgroup peak). All 189 theorem statements are current-source
hash-bound. New axiom sets are eleven empty and twenty-one propext; no allowlist
or budget changed. Fresh MCP diagnostics for the module and complete audit,
inventory (nine modules), exact signature coverage and resource controls pass.
Failed local iterations needed explicit intermediate states, actual dispatch
normalization, the Boolean conjunction iff and lexer-match reduction. Their
exact timings were not captured; `parser-arrays-iterations.json` preserves that
limitation. Failed proof/error propagation is not an accepted axiom signature.
No explicit sorry, admit or axiom was added.

Separate read-only finder and skeptic reviewed all 32 statements without the
Lean server. Source review found no confirmed issue and identified the
mixed-family result as disjointness. Final trust verdicts are recorded in
`reviews-parser-arrays.json`. Mapping/function and static-length completeness,
full array/whole-type identity, solc fixtures, final full gates and full-scope
acceptance remain open. The persistent goal remains active.


## External grammar fixture checkpoint

`tests/h28-sol/type-grammar/fixtures.json` enumerates all 29 fixture files,
source SHA-256 identities, clauses, compiler pin and exact type strings. Six
positive source files contain 13,219 generated field positions, reducing to
13,218 distinct positive type strings; 23 files supply negative grammar
controls. Enumeration covers 5,287 canonical elementary spellings plus both
integer aliases, all 5,286 elementary mapping-key spellings, qualified paths,
both optional mapping names and all five value constructors, all 32 function
attribute value/order variants crossed with nine parameter and nine return
variants (2,592 combinations), all data locations/names, multiple-item lists,
static/dynamic arrays and nested mapping/function/array boundaries through
depth 32. The generator and complete manifest enumerate every fixture; no
sample-only constructor inventory is used. Universal syntax claims still need
the remaining proofs.

Pinned solc is 0.8.38+commit.1835d247.Emscripten.clang, SHA-256
`6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`,
downloaded from its public solc-bin path into task-owned scratch. The exact
URL, size and verification are recorded in `solc-download.json`. Node is
v24.19.0. Compilation uses stopAfter parsing and AST output. Undefined names,
nonconstant lengths and semantically inadmissible location/visibility forms
remain parsing controls; no name resolution, constant evaluation, operational
admission, lowering or code generation is claimed. Negative failures must be
ParserError. Actual checked Lean parseType executes every exact generated type
string and compares the outer constructor with its solc declaration node.
This is an external execution/root-kind check, not a kernel theorem, complete
AST equality or compiler-equivalence proof. No native_decide or trust shortcut
is used.

The first extraction used FunctionTypeName.src and produced 2,598 Lean test
failures because those spans included the following identifier/delimiter.
That failed data/report is preserved in the bad-ast-spans evidence. The repair
uses all original generated type strings, checks their bytes at actual parsed
ContractDefinition child declaration starts, checks every variable index/name
and total field count, and takes its actual type-node kind. It neither trims
strings nor filters by Lean success. A later failed gate filtered on stateVariable and selected no declarations
in parsing-only output; selecting actual AST parent context repaired it. These failures remain non-passing evidence.

Separate finder and skeptic identified two acceptance-guard gaps. An
unexpectedly accepted negative could dereference missing type_sources before
saving a result; it now reports FAIL safely. Empty/stale/truncated type data
could previously pass the IO loop. The new external preflight validates the
current manifest/compiler/source pins, successful complete solc receipt, hash
of the consumed case bytes, and exact positive/negative source membership and
provenance. The bounded Lean gate runs it before Lean, and Lean additionally
checks both total and polarity counts. Five negative guard controls refuse
empty, truncated, duplicate, inverted and misattributed data. Both reviewers
accepted the repaired checkpoint; `reviews-fixtures.json` records the fixes.

Final solc gate `h28-type-e6ec9c2c12b9.json`: exit zero, all 29 fixtures pass,
4.222s wall time, 237,944,832 bytes sampled aggregate RSS. Final Lean fixture
gate `h28-type-f50f04acfd5e.json`: exit zero, preflight passes, 13,218 positive
and 23 negative cases with zero failures, 7.938s wall time, 367,525,888 bytes
sampled aggregate RSS. Both preserve source hashes, no swap, memory/headroom
limits and exclusive serial execution. An attempted fresh MCP check hit the
unchanged 4 GiB headroom guard; its failure and resource record are preserved.
The permitted standalone file gate passed with lower runtime overhead. No
cache eviction, resource-accounting change or proof budget increase occurred.
The earlier syntax iteration used a reserved keyword and was corrected without
overriding evaluation errors; its exact timing was not captured.

The refreshed final-tooling audit `h28-type-73427ddbe57c.json` passes with all
189 unchanged proof statements and empty/propext axiom sets only, 4.757s wall
time and 303,673,344 bytes sampled aggregate RSS. Exact signature, fixture
coverage, resource controls and source inventory checks pass. Runtime identity
remains Lean 4.24.0 / Lake 5.0.0-src+797c613 with the already-recorded permitted
KeySort pass before RUNTIME_GATE_PASS. No new full-project gate pass is claimed.
Mapping/function/static-length/full array proofs, whole-type identity with
explicit atom dependencies, final full gates and whole-assignment acceptance
remain open. The persistent goal stays active.


The full staged whitespace check reported trailing spaces in raw compiler
stdout on accepted-fixture lines. Those immutable logs remain verbatim; that
check is recorded as failed in whitespace-fixtures-full.json. The staged
source/documentation/JSON/fixture check excluding only raw stdout logs passes
in whitespace-fixtures-source.json. No source whitespace finding is hidden.


## Recursive stopping-context checkpoint

`Solidity/Frontend/TypeGrammarH28/ParserContexts.lean` adds 19 statements.
The Boundary certificate independently enumerates eleven sufficient continuation
shapes: EOF, an optional-name identifier, the three closing delimiters, comma,
semicolon, mapping arrow and all three data-location keywords. It contains no
type-parser-success premise. Actual producer stop facts are proved for payable
lookahead, array suffix, qualified path, function attributes (all initial
values/orders/fuel) and optional returns. Elementary, qualified and arbitrary
dynamic-array prefixes preserve every actual remaining token/location, original
choices and EOF offset. CompleteAt records a genuine raw prefix contract with
explicit returned layout and sufficient budget; its four instances are
constructively inhabited for all elementary/path values and all array depths
using budgets two and k+2. No whole-type identity/completeness premise is used.

Boundary is sufficient, not a necessary or exhaustive characterization of all
possible stopping contexts. Its four exclusion theorems concern certificates
for an opening bracket, every visibility, every mutability and returns; they
are not parser-refusal or language-exclusion claims. An elementary type can
legitimately stop before public elsewhere, although Boundary does not certify
that token. These local sufficient contexts cover the nested field/list
continuations needed next; no original in-profile type form is removed.

The initial MCP attempt hit the unchanged four-GiB headroom guard, with no
active Lean job left. Enclosing cgroup usage was then dominated by clean file
pages. A subsequent resource-only operation used POSIX_FADV_DONTNEED on
read-only Lean artifact descriptors under both writer and heavy-runtime locks.
It advised 23,112 files (9,440,956,849 bytes), checked unchanged inode/size/mtime/
ctime for every descriptor, reported no error, and recovered guarded available
headroom from 4,458,749,952 to 10,162,548,736 bytes. No artifact was deleted or
modified; no cache transport, Mathlib update, cap/accounting/swap change or
proof-budget raise occurred. `clean-file-page-release.json` records the actual
before/after cgroup statistics. This happened after the fixture checkpoint.
The next checks may be cold; their times are not a matched speed comparison
and no code refactor or speed claim is made.

Fresh module/audit MCP diagnostics pass with unchanged proof sources. The full
208-statement audit `h28-type-8eab89362929.json` passes: exit zero, no guard/OOM,
6.896s wall time, 323,133,440 bytes sampled aggregate RSS, 120,569,856 bytes
cgroup peak. All statement/axiom records bind current proof hashes; the 19 new
sets are eleven empty and eight propext. Source inventory (ten modules), exact
signatures, resource controls and current external fixture preflight pass.
Separate read-only finder and skeptic accepted this checkpoint with no
confirmed finding and no Lean-server use; `reviews-parser-contexts.json`
records the certificate nuance and checkpoint-only trust verdicts.

The added contracts prepare recursive mapping/function/list proofs. They do
not complete those constructors or static-length expression dependencies.
Universal remaining-constructor completeness, whole-type syntax identity/layout
equivalence and final whole-assignment gates/reviews/handoff remain open.
The persistent goal stays active.


## Mapping constructor and certificate checkpoint

`Solidity/Frontend/TypeGrammarH28/ParserMapping.lean` adds 44 statements.
Actual elementary/path key parsing, the intrinsic non-payable-key invariant,
both optional names and every actual marker/field location are covered.
TailExact is a Prop naming the frozen producer subterm after its key; it is
not a replacement operational parser. Its proof is discharged from a strict
value child's independently established CompleteAt contract. Actual mapping
body and typeName prefix completeness then follow at child budget plus two,
with all original choice state and trailing positions preserved. Actual yield
and precedence preservation/converse are proved separately. A constructive
length inequality proves the frozen 16*(count+1) fuel sufficient and derives
checked/source parseType corollaries and soundness/converse characterizations.
No whole mapping-parser success is assumed by its constructor proof.

Certified names the universal successful-yield/precedence completeness TARGET:
for each original successful layout, it must construct a possibly different
parsed layout and a raw prefix certificate, exact successful yield and
sufficient Nat budget bounded by the frozen wrapper. Its generic checked,
source and identity/layout projection theorems explicitly assume that target;
they are not evidence that every type already satisfies it. certified_mapping
constructs the parent target from strict-child certification only. Elementary,
qualified and arbitrary dynamic-array bases independently instantiate it.
Original layout witnesses are not equated, and the original false raw-yield
identity claim/counterexample remains unchanged.

Control builders use existing intrinsic mapping fields with independently
varying keys and optional names at every depth. Arbitrarily deep mapping chains
over arbitrary-depth elementary/qualified dynamic arrays discharge every
certificate, yield and precedence obligation. Their syntax identity and exact
successful layout equivalence require no certificate premise left over.
Universal inhabited controls exhibit actual token yields and actual checked
parses for every such frame/depth choice, rather than relying only on
conditional equality implications. Two universal negative parser controls
separately reject an artificial one-token payable key and its real two-token
address-payable spelling, at exact actual source/error positions. No name
resolution, expression evaluation, lowering or operational type admission is
claimed.

Fresh module/audit MCP diagnostics pass. The all-module audit
`h28-type-f7330c1853bd.json` passes with unchanged source hashes: exit zero,
no guard/OOM, 9.997s wall time, 355,635,200 bytes sampled aggregate RSS and
152,383,488 bytes cgroup peak. All 252 statement/axiom signatures are bound to
current proof bytes. The 44 new sets are twelve empty and thirty-two propext;
no allowlist, intrinsic producer representation or proof budget changed.
Inventory (eleven modules), exact signatures, resource controls and current
external fixture provenance/coverage pass. Local failed proof iterations and
their repairs are recorded in parser-mapping-iterations.json; exact individual
iteration timings were not captured. Automatic error-recovery axioms in those
failed checks are not accepted proof signatures.

Separate read-only finder and skeptic accepted all 44 statements and the fresh
trust audit with no confirmed finding, neither using the Lean server.
`reviews-parser-mapping.json` records their checkpoint-only verdicts and the
conditional-certificate distinction. Function and static-length certification,
arrays around mappings, global certification/type identity and final full
gates/reviews/handoff remain open. Constructor preservation does not discharge
those remaining obligations or narrow the original language. The persistent
goal remains active.


## Dynamic closure around mappings

`Solidity/Frontend/TypeGrammarH28/ParserDynamicClosure.lean` adds 20 statements.
Actual dynamic-array yield and precedence decomposition/converse apply to every
base type. The crucial raw parser proof composes mappingType body completion
before the real greedy typeSuffix call; it never assumes typeName can stop
before an opening array bracket. A strict value child's budget B and k suffixes
give the explicit conservative sufficient budget B+k+2. Its frozen token-count
bound and certificate preservation are proved independently, retaining actual
locations, remaining tokens, EOF and layout order.

The proof-only DynamicMappingGrammar control family covers arbitrary mapping/
dynamic-array interleavings with arbitrary keys and optional names, over every
elementary/qualified base. Each member independently has a real token yield,
true precedence and an actual checked parse. Identity/successful layout
equivalence and source parseType characterizations follow with no certificate
premises left over for this family. A universal negative yield control refuses
every unused layout choice. This family is an inhabited control, not a
replacement for the original assignment language. Function roots and static
lengths remain mandatory unfinished cases.

Separate read-only finder/skeptic accepted every new statement and the fresh
272-statement audit without findings or Lean-server use. The new axiom sets
are two empty and eighteen propext. Fresh module/audit diagnostics pass.
The reviewed audit `h28-type-66db517edf62.json` passes in 7.879s with
325,607,424 bytes sampled aggregate RSS. After the fixture isolation correction
below, `h28-type-9c8bb13234b0.json` rechecks the final tooling snapshot: exit
zero, no guard/OOM, 6.853s wall time, 303,214,592 bytes sampled aggregate RSS,
96,579,584 bytes cgroup peak. Both audits bind identical proof bytes; all 272
current statement/axiom records cite the final audit. Inventory now covers
twelve modules, signatures and current fixture provenance pass. No allowlist,
producer interface, representation or budget changed. The one failed local
iteration needed a final rfl after list normalization exposed a definitionally
reflexive Option bind; its exact timing was not captured and it is not counted
as a pass. Reviews and limitation are in reviews-parser-dynamic-closure.json
and parser-dynamic-closure-iterations.json.

A fixture-quality review found the prior A. x; negative wrapper could parse
the valid path A.x then fail for a missing declaration name. The wrapper now
uses function bad(A. ) external {}, keeping the exact negative fragment A.
and its polarity. Pinned solc now rejects at the closing parenthesis, directly
isolating the type-name boundary. The previous receipt is preserved and
qualified-path-fixture-isolation.json records the finding. Both separate
read-only reviewers accepted the correction in reviews-path-fixture-isolation.json.
Post-fix solc gate h28-type-b7d600975034.json passes all 29 fixtures in 4.207s,
237,768,704 bytes sampled RSS. Post-fix Lean gate h28-type-4f4be574c7d1.json
passes exact current preflight and all 13,218 positive/23 negative cases with
zero failures in 7.363s, 366,891,008 bytes sampled RSS. Input proof files were
unchanged; these remain external parsing/root-kind controls.

Global function/static-length certification, whole-language identity with
explicit read-only atom dependencies and final full-project gates/reviews/
handoff remain open. The persistent goal stays active.


## Suffix readiness and strong yield-prefix evidence

`Solidity/Frontend/TypeGrammarH28/ParserReady.lean` adds 19 statements.
Function lists need canonical printing that remains valid when later fields'
layout choices follow it. PrefixCertified therefore observes actual successful
yield with arbitrary original unconsumed choices and constructs its own layout,
cost/need, suffix-readiness equation, canonical YieldExact under every future
layout suffix, and frozen token-count fuel bound. Existing Certified and every
producer definition remain unchanged. This stronger target is independently
instantiated for elementary/qualified types, mappings from strict children and
general dynamic-array extension, including every member of the already
inhabited mapping/array control family. It supplies printer suffix stability
explicitly rather than silently assuming a producer-interface fact.

ReadyAt equates actual typeName(residual+cost) parsing with the actual residual
typeSuffix parser. Continuations admit known terminal contexts or an opening
array bracket. The equation preserves both further consumption and errors;
it does not assume suffix success or claim that greedy parsing stops before
an array. Positive need converts the equation into CompleteAt at need+cost.
A universal countercontrol proves that elementary readiness can hold at zero
need while CompleteAt at fuel one is false for every elementary form. The
positive-need guard is therefore substantive. The unconsumed-layout control
shows prefix yield preserving its original remaining choices; it is not an
example of two distinct successful whole-layout witnesses.

Fresh module/audit diagnostics pass. The all-module audit
h28-type-f89239a95b56.json passes with unchanged proof hashes, exit zero, no
guard/OOM, 9.489s wall time and 333,934,592 bytes sampled aggregate RSS. All
291 current statement signatures are source-bound; new sets are seven empty
and twelve propext. Inventory covers thirteen modules; exact signatures and
current fixture provenance/coverage pass. The local failed iteration needed a
final definitional rfl and explicit Tok.punct typing; exact iteration timing
was not captured and no failed recovery axiom is accepted. Both separate
read-only reviewers accepted every new statement and fresh trust evidence
without findings or Lean-server use. reviews-parser-ready.json and
parser-ready-iterations.json preserve their scope and the iteration limitation.

Function parameter/return and attribute layouts, static length atom interfaces,
global prefix certification and final whole-assignment gates remain open.
These proof targets do not replace those obligations or narrow the original
language. The persistent goal remains active.


## Parameter trailers and actual parenthesized lists

`Solidity/Frontend/TypeGrammarH28/ParserParams.lean` adds 39 statements.
ParamCertified is derived from independent strict-child PrefixCertified support;
it preserves every optional data location/name and arbitrary actual token
locations, state choices and EOF. ParamsCertified constructor closure observes
actual original yields, including unconsumed layout choices, and constructs
canonical stable printing and ListReady evidence. ListReady uses a common
maximum parameter fuel and independent separator repetition fuel, bounded by
the real residual tokens. The parameter budget has an explicit extra frame;
this checkpoint does not assume the eventual enclosing function fuel bound.

The actual paramsParen completeness theorem consumes a genuine opening and
closing parenthesis and preserves the entire arbitrary outside suffix.
ListEnd.eof only stops the separator helper; it is never substituted for the
required closing parenthesis. An actual successful first parameter proves the
nonempty branch cannot mistake its first token for ')'. Inhabited controls
cover arbitrarily long lists, every elementary constructor family, all three
data locations or absence, and arbitrary optional names. Negative controls
prove actual missing-close and duplicate-comma refusals. These constructor
lemmas do not replace the original full function-type language.

The first kernel build, h28-type-1b3fabb56178.json, was rejected at trust
acceptance: six statements inherited Quot.sound through a fixed-index recursive
projection. Its source snapshot, log and complete diagnostics remain preserved.
The skeptic also required restoration of the original unconditional inverse
claim after an attempted conditional helper replacement. The repaired generic
structural projection and primitive syntax induction prove the unconditional
param_values_to_syn with no new premise, while retaining the separate helper.
This was a trust/statement repair, not a measured speed optimization. The broad
syntax induction was warned before use; no heartbeat or other proof budget rose.
Failed local iteration timings were not captured and are not passes.

The current serial all-module audit h28-type-6adf100a12d8.json passes in
14.761s with 406,482,944 bytes sampled aggregate RSS, unchanged source hashes,
exit zero and no guard/OOM. All 330 current theorem signatures match source
and observed axiom output; the 39 new sets are fourteen empty and twenty-five
propext. Fresh module/audit MCP diagnostics have no errors, warnings, partial
results or timeouts. Source inventory covers fourteen local modules, and exact
current 29-fixture/13,218-positive/23-negative provenance checks pass. Actual
Lean 4.24.0 and Lake 5.0.0-src+797c613 and the passing KeySort runtime receipt
remain pinned by the earlier runtime gate; no new runtime capability is claimed.
Separate read-only finder/skeptic reviews and the resolved finding are recorded
in reviews-parser-params.json, with no Lean-server use.

Return-list/function attribute layouts, static length atom contracts and closure,
global certification/uniqueness with explicit dependencies, full-project final
gates and whole-assignment acceptance remain open. The persistent goal is active.


## Exact function attribute layouts

`Solidity/Frontend/TypeGrammarH28/ParserFnAttrs.lean` adds 24 statements.
The original successful arrange relation is equivalent to the five exact
empty/visibility/mutability/two-order shapes, for every optional visibility
and mutability and every original order/tokens. No layout profile is filtered.
Raw fnTypeAttrs at constructive fuel three consumes the exact corresponding
real located prefix before a certified continuation or a returns keyword,
preserving the entire suffix, choices and EOF. Equal actual attribute yields
force equal visibility, mutability and order through two independently proved
parses of the same tokens, without assuming attribute or type uniqueness.

Inhabited controls cover all twenty optional-field combinations and the twelve
additional mutability-first layouts, matching all thirty-two fixture layouts.
Universal controls preserve the actual distinction: second visibility stops
without consuming that token, while every mutability pair produces the actual
repeated-attribute error at the second token's start. This does not admit
repeated attributes as whole types. Any original order of length at least three
is refused by the printer. AttrBoundary supplies sufficient contexts; it is not
an asserted necessary boundary or an exclusion from the original language.

The serial all-module audit h28-type-6b447f4a973d.json passes in 9.579s with
326,766,592 bytes sampled aggregate RSS, unchanged source hashes, exit zero
and no guard/OOM. All 354 statement/hash signatures match; the 24 new sets
are twelve empty and twelve propext. Fresh module/audit diagnostics are complete
without warnings/errors/timeouts. Local registration covers fifteen modules;
full inventory, exact signatures and current fixture provenance checks pass.
Both separate read-only reviewers accepted source/trust evidence without
semantic findings or Lean-server use. They corrected an informal count of25
to the actual24 before handoff. reviews-parser-fn-attrs.json and
parser-fn-attrs-iterations.json preserve review scope and iteration limitations.

Actual return-list/enclosing function constructor completeness and fuel,
static length atom contracts/closure, global certification/uniqueness and final
whole-project gates remain open. This checkpoint is not full-assignment
acceptance; the existing persistent goal remains active.


## Actual function constructor and return-list composition

`Solidity/Frontend/TypeGrammarH28/ParserFunctions.lean` adds 32 statements.
The actual returns parser is complete for absent returns or an independently
supported nonempty parameter list. Explicit returns() remains refused; the
real closing parenthesis and exact arbitrary outside suffix are preserved.
Capture runs parameter parsing with empty choices, restores caller choices,
then the actual record calls put the root attribute order before the parameter
and return layouts. fn_body_complete proves that exact producer computation.

ReadyAt for functions preserves the actual residual typeSuffix continuation,
including further array consumption/errors. Its constructive need is
max(parameterBudget+1, returnBudget)+1, with dispatch cost one. Actual token
lengths independently discharge the unchanged sixteen-times frozen fuel bound.
The original function yield converse observes every successful original layout
and unconsumed suffix. prefix_fn then derives canonical stable printing and
readiness from strict ParamsCertified parameter/return children; parent
certification is never a premise. Checked certification and parseType iff
follow. This remains constructor closure, not an unproved claim that every
length atom or type is supported.

Inhabited controls cover arbitrary elementary parameter/return-list lengths,
all optional locations/names/visibility/mutability fields, and arbitrary-depth
nested functions placing the preceding type in both parameter and return
positions. Constructive layout evidence correctly duplicates that child's
choices at the two occurrences; actual checked parses are established at
every depth. General dynamic-array closure around supported functions follows.
A real fuel-two refusal reports the following opening parenthesis position.

The audit h28-type-cc387451857c.json passes in 11.599s, with 354,369,536 bytes
sampled aggregate RSS, unchanged source hashes, exit zero and no guard/OOM.
All 386 statement/hash signatures match; new sets are seven empty and twenty-five
propext. Fresh module/audit diagnostics are complete without warnings/errors.
Inventory covers sixteen modules; source signatures and current exact fixture
provenance pass. Separate read-only finder/skeptic source/trust reviews accept
all 32 statements, with no remaining finding and no Lean-server use.

A broad simplification in a new nested control was interrupted for slow
checking and replaced by explicit Boolean constructor reductions. Full
all-severity diagnostics also caught unused simp arguments and Quot.sound
introduced by broad goal simplification in prefix_fn. Local explicit flattening
and rewriting removed that dependency. All statements/premises remained
unchanged, as the skeptic verified against preserved before-source snapshots.
No proof budget rose. Failed iteration exact timings were not captured; those
requests are not passing evidence. parser-functions-iterations.json and
reviews-parser-functions.json record the repairs and acceptance boundary.

Static length atom contracts/closure, global all-constructor certification and
exactness with explicit atom dependencies, and final whole-project gates remain
open. No whole-compiler correctness or completed assignment is claimed. The
existing persistent goal remains active.


## Static arrays with explicit read-only length atoms

`Solidity/Frontend/TypeGrammarH28/ParserLengths.lean` adds 26 statements.
LengthAtom names independent actual expression parsing before a real closing
bracket, canonical suffix-stable expression yield, a positive constructive
budget bounded by the same frozen token scale, and balanced/nonempty tokens.
It is not assumed for every expression and assumes no resulting type-name
completeness or identity theorem. The atom contract is sufficient dependency
evidence, not a new language exclusion, expression implementation or admission
operation. SOL-QN resolution and SOL-CB constant evaluation remain excluded.

Identifier and every intrinsic NumLit atom independently satisfy that contract
through actual expr parsing at fuel five or greater, preserving arbitrary
locations, choices, following tokens and EOF. Zero-fuel and actual identifier
fuel-four refusals are genuine controls. Static suffix composition consumes
that actual atom and the real closing bracket, then preserves the residual
actual typeSuffix, including further consumption or errors. Base readiness
and atom fuel compose constructively within the unchanged sixteen-times bound;
base and atom reverse layout concatenation matches the producer.

The original array-some yield converse and precedence converse use actual
producer clauses. prefix_array_some derives full static constructor closure
from a strict base certificate and the explicit atom contract. Source parseType
iff follows without evaluation. Arbitrary-depth numeric and identifier static
towers have independently constructed canonical yields, precedence, prefix
certificates and actual checked-parser inhabitants; no global atom assertion
is used in these controls.

The audit h28-type-3509681f8c6e.json passes in 13.662s with 417,234,944 bytes
sampled aggregate RSS, unchanged source hashes, exit zero and no guard/OOM.
All 412 statement/hash signatures match; the 26 new sets are six empty and
twenty propext. Fresh module/audit MCP diagnostics are complete and clean.
Inventory covers seventeen modules; signatures and exact current fixture
provenance pass. Separate read-only finder/skeptic source/trust reviews accept
the checkpoint, with no remaining semantic finding or Lean-server use.

An initial broad root-helper simplification timed out at sixty seconds with
partial diagnostics; that request was stopped and is not passing evidence.
Primitive conjunction extraction proves the unchanged statement. Full
diagnostics also caught unused arithmetic simp arguments and Quot.sound in
atom-instance goal simplification; local explicit flattening/rewriting removed
it. Before-source snapshots and trust-rejected diagnostics are preserved in
parser-lengths-iterations.json and linked evidence. No proof budget rose.
Exact failed-iteration timings were not captured.

The new origin/master publication89373e34cdfd6bb5db7054b1c204d01edffc5fa7 was
fetched in this original owned checkout, with ancestry and all four immutable
frontend inputs verified identical to the assigned base. No merge/rebase,
producer duplication or goal reset occurred. publication-89373e34.json records
that only Layouts and Counterexamples are reported integrated; the remaining
committed work remains lane-owned.

Global all-constructor closure/exactness with explicitly retained atom
dependencies and final whole-project gates remain open. No whole-compiler
correctness or whole-assignment acceptance is claimed. The persistent goal is
active.


## All-constructor finite-dependency exactness

`Solidity/Frontend/TypeGrammarH28/Exactness.lean` adds 32 statements.
Deps is indexed by original intrinsic Syn and includes every elementary,
qualified, mapping, function and array constructor, both array options, and
all parameter/list clauses. Primitive induction constructs actual prefix,
parameter and list certificates; the generic helper's True fallback cannot
be inhabited by Deps at an unrelated category and is never a type-name target.
No operational type admission, producer interface or source syntax changed.

finite_atom_dependencies is universal over original Syn. Its construction
collects only actual static array payloads from type/parameter/list structure,
leaving expression internals opaque. The finite completeness, source iff and
exactness theorems require only that finite list's LengthAtom facts. They do
not use all_constructor_coverage's stronger hypothetical global atom premise,
and do not assume resulting type identity or completeness. Arbitrary expression
atom support remains an explicit external dependency. Identifier/numeric
instances and the all-constructor mixed control discharge their own atom facts.

Actual raw typeName completeness uses exactly 16 * (locatedTokenCount+1), with
arbitrary locations and EOF, followed by checked/source corollaries. Source
soundness requires no atom/completeness premise. Identity compares arbitrary
original successful layout witnesses, derives AST equality and successful
LayoutEquivalent, and never equates those witnesses. The same local atom facts
plus actual frozen precedence discharge every earlier delimiter-balance
obligation. Boundary exactness therefore combines arbitrary-depth token-prefix
and remainder uniqueness with AST/layout exactness, without a new expression
balance or identity assumption. The original false unrestricted raw-yield
identity claim remains preserved by its actual counterexample and precedence
control; no whole-expression or whole-unit uniqueness is claimed.

MixedFields leaves every original field family arbitrary. Its genuine mixed
control contains a dynamic elementary array parameter, a qualified return,
a function inside a mapping and an outer numeric static array, plus arbitrary
additional parameter/return lists. mixed_deps, mixed_prec, mixed_exact and
mixed_checked construct real support, canonical yields and checked parses for
every such field assignment. No mock parser or success premise supplies its
inhabitance. Source iff remains tied to real lexed pieces.

The serial audit h28-type-9f3538c8bd3b.json passes in 14.812s with 370,565,120
bytes sampled aggregate RSS, unchanged source hashes, exit zero and no
guard/OOM. All 444 statement/hash signatures match; the 32 new sets are two
empty and thirty propext. Fresh module/audit MCP diagnostics are complete and
clean. Inventory covers eighteen modules; exact signatures and current fixture
provenance pass. Current light source checks record wall/user/system timings
and per-command maximum RSS. Earlier light-check timings were not captured;
legacy handoff summary zero durations mean unknown, never measured zero.

Both separate read-only finder/skeptic reviews accept all 32 conditional source
results and fresh trust evidence, with no remaining confirmed finding or Lean
server use. A rejected mutual structural recursion was repaired, after warning,
by one category-indexed proof predicate and primitive induction. No statement,
premise, producer contract or proof budget was weakened. The failed iteration's
exact timing was not captured and its recovery axioms are not passing evidence.
exactness-iterations.json preserves that boundary.

acceptance-all-constructors.json enumerates every assigned constructor/clause,
all eighteen proof files and 444 theorem names, all eight immutable inputs,
and all 29 grammar fixtures with hashes, polarities, clauses and position
counts. It records kernel versus external-test boundaries, substantive atom
premises, preserved false claims and exclusions. It is proof-scope acceptance,
not final whole-assignment acceptance. Final repository policy gates, combined
scope-complete reviews and final handoff remain outstanding. The persistent
goal stays active until those obligations are resolved.


## Final validation and reserved central-registration blocker

The owned implementation/proof/control/fixture scope is complete under the
explicit local read-only atom contracts. Separate combined finder/skeptic
reviews verify all eighteen proof files, 444 exact statement/hash signatures,
eight immutable input pins and twenty-nine fixtures. The earlier top-level
queue/status text was corrected to distinguish this completed conditional
scope from external arbitrary-expression support and remaining project gates.
No whole-compiler or unconditional expression result is claimed.

| Actual command | Outcome | Wall seconds / sampled aggregate RSS | Decisive evidence |
| --- | --- | --- | --- |
| bounded runtime: Lean/Lake versions and KeySort | PASS | 2.649 / 245,805,056 bytes | h28-type-8f49088474e6: Lean 4.24.0, Lake 5.0.0-src+797c613; KeySort exits 0 before RUNTIME_GATE_PASS |
| run_bounded.py axioms | PASS | 11.080 / 313,335,808 bytes | h28-type-1a6754c4e28f: all 444statements, only empty/propext signatures |
| run_bounded.py solc | PASS | 5.985 / 248,983,552 bytes | h28-type-48a2047a852e: all 29fixtures, zero failures |
| run_bounded.py lean-fixtures | PASS | 8.421 / 367,009,792 bytes | h28-type-a376784ef40e: 13218 positive / 23 negative, zero failures |
| final_policy.py full: unmodified gate.sh full | FAIL | 69.831 / 830,590,976 bytes | h28-policy-86f0261915d5: run-lean/roots/orphans report 18 missing central imports |
| final_policy.py build: original defaults plus SolkeyTestSuite | PASS | 5.017 / 104,292,352 bytes | h28-build-7c7dd54fc29d: 3,672 jobs completed successfully |
| final_policy.py solkey: actual check-solkey.sh | PASS | 2.792 / 2,224,128 bytes sampled | h28-solkey-4ba077b03f26: 377 taclets / 131 read-bearing annotations match; cgroup peak 555,651,072 bytes |

The full policy's touched builds, trust, layers, doc paths, axiom pins,
TestSuite, corpus and strict automation pass. TestSuite reports 552 derived,
11 refuted, zero pending/divergent and one pre-existing exclusion; the corpus
check matches its original pins. These are repository-wide baseline checks,
not new whole-compiler proofs. run-lean exits at its root check before its
build/sort stages; the separately executed commands above are recorded exactly
as independent validation, never as a passing run-lean gate. The ordinary
full gate remains failed. Integer stage timings in the official gates.tsv
have second resolution; sampled RSS can miss short-lived subprocess peaks.

The first version preflight and copied-snapshot pin failures are preserved,
with their exact recoveries. The snapshot and repository pin have identical
473da8944ca7329e6b76819863591407db26e7ec provenance and manifest bytes; mounting
the existing pin read-only fixed TestSuite/corpus setup without source changes.
Two default-build attempts hit the unchanged headroom guard. One printed build
success/exit 0 but remains failed because its guard fired. Removing 49 stopped
owned containers named in saved receipts freed about 9.36 GB of headroom; bind
mounts, images and all saved artifacts remained intact. Read-only clean-page
advice then recovered additional headroom. Retried build/sort checks pass with
12 GiB/no swap, one CPU/-j1, unchanged 4 GiB reserve/600s guard and unchanged proof
budgets. No system cache-drop, swap change, new VM or cache transport occurred.

Final guard controls confirm enclosing-cgroup headroom and lifetime-lock
refusal; five forged/missing/duplicate/polarity/provenance fixture receipts are
refused. Current inventory/signature/fixture checks pass with measured command
timings and maximum RSS. All eight source pins also match the new published
89373e34cdfd6bb5db7054b1c204d01edffc5fa7 commit. final-validation-summary.json,
final-guard-controls.json and the raw per-run receipts preserve commands,
exits, source identities and decisive outputs, including failed attempts.

The assignment expressly reserves generated roots to central integration:
"New modules have a local registration manifest for central integration; no
generated root changes." Consequently the worker leaves Solidity.lean and
shared registries untouched. central-registration-blocker.json enumerates the
actual eighteen missing imports, ownership and required unchanged gates.
Origin/master already reports Layouts and Counterexamples integrated; the
assigned pinned-base branch still lacks all eighteen root imports. The owner
can deduplicate the two published modules using the provided manifest/patch.
No new exclusion or premise approval is requested; the remaining action is
already assigned to the central integration owner. questions=[] is intentional.

Full-assignment acceptance is blocked until reserved integration and the
corresponding full policy gates pass. The final sealed handoff includes the
complete committed patch/bundle, exact base/head/branch, all evidence and
checksum manifest. Any exact-head follow-up receipts created after the final
metadata commit are included in that archive and do not change proof sources.
The existing goal is not marked complete with these failures outstanding.


Both final reviewers confirm no remaining source, tooling, provenance or current
queue-accounting finding. The measured final_policy.py bytes match the passing
build/sort/axiom/solc/Lean-fixture receipt hashes exactly. Its earlier measured
full-policy version and full mode-extension diff are retained with matching
hashes in final-policy-wrapper-source-bindings.json. The preserved full raw-output
whitespace check fails; the passing source-only check excludes only the actual
immutable raw-output files listed in its receipt, without rewriting any output.
reviews-final-combined.json records conditional-scope acceptance and keeps
whole-assignment acceptance blocked. Exclusive-write scope checks confirm all
tracked/untracked work stays in the three authorized prefixes; no generated
root, producer, shared module map or trust inventory changed.

## H35 VM validation and cache transport (2026-11-04)

Fresh VM checks at d6caec1328573a9cee51ac9d889adb470da3bdfc:
`python3 -B tests/h28-sol/type-grammar/run_bounded.py axioms` passed
(exit 0, 10.519 s, sampled RSS 313118720 bytes): all 18 owned modules built
serially with Lean -j1, all 444 axiom inventories emitted, only []/[propext].
`python3 -B tests/h28-sol/type-grammar/run_bounded.py lean-fixtures` passed
(exit 0, 7.346 s): 13218 positive and 23 negative controls, zero failures.
Both guards passed, sources unchanged, 12 GiB memory/no swap and 4 GiB headroom.
Detailed commands, logs and resource evidence: `tests/h28-sol/type-grammar/evidence/h35/`.
This supplement changes no Lean source, theorem, fixture or premise.

H35 cache payload: `/workspace/scratch/h28-type-grammar/h35-cache`,
18 owned-module input mappings, 54 artifacts, 12779136 bytes.
The actual `bash scripts/coord-tools/ship-cache.sh /workspace/solidity-lean`
attempt used documented `SHIP_ALLOW_HEAD=1`, this owned cache, and an explicit
single assigned lane. It packed the payload, then exited 1: the coordinator
catalog `/home/agent/.local/share/cloudvm/batches/solidity-h28-sol-20261104/catalog.json`
is absent. No transfer succeeded; cache-receipts.tsv records FAILED.
The script is a coordinator-to-lane relay and also requires coordinator vmexec
configuration, which is absent here. The prepared pack is available for the
coordinator to retrieve; it is not a successful shipment receipt.

H35 acceptance remains blocked by cache transport setup and the previously
recorded generated-root integration failures. No shared roots were changed.
The immutable prior final package remains
`/workspace/scratch/h28-type-grammar/checkpoint-d6caec132857-final`.

Separate read-only finder and skeptic accepted this H35 supplement with no
confirmed finding, without Lean server use. Their evidence is `evidence/h35/reviews.json`.

## Published-master adoption, 2026-11-05

Adopted exact published master `8495f1deb0a95dd6b9301822d8649ab76b217681`
by merge `020d1a8f5cb0344f24331695f3eb583d7755a530`, whose first parent is
owned H35 head `b00b91a9de659091f64c0bc4e1809b252365d1d7`. Both published
master and original pinned base are verified ancestors. All 489 tracked owned
files and four frozen producer inputs are byte-identical before/after adoption;
full identities are in `evidence/adopted8495/adoption.json`.
The published packet does not integrate the remaining type-grammar modules.
The local registration manifest still lists all 18; the shared root imports
Layouts and Counterexamples only, leaving exactly 16 missing imports.

All following actual VM gates ran at the merged head, serially, Lean -j1,
12 GiB/no swap with 4 GiB minimum VM/host headroom. Gate commands, source hashes,
exits, elapsed time, RSS and raw log paths are in `evidence/adopted8495/`.

| Command | Outcome | Decisive evidence |
| --- | --- | --- |
| `python3 -B tests/h28-sol/type-grammar/run_bounded.py axioms` | PASS, 11.663s | 18 owned builds; 444 inventories, only []/[propext] |
| `python3 -B tests/h28-sol/type-grammar/run_bounded.py lean-fixtures` | PASS, 8.489s | 13218 positive/23 negative; zero failures |
| `python3 -B tests/h28-sol/type-grammar/final_policy.py full` (first attempt) | FAIL, exit137, 85.457s | headroom guard interrupted touched build; no policy verdict |
| same full command (retry) | FAIL, exit1, 337.278s, guard null | touched build1675 jobs PASS; run-lean/roots/orphans FAIL16missing imports; every other stage PASS |
| `python3 -B tests/h28-sol/type-grammar/final_policy.py build` | PASS, 12.977s | all default targets and SolkeyTestSuite |
| `python3 -B tests/h28-sol/type-grammar/final_policy.py solkey` | PASS, 1.768s | actual SolKey check |
| `python3 -B tests/h28-sol/type-grammar/run_bounded.py runtime` | PASS, 2.119s | actual KeySort before RUNTIME_GATE_PASS |

Actual Lean 4.24.0 (797c613eb9b6d4ec95db23e3e00af9ac6657f24b),
Lake 5.0.0-src+797c613. Full retry minimum headroom10103820288 bytes,
sampled RSS4571099136 bytes; no source changed during any gate.
Initial failure and recovery are retained: only 15 stopped containers identified
by owned receipts were removed, safe metadata saved, and clean file pages advised
read-only with POSIX_FADV_DONTNEED. No source/cache files deleted or limits relaxed.

Fresh H35 cache export reselected current 18 input mappings and54 artifacts,
12779136 bytes. The actual ship-cache.sh invocation uses documented non-master
override and an explicit assigned-lane file; all overrides are recorded. It
packed and verified54/54 artifact hashes, then exited1 because the coordinator
catalog is absent. vmexec configuration is also absent. No transfer succeeded.
Prepared pack SHA256: `5e4dfe19e7ad8f39789827c39aba454cbc08690917dbad3173567ee9bdb460ac`.
The coordinator's cache-delta notice establishes no local cache freshness.

Original proof/external-test boundaries and all LengthAtom dependencies remain
unchanged. No whole-lane acceptance: reserved central-root integration and
successful cache transport are still outstanding; no question or waiver is requested.

Separate read-only finder/skeptic accepted adoption and the complete supplement
with no findings, without Lean server use; `evidence/adopted8495/reviews.json`.
Default build checked3923 jobs; SolKey checked377 taclets/131 annotations.

## Follow-on published-master adoption, 2026-11-05

Adopted exact `f77cf60d3cea8f7f1db8db29cc027532b0cd3fce` by merge
`60eac8cef2155ba5ebb446ae41fa19a947b76def`, first parent
`6b2188f9c3d1010d7cf0ae9de5fcd5b95fc77d3f`. Original base and both
published masters are verified ancestors. All534 tracked owned files and four
frozen producer inputs were byte-identical across adoption; full enumeration
and hashes are in `evidence/adoptedf77/adoption.json`. ParserBasics/ParserChecks
are the same owned bytes now integrated centrally. With Layouts/Counterexamples,
the root registers4 of18 modules; exactly14 remain missing. Local manifest still
enumerates all18. No producer, premise, exclusion, theorem or budget changed.

Fresh actual VM receipts, full commands, exits, source hashes, elapsed times,
RSS and raw log paths are in `tests/h28-sol/type-grammar/evidence/adoptedf77/`.
Every heavy check was serial, Lean -j1,12GiB/no swap,4GiB headroom guard.
Resource preflight removed only5 stopped containers identified by prior owned
receipts and advised clean file pages read-only; no source/cache data deleted.

| Command | Actual outcome | Decisive output |
| --- | --- | --- |
| `python3 -B tests/h28-sol/type-grammar/run_bounded.py axioms` | PASS9.927s | 18 builds;444 inventories only []/[propext] |
| `python3 -B tests/h28-sol/type-grammar/run_bounded.py lean-fixtures` | PASS8.394s | 13218positive/23negative;zero failures |
| `python3 -B tests/h28-sol/type-grammar/final_policy.py full` first attempt | FAIL605.369s,exit137 | existing600s guard interrupted upstream rebuilding; no policy verdict |
| `python3 -B tests/h28-sol/type-grammar/final_policy.py build` first attempt | FAIL605.686s,exit137 | same guard during upstream rebuilding; retained completed cache outputs |
| full retry, identical command/limits | FAIL341.085s,exit1,guard null | build2015jobs PASS;only run-lean/roots/orphans FAIL14imports;every other stage PASS |
| default build retry, identical command/limits | PASS3.316s | all3938jobs/default targets+SolkeyTestSuite |
| `python3 -B tests/h28-sol/type-grammar/run_bounded.py runtime` | PASS2.107s | actual KeySort precedes RUNTIME_GATE_PASS |
| `python3 -B tests/h28-sol/type-grammar/final_policy.py solkey` | PASS1.236s | 377taclets/131annotations |

Actual Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b,
Lake5.0.0-src+797c613. Full retry minimum headroom8916578304 bytes,
sampled RSS2709303296 bytes. Every receipt records source_unchanged=true. Initial
interruptions remain explicit failures, not silently replaced by later receipts.

Fresh H35 shipment attempt reselected18 mappings/54artifacts,12779136bytes.
Actual ship-cache.sh command and all documented environment overrides are in
cache-attempt.json. It packed and verified54/54 hashes, then exited1 because
`/home/agent/.local/share/cloudvm/batches/solidity-h28-sol-20261104/catalog.json`
is absent. Coordinator vmexec is also absent. No transfer succeeded and no cache
freshness follows from the upstream notice. Prepared pack SHA256 remains
`5e4dfe19e7ad8f39789827c39aba454cbc08690917dbad3173567ee9bdb460ac`.

Original proof versus external-test boundaries, local finite LengthAtom contracts,
29solc fixture source identities and13241parser cases are unchanged. Whole-lane
acceptance remains blocked on central registration14imports and successful cache
transport; no waiver or premise approval is requested.

Separate read-only finder and skeptic accepted the complete follow-on supplement
with no findings, without Lean server use; `evidence/adoptedf77/reviews.json`.

## Published 9584f9e7 adoption and H41 cache handoff, 2026-11-05

Exact published master `9584f9e7df09f638d9e0cb8930501d1660aa4b2f` was
merged as `ce5c40983cc0dd1091e02b3f087a0064ac923da2`, first parent
`4972b8fc3f301c3d95349b57206f8316be0d1426`. Base and prior published
masters are verified ancestors. All582 tracked owned files and four frozen
producer inputs were byte-identical across adoption; complete enumeration and
hashes are in `evidence/adopted9584/adoption.json`. Composition is now integrated
using the exact owned bytes. Root imports5 of18 owned modules, leaving13
missing imports; the local manifest still enumerates all18. No theorem, premise,
exclusion, proof budget, producer interface or lane-authored root changed.

Fresh actual VM commands and full receipts are in `evidence/adopted9584/`,
including source identities, exits, timing, RSS and raw log paths. Lean checks
were serial -j1,12GiB/no swap,4GiB headroom guard. Resource preflight removed
only7 stopped containers identified by owned receipts, preserving metadata,
and advised clean file pages read-only; no source/cache data was deleted.

| Command | Actual outcome | Decisive output |
| --- | --- | --- |
| `python3 -B tests/h28-sol/type-grammar/run_bounded.py axioms` | PASS14.045s | 18 builds;444 inventories only []/[propext] |
| `python3 -B tests/h28-sol/type-grammar/run_bounded.py lean-fixtures` | PASS10.115s | 13218positive/23negative;zero failures |
| `python3 -B tests/h28-sol/type-grammar/final_policy.py full` | FAIL429.941s,exit1,guard null | touchedbuild2122jobs PASS;only run-lean/roots/orphans FAIL13imports;all other stages PASS |
| `python3 -B tests/h28-sol/type-grammar/final_policy.py build` | PASS12.011s | all4010jobs/default targets+SolkeyTestSuite |
| `python3 -B tests/h28-sol/type-grammar/run_bounded.py runtime` | PASS2.688s | actual KeySort precedes RUNTIME_GATE_PASS |
| `python3 -B tests/h28-sol/type-grammar/final_policy.py solkey` | PASS2.323s | 377taclets/131annotations |

Actual Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b,
Lake5.0.0-src+797c613. Full gate minimum headroom8243781632 bytes,
sampled RSS5253427200 bytes. Every receipt records source_unchanged=true.
All guards passed this adoption. Historical failures remain preserved separately.

H41 supersedes the prior VM shipping workflow. **No ship-cache.sh invocation
was made for this adoption.** The VM responsibility is a verified pack for
coordinator pull; delivery/freshness is not claimed. Current18 input mappings
and54 artifacts (12779136bytes) were selected from actual owned traces. Pack
creation used tar and zstd -T1,one CPU,12GiB address-space bound,no host swap,
4GiB headroom precheck. All54 compressed archive members were independently
streamed and checked against current cache sizes/SHA256 values.

Pack: `/workspace/scratch/h28-type-grammar/master9584-cache-h41/owned-artifacts.tar.zst`
SHA256: `da52ab498a74f0760aaa71ab9e8b8eb4386e95776383c1f8c518756f38946981`
Input mappings: `/workspace/scratch/h28-type-grammar/master9584-cache-h41/inputs/solidity-lean.jsonl`
Artifact manifest: `/workspace/scratch/h28-type-grammar/master9584-cache-h41/artifacts.json`
Receipt: `evidence/adopted9584/cache-receipt.json`; trace identities and mappings
are retained beside it. Pack preparation passes; actual coordinator pull/import
is pending, without an unsupported transport receipt. Historical VM shipping
failures are immutable evidence of earlier instructions, not a current VM action.

Original proof/external-test boundaries and finite local LengthAtom contracts
remain unchanged; arbitrary expression support is externally unproved and no
whole-compiler correctness is claimed. Whole-assignment acceptance remains
blocked by reserved central-root integration13imports and its required full
gates. Coordinator cache pull is pending under H41; no scope waiver is requested.

Separate read-only finder and skeptic accepted adoption, complete VM evidence
and H41 cache handoff with no findings, without Lean server use;
`evidence/adopted9584/reviews.json`.

## Published b86ae456 adoption and H41 handoff, 2026-11-05

Exact published master `b86ae4568cef6d6226f4d170360bbb089debe3fb` was
merged as `b878976915e3b212e1700ac736607f1806b784d2`, first parent
`6fece6f72fd48b1cfa55e5472fdeacfe97c4e0e9`. Original base and prior
published masters are verified ancestors. All621 tracked owned files and four
frozen producer inputs were byte-identical across adoption; complete enumeration
and hashes are in `evidence/adoptedb86/adoption.json`. ParserArrays/ParserPaths
are newly integrated using the same owned bytes. Root imports7 of18 owned
modules, leaving11 missing; the local manifest enumerates all18. No theorem,
premise, exclusion, proof budget, producer interface or lane-authored root changed.

Fresh actual VM receipts, exact commands, source hashes, exits, elapsed times,
RSS and raw log paths are in `evidence/adoptedb86/`. All heavy checks were
serial, Lean -j1,12GiB/no swap,4GiB headroom guard. Resource preflight removed
only6 stopped containers identified by owned receipts, preserving metadata,
and advised clean file pages read-only; no source/cache data was deleted.

| Command | Actual outcome | Decisive output |
| --- | --- | --- |
| `python3 -B tests/h28-sol/type-grammar/run_bounded.py axioms` | PASS12.791s | 18 builds;444 inventories only []/[propext] |
| `python3 -B tests/h28-sol/type-grammar/run_bounded.py lean-fixtures` | PASS7.895s | 13218positive/23negative;zero failures |
| `python3 -B tests/h28-sol/type-grammar/final_policy.py full` | FAIL174.931s,exit1,guard null | touched2191jobs PASS;only run-lean/roots/orphans FAIL11imports;every other stage PASS |
| `python3 -B tests/h28-sol/type-grammar/final_policy.py build` | PASS5.473s | all4061jobs/default targets+SolkeyTestSuite |
| `python3 -B tests/h28-sol/type-grammar/run_bounded.py runtime` | PASS2.213s | actual KeySort precedes RUNTIME_GATE_PASS |
| `python3 -B tests/h28-sol/type-grammar/final_policy.py solkey` | PASS4.004s | 377taclets/131annotations |

Actual Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b,
Lake5.0.0-src+797c613. Full gate minimum headroom12591157248 bytes,
sampled RSS988774400 bytes. Every receipt records source_unchanged=true.
All guards passed this adoption; historical failures remain preserved separately.

H41: no ship-cache.sh invocation was made on the VM for this adoption.
A fresh verified owned pack is ready for coordinator pull; delivery/import and
cache freshness are not claimed. All18 mappings exactly match current trace
outputs;54 artifact files and54 unique compressed members match sizes/SHA256.
Tar/zstd commands and resource limits are recorded in cache-receipt.json.

Pack: `/workspace/scratch/h28-type-grammar/masterb86-cache-h41/owned-artifacts.tar.zst`
SHA256: `da52ab498a74f0760aaa71ab9e8b8eb4386e95776383c1f8c518756f38946981`
Input mappings: `/workspace/scratch/h28-type-grammar/masterb86-cache-h41/inputs/solidity-lean.jsonl`
Artifact manifest: `/workspace/scratch/h28-type-grammar/masterb86-cache-h41/artifacts.json`
Pull/import remains coordinator-owned under H41; VM pack preparation passes.

Original proof/external-test boundaries, finite local LengthAtom contracts,
29solc fixture identities and13241parser cases remain unchanged. Arbitrary
expression support is externally unproved; no whole-compiler correctness claim.
Whole-assignment acceptance remains blocked by reserved central-root integration
11imports and its required full gates; no scope waiver is requested.

Separate read-only finder and skeptic accepted adoption, complete VM evidence
and H41 handoff with no findings, without Lean server use;
`evidence/adoptedb86/reviews.json`.

## Published 8bf83218 adoption and H41 handoff, 2026-11-05

Exact published master `8bf8321873befa3f35ca31e97e5339a1baee93e6` was
merged as `467c5061bc484dd5f6f563ec7435c85f889532e3`, first parent
`9b0d7813e4ae5eda9bb2a983d42882ed4ffa27aa`. Base and prior published
masters are verified ancestors. All660 tracked owned files and four frozen
producer inputs were byte-identical across adoption; full enumeration/hashes
are in `evidence/adopted8bf/adoption.json`. This publication adds no type-grammar
fragments: root still imports7 of18 modules, leaving11 missing. Local manifest
still enumerates all18. Owned statements,premises,exclusions and budgets remain.

Fresh actual VM receipts, exact commands, source hashes, exits, timings, RSS
and raw log paths are in `evidence/adopted8bf/`. All heavy checks were serial,
Lean -j1,12GiB/no swap,4GiB headroom guard. Resource preflight removed only6
stopped containers identified by owned receipts, preserving metadata, and advised
clean file pages read-only; no source/cache data was deleted.

| Command | Actual outcome | Decisive output |
| --- | --- | --- |
| `python3 -B tests/h28-sol/type-grammar/run_bounded.py axioms` | PASS11.700s | 18 builds;444 inventories only []/[propext] |
| `python3 -B tests/h28-sol/type-grammar/run_bounded.py lean-fixtures` | PASS7.914s | 13218positive/23negative;zero failures |
| `python3 -B tests/h28-sol/type-grammar/final_policy.py full` | FAIL162.615s,exit1,guard null | touched2244jobs PASS;only run-lean/roots/orphans FAIL11imports;every other stage PASS |
| `python3 -B tests/h28-sol/type-grammar/final_policy.py build` | PASS11.388s | all4106jobs/default targets+SolkeyTestSuite |
| `python3 -B tests/h28-sol/type-grammar/run_bounded.py runtime` | PASS3.153s | actual KeySort precedes RUNTIME_GATE_PASS |
| `python3 -B tests/h28-sol/type-grammar/final_policy.py solkey` | PASS4.475s | 377taclets/131annotations |

Actual Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b,
Lake5.0.0-src+797c613. Full gate minimum headroom11072409600 bytes,
sampled RSS2698354688 bytes. Every receipt records source_unchanged=true;
all guards passed this adoption. Historical failures remain preserved separately.

H41: no VM ship-cache.sh invocation this adoption. A fresh verified pack is ready
for coordinator pull; delivery/import/freshness is not claimed. All18 mappings
exactly match current trace outputs, and54 artifact files and54 unique compressed
archive members match sizes/SHA256. Exact tar/zstd commands and limits are in
cache-receipt.json. Artifact content and pack hash remain unchanged.

Pack: `/workspace/scratch/h28-type-grammar/master8bf-cache-h41/owned-artifacts.tar.zst`
SHA256: `da52ab498a74f0760aaa71ab9e8b8eb4386e95776383c1f8c518756f38946981`
Input mappings: `/workspace/scratch/h28-type-grammar/master8bf-cache-h41/inputs/solidity-lean.jsonl`
Artifact manifest: `/workspace/scratch/h28-type-grammar/master8bf-cache-h41/artifacts.json`
Coordinator pull/import remains pending; VM preparation passes.

Original proof/external-test boundaries, finite local LengthAtom contracts,
29solc fixture identities and13241parser cases remain unchanged. Arbitrary
expression support is externally unproved; no whole-compiler correctness claim.
Whole-assignment acceptance remains blocked by reserved central-root integration
11imports and its required full gates; no scope waiver is requested.

Separate read-only finder and skeptic accepted adoption, complete VM evidence
and H41 handoff with no findings, without Lean server use;
`evidence/adopted8bf/reviews.json`.

## Required rebase onto e6849d3b, 2026-11-05

Rebased the existing assigned branch onto `e6849d3bdf516099d20c33d3581d523449764018`
before making this handoff commit. All18 proof modules, four frozen producer inputs
and non-pruned owned helpers/docs were already byte-identical upstream. Empty
replay avoided duplicating integrated fragments or republishing pruned evidence.
The29historical commits remain under `refs/codex-backups/type-grammar/pre-e6849d3b`
and `/workspace/scratch/h28-type-grammar/rebase-e6849d3b/pre-rebase.bundle`.
All509preserved files hash-match the pre-rebase work;485upstream-pruned runtime
assets were restored only locally and Git-ignored. This includes every original
fixture and generated case: nothing was dropped from grammar/control coverage.
The fresh solc receipt is intentionally updated; no proof/fixture source changed.

The thin committed ledger is `tests/h28-sol/type-grammar/evidence/rebase-e6849d3b-summary.json`.
It enumerates all18 module hashes/counts, all constructor/field/layout clauses,
all29fixture identities and exact commands/exits/timing/RSS. Complete raw receipts
and logs remain outside Git in `/workspace/scratch/h28-type-grammar/rebase-e6849d3b/raw-gates/`,
respecting upstream pruning. Fresh actual VM gates at e6849d3b:

| Gate | Result | Decisive output |
| --- | --- | --- |
| runtime | PASS3.358s | Lean4.24.0/Lake5.0.0-src+797c613;actual KeySort before RUNTIME_GATE_PASS |
| solc | PASS4.260s | all29positive/negative grammar fixtures |
| owned build+axioms | PASS11.663s | 18modules,444inventories:177empty,267propext |
| parser controls | PASS8.505s | 13218positive/23negative,zero failures |
| full policy | FAIL232.359s,exit1,guard null | touched2346jobs;all stages PASS exceptaxiom-pins |
| default build | PASS2.849s | 4178jobs,defaulttargets+TestSuite |
| SolKey | PASS1.277s | 377taclets/131annotations |

All checks were serial Lean -j1,12GiB/no swap,4GiB headroom guard.
Full minimum headroom7866126336bytes,sampled RSS2547249152bytes.
All source-unchanged guards pass; no proof budget or gate was weakened.

**Current blocker:** `node scripts/check-axiom-pins.mjs` reports0errors and
479unrecorded changes, with0TypeGrammarH28 notes. All are outside this lane.
Exact output is `/workspace/scratch/h28-type-grammar/rebase-e6849d3b/unrecorded-pins.txt`;
classification is `pin-blocker.json` beside it. Shared pin inventory remains untouched.
Passing a required full rerun after central reconciliation is still outstanding.
Historical ledgers saying root-registration blocked remain historical; this
section and the fresh ledger explicitly supersede that blocker.

Read-only original-queue finder/skeptic found no unfinished owned proof/fixture
obligation within the permitted local LengthAtom boundary. Arbitrary-expression
LengthAtom support remains external, source completeness remains conditional on
those explicit facts, and the false raw-yield claim retains its counterexample.
Fixture evidence is grammar acceptance/root-kind agreement, not AST/compiler
equivalence. No whole-expression/compiler correctness or whole-goal completion.

H41: no VM ship-cache invocation. Verified18mappings/54artifact members ready
for coordinator pull at `/workspace/scratch/h28-type-grammar/rebase-e6849d3b/cache-h41/owned-artifacts.tar.zst`,
SHA256 `da52ab498a74f0760aaa71ab9e8b8eb4386e95776383c1f8c518756f38946981`.
Mappings/manifest/traces/receipt are beside it. Pull/import pending;no delivery
or freshness claim. No scope waiver or shared-inventory edit is requested.

Separate read-only finder/skeptic accepted rebase fidelity, original-queue
accounting, complete fresh VM evidence and this thin handoff with no findings,
without Lean server use. Their verdicts are in the committed summary.

## Final human-authorized stop-and-handoff, 2026-11-06

H82 permits statement-preserving edits across files. The current patch adds3554
missing records to `scripts/g07-axiom-pins.json`, preserving all8154old records
and all6492tracked Lean source hashes/checker bytes. No theorem, definition,
interface, actual axiom set, proof budget, exclusion or trust policy changed.
Independent read-only finder/skeptic accepted the additive diff with no findings.
Checker regressions and static inventory pass:11708pins,0errors,0notes.
Fresh runtime/solc/ownedaxiom/parser controls passed. Human retirement canceled
the active full gate,exit137;no passing full acceptance or later default/SolKey
result is claimed. This supersedes old shared-pin-blocker counts without
rewriting their historical evidence.

Mandatory original scope is committed in `tests/h28-sol/type-grammar/handoff/`.
`OPEN-QUEUE-AND-WAITS.json` enumerates open validation/backfill boundaries. Bulk
raw evidence remains `/workspace/scratch/h28-type-grammar/h82-additive-pins/`;
final authenticated patch/bundles/manifests identify all exact paths and hashes.
No H71 push authorization text was available,so no push. Successor is responsible
for integrating the final head. No ownership takeover precedes final stopped/head
acknowledgment. No Claude-owned source edit or message;no new proof implementation.

PAUSED was explicitly requested;the exposed goal tool cannot express it. No
complete/blocked substitution was attempted. Coordinator must apply PAUSED;the
worker stops after this handoff with no automatic implementation continuation.

## H67 re-cut requested by coordinator, 2026-11-06

The held candidate `bcbac2605b359b501e21e33d004e9f5df5d1f014` and observed
merge head `dce2d51265abc160827f56517a7d7341025624ad` are preserved under
`refs/codex-backups/type-grammar/pre-h67-recut` and the external pre-cut bundle.
The replacement is cut directly on `20e492ee99a3fa8679aa526de0b6e731d85e4134`.
It retains docs/handoff only and omits every G07 inventory/fragment delta, plus
the nonessential solc timing-only receipt delta. No Lean source or statement,
definition,actual axiom set,budget,checker or trust policy changed.

H67 assigns G07 reconciliation to the separate one-off job. Historical H82
metadata and test results above remain historical evidence only;they do not
validate this replacement head. No new Lean/full gate was run. Original prompt,
work/backfill queue,scope and stopped-state handoff remain committed. The worker
remains retired;this correction is not automatic implementation continuation.
