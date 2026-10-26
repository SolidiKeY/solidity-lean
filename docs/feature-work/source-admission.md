# Source admission milestone

Integration status (2026-10-26): included in the shared checkout. Current
combined validation is tracked in [integration.md](integration.md).
Worker handoff statuses and isolated validation results below are historical;
they neither report the current combined checks nor establish full source support.

Modern `scripts/solc-ast.mjs` output records the exact supported compiler file,
version and SHA-256; source SHA-256; accepted pragma tokens; AST analysis stage;
and explicit pipeline, EVM target, optimizer and output settings. Both pinned
0.8.34 and 0.8.38 compilers are supported. Unknown modes/settings, mismatched
pragma records and incomplete modern headers fail. `--via-ir` selects source-order
operand scheduling automatically; modern imports refuse a manual `evalOrder`
override. Requested ABI-v1 under via-IR records effective ABI-v2. Legacy-v1
decoding remains an explicit implementation diagnostic.

Historical four-field fixtures remain compatible and report
`admissionChecked = false`; regenerate them with `--legacy-fixture` only when
preserving that boundary. Modern fixtures report source features and structured
diagnostics separately from their existing elaboration status.
Modern representation-limit failures are implementation gaps; historical
fixtures keep their pinned legacy statuses. The compiler
record is `N.report.provenance`. This is provenance of external solc analysis,
not authentication of handwritten JSON, bytecode validation, or a theorem of
compiler/lowering equivalence.

`Frontend/SolcJson/Admission.lean` scans known nodes, semantic type metadata,
call options, arguments, selected modifiers, execution dependencies and lexical
specifications. Declaration references follow headers by compiler identity;
mutable initializers and base-constructor arguments execute only for deployment.
Metadata-only selectors do not pull unrelated function bodies into admission.
Possible self-calls include cast/aliased receivers. Payment dispatch requiring
inherited receive, fallback or receive modifiers is refused until that dispatch
is implemented. General function-value dispatch remains an implementation gap. Resolved scalar
operator aliases use the declaration-aware validator and typed call lowering
described in [the numeric milestone](numeric-operators.md); missing, malformed
or nominally mismatched annotations are refused. Scope decisions never depend on inventory status.
Stored external-function `.address`/`.selector` observations retain explicit ABI-kind
casts through lowering. Stable pure places are supported; effectful receivers
remain refused. Direct declaration metadata remains supported. Finite dynamic
dispatch and synthesized getter candidates follow [finite-dispatch.md](finite-dispatch.md)
and [getter-dispatch.md](getter-dispatch.md).

The declaration index is finite and rejects duplicate or missing identities.
Depth and declaration traversal have explicit bounds. Unknown node kinds,
literal/operator/location shapes and missing required type/prefix metadata fail
closed. `ScopeScan.within` proves that every feature in a successful result is
in the selected profile. It does not prove extractor completeness or source
lowering correctness. These feature families therefore remain `partial` in the
inventory; recursive nominal types and ABI-v1 decoder interfaces remain separate
integration work.

Source names keep their raw semantic spelling. Emitted Lean syntax quotes
identifiers, including dollar names and keywords; macros recover raw names.
Positive declaration IDs distinguish user functions and fields from builtins.
Specification and loop scans use syntax and lexical binders, including quantified
names, instead of matching words inside strings/comments. An inherited builtin
observation shadowed in the executing contract receives an implementation
diagnostic rather than changing its meaning silently.

The literal reader now handles rational remainder, signed bit operations and
arithmetic right shift, evaluated outer array bounds, exact string/Unicode/hex
bytes, zero scientific constants with extreme exponents, and degenerate powers.
General constant-materialization bounds remain. Address literals and conversions
retain their ABI kind through captures, arrays, conditionals and lazy expressions.
Canonical assembly rethrow requires the exact shape and matching memory-bytes
declaration identity; ordinary integer pointers do not qualify.

## Review and validation

Read-only finder and skeptic reviews found and prompted fixes for semantic
name emission, inherited invariant escaping, selector-only dependencies, aliased
self-calls, self-payment dispatch, missing AST type/prefix metadata,
deployment-only argument leakage, modifier dispatch and lexical loop/specification
scope. Reviewers did not run Lean or modify files.

Per-file Lean diagnostics pass for the changed frontend and all three source
regression modules. Kernel-checked execution covers literal/address/identifier
examples. A universal remainder correctness theorem and a false remainder
counterexample both check; headline theorem axiom reports use only the standard
`propext`, `Classical.choice` and `Quot.sound` axioms.

`scripts/check-source-admission.mjs SOLJSON SHA256 MODULES_DIR` independently
compiles and executes 22 cases for each pinned compiler across legacy/via-IR
under Cancun, including the expected Panic(0x01) rejection, and checks six invalid
sources, four invalid pragma combinations and three accepted modes per compiler.
This optional reference uses external EVM test packages;
the Lean package still has no external dependencies. Modern fixture defaults use
Osaka; the reference's EVM target is recorded separately and is not an EVM theorem.

Frozen TestSuite AST regeneration was byte-identical. Final library, TestSuite,
sort/corpus, automation and structural checks are pending the final validation
run. The pre-existing baseline has 33 scratch-module orphans and 13 missing
external/vendor documentation paths; these are not introduced by this milestone.

## Stored external function observations

The source reader retains `address` and `bytes4` casts around stored external
function members before the native `fnPure` pass turns them into quotient and
remainder arithmetic. ABI packed addresses therefore occupy 20 bytes and packed
selectors four; standard selectors remain left aligned in a 32-byte word.

Admission accepts this path only with matching result metadata, an external
function type at the outer level (and matching type identity when retained),
and a stable receiver place. Calls, assignments,
increments and compound indices remain refused: the native selector lowering
reads its receiver twice, so accepting an effectful receiver would duplicate
effects or callbacks. No new callback semantics or dispatch targets are assumed.
Direct function declaration selectors retain their existing receiver helper.

Regression checks pin the source casts, reject internal/malformed/effectful
receivers, and execute the ABI packed/standard/concat layouts in
`Examples/Tactics/SourceAdmissionImport.lean`. The existing false
`storedFunctionKind` assertion becomes admitted rather than being rejected for
missing implementation; accepting its syntax is not a proof of that assertion.

This patch has not run Lean diagnostics or builds; integration must validate
`Frontend/SolcJson/Body.lean`, `Frontend/SolcJson/Admission.lean`, and the
regression module before claiming coverage. General function dispatch admission
remains a separate prerequisite for the full FunctionTypes source suite.
