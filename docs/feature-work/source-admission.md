# Source admission milestone

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
is implemented. General function-value dispatch and used operator aliases also
remain implementation gaps. Scope decisions never depend on inventory status.
Stored external-function `.address`/`.selector` observations also need a typed
ABI-kind interface: the existing function-value lowering turns them into plain
arithmetic. Modern admission refuses that shape so a wrongly packed value cannot
support a source proof. Direct declaration metadata remains supported.

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

### Function-value source regression alignment

The combined Dafny/editor validation exposed older function-value test
expectations that predate admission commit `ea06b814`, already present in the
initial `23d23377` checkout. The modern source interface refuses unresolved
value-call dispatch and stored ABI-kind observations; the intrinsic tag model
does not justify admitting them as source proofs.

The updated integration test pins all 24 qualified function rows in source
order: three direct proofs, three internal helpers and eighteen explicit
`solidity.functionDispatch` gaps. Every gap retains its exact diagnostic reason,
the report has no global errors, and the strict suite verdict remains false.
Direct `ext`, `externalSelector` and `equality` proofs remain required. Unrelated
functions named `externalValue` in the binding and inheritance fixtures retain
their original proof expectations.

The focused real-source test passed in 11.14 seconds. Independent read-only
finder and skeptic reviews confirmed the complete row roster, baseline policy
and strict verdict; neither ran Lean. This changes test expectations, not the
admission policy or the runtime model.
