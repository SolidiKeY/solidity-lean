# Source admission

Which compiler output the solc importer accepts, and what it refuses before
lowering. Inventory status: partial (admission is checked; extraction
completeness and lowering correctness are not proved).

## Supported

- **Compiler provenance.** `scripts/solc-ast.mjs` records the compiler file,
  version and SHA-256, the source SHA-256, the accepted pragma tokens, the AST
  analysis stage, and the pipeline, EVM target, optimizer and output settings.
  The pinned 0.8.34 and 0.8.38 compilers are both supported. The record is
  `N.report.provenance` (`Frontend/Source.lean`). `--via-ir` selects
  source-order operand scheduling; a requested ABI-v1 under via-IR records the
  effective ABI-v2. Modern fixtures default to Osaka.
  `Provenance.compilation` distinguishes historical inputs from analysed
  pipeline/settings records. `legacyFixture`, `pipeline`, `settings` and
  `effectiveCoder` are derived observations: they cannot be updated separately.
  Settings text is validated by `Source.read`; constructing a provenance record
  directly is not a validation certificate.
- **Static compiler-code inputs.** `Source.readCompilerCode` accepts bounded,
  linked hex artifacts only with matching modern compiler/source/settings
  provenance and declaration identity. These supply static creation/runtime
  constants; they do not model deployed-account code or prove compiler
  correctness. Historical fixtures cannot acquire these observations.
- **Historical fixtures.** Four-field fixtures still load with
  `admissionChecked = false` (`legacyFixture`); regenerate them with
  `--legacy-fixture` only to keep that boundary. They keep their pinned legacy
  statuses.
- **Admission scan** (`Frontend/SolcJson/Admission.lean`). It covers known
  nodes, semantic type metadata, call options, arguments, selected modifiers,
  execution dependencies and lexical specifications. Declaration references
  follow headers by compiler identity. Mutable initializers and base-constructor
  arguments execute only at deployment. Metadata-only selectors pull in no
  function bodies. Possible self-calls include cast and aliased receivers.
  `ScopeScan.within` proves that every feature of a successful result is in the
  selected profile. Scope decisions never depend on inventory status.
- **Names.** Source names keep their raw spelling: emitted Lean quotes
  identifiers, including `$` names and keywords. Positive declaration IDs
  separate user functions and fields from builtins. Specification and loop
  scans use syntax and lexical binders, so words inside strings and comments
  do not match.
- **Literals.** Rational remainder, signed bit operations, arithmetic right
  shift, evaluated outer array bounds, exact string/Unicode/hex bytes, zero
  scientific constants with extreme exponents and degenerate powers. Address
  literals and conversions keep their ABI kind through captures, arrays,
  conditionals and lazy expressions.
- **Stored external function members.** `.address`/`.selector` keep their
  `address`/`bytes4` casts until the native `fnPure` pass, so packed addresses
  take 20 bytes and packed selectors four. This needs matching result metadata,
  an outer external function type and a stable pure receiver place
  (`Examples/Tactics/SourceAdmissionImport.lean`).
- Operator aliases: [numeric-operators.md](numeric-operators.md). Function-value
  dispatch: [finite-dispatch.md](finite-dispatch.md) and
  [finite-dispatch.md](finite-dispatch.md#getter-targets).

Regressions: `Examples/Tactics/SourceAdmissionImport.lean`,
`SourceLiteralsImport.lean`, `SourceIdentifiersImport.lean`.

Unsupported state initializers retain a refused constructor row, including an
implicit constructor; initialization failure cannot become a default deployment.
Pipeline-specific inheritance scheduling is documented in
[the declaration repairs](declarations-metadata.md#group-08-source-lowering-repair-2026-10-26).
[The resumed repairs](declarations-metadata.md#group-08-resumed-remaining-declarations-2026-10-27)
cover static compiler-code artifacts, enum struct dependencies and restricted
mixed storage-return projections. Direct enums and one-dimensional enum arrays
retain exact range premises; composite ABI inputs containing enums remain
refused until recursive cardinality checks exist.

Function-value calls follow [finite dispatch](finite-dispatch.md), including
[getter candidates](finite-dispatch.md#getter-targets) and the restricted
zero-argument internal memory-byte return. Other reference signatures and
renamed inherited external values retain their explicit refusal boundaries.

## Refused, and why

- Unknown modes or settings, mismatched pragma records, incomplete modern
  headers, and a manual `evalOrder` override on a modern import.
- Unknown node kinds, literal/operator/location shapes, missing type or prefix
  metadata, and duplicate or missing declaration identities. The declaration
  index is finite, and depth and traversal are bounded.
- Payment dispatch that needs an inherited receive or fallback, or receive
  modifiers, until that dispatch is implemented.
- An effectful receiver of a stored function member (a call, an assignment, an
  increment, a compound index): the native selector lowering reads its receiver
  twice, which would duplicate effects or callbacks.
- An inherited builtin observation that the executing contract shadows gets an
  implementation diagnostic instead of a silent change of meaning.
- Canonical assembly rethrow only in its exact shape, with the matching
  memory-bytes declaration identity; ordinary integer pointers do not qualify.
- Legacy ABI-v1 decoding is an implementation diagnostic.

## Decisions

- Provenance records an external solc analysis. It does not authenticate
  handwritten JSON or validate bytecode, and it is no theorem of
  compiler/lowering equivalence.
- Representation-limit failures of modern fixtures are implementation gaps,
  reported separately from elaboration status.

## Left

- General constant-materialization bounds.
- Function-value target sets outside the checked finite-dispatch fragment.
- Recursive nominal types ([recursive-types.md](recursive-types.md)) and the
  ABI-v1 decoder.

## Reference check

`node scripts/check-source-admission.mjs SOLJSON SHA256 MODULES_DIR` compiles
and runs the cases for each pinned compiler, legacy and via-IR, under Cancun,
and checks the invalid sources and pragma combinations.

## Source scope and selector integration

Clashing local bindings use fresh declaration-ID names, preserving outer initializer
reads and restoring the surrounding scope after a block. Source parameters,
loop annotations and certified witness positions retain their compiler identity.
Specification binders retain their nearest lexical scope; the finite-filter
omitted-state check inspects parsed free root reads instead of bound names.

Declaration selectors resolve by compiler ID. Error/event selectors receive no
`.address` exemption; missing identities and same-named local variables cannot
be folded as error declarations. Stable stored external values use the separate
typed ABI projection path. Malformed and effectful projections remain refused.
The integrated source checks require the complete 26-row FunctionTypes roster:
16 proofs, seven internal helpers and three pending false claims. See
[dafny-verification.md](dafny-verification.md#integration-with-current-origin)
for the focused build, source tests and independent merge reviews.
