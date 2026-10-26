# Declarations and metadata

## M1: compiler-resolved metadata (2026-10-25)

`Frontend/SolcJson/Body.lean` resolves `type(C).name` from the contract
declaration's name and produces its UTF-8 string literal. `type(I).interfaceId`
XORs exactly the selectors of ordinary external/public functions declared in
`I`, including its own overloads and overrides. Inherited methods and
receive/fallback declarations contribute nothing.

Error selectors are four bytes; non-anonymous event selectors are 32 bytes.
Both come from solc's exact canonical ABI metadata and are resolved by
declaration ID, including qualified declarations with the same short name.
The parser returns `Fin (2^(8*bytes))`, carrying the ABI bound in its result.
Malformed widths/non-hex digits fail closed. Anonymous event selectors are
refused independently of the compiler's source validation. The source compiler
continues to reject invalid contexts such as an ambiguous overloaded method
reference or a public function's declaration-selector access inside its own
contract. No selector uniqueness or hash injectivity is assumed.

The compiler helper retains selector fields and additional declaration IDs
only where the source observes metadata. The frozen TestSuite fixture stays
byte-for-byte unchanged. Metadata inherits the frontend's existing validated
compiler/fixture boundary; this milestone adds no compiler-correctness theorem.
The source fixture uses the repository's SHA-pinned solc 0.8.34; the metadata
rules were checked against `Types.cpp` at the inventory's pinned 0.8.38 commit
`1835d247de183f23e7b0e2bc4a50732af525b77c`.

Static declaration selectors and `this.f.selector` fold directly. A dynamic
function selector uses a fresh pure helper consuming its receiver argument;
the existing typed call elaborator evaluates that argument exactly once in
its original expression position. Boolean and conditional arms remain lazy.
Unnamed input parameters now receive collision-avoiding names derived from
declaration IDs, so otherwise supported unnamed signatures elaborate. Unnamed
returns retain the existing return-frame naming convention.

The fixture covers contract-name bytes, interfaces with inherited methods,
selectorless entries and overloads, enum/value-type error parameters, tuple
event parameters, qualified errors, function selector/address projections,
overload calls and receiver effects. Its deliberately false interface-ID
assertion must remain pending. The Lean example retains kernel-checked
interface-ID and receiver-evaluation proofs and malformed/anonymous metadata
rejection cases.

### Review and validation

The read-only finder and skeptic reviewed importer metadata, compiler-field
retention and renaming. Confirmed fixes exclude selectorless interface entries,
preserve effectful receiver evaluation, and keep lazy receiver expressions in
their arms. An attempted rewrite of aliased function values was removed:
the existing function-value packer hashes model names, so renamed inherited
values need a separate source-signature representation change. Their suggested
overloaded-pointer example is rejected by the pinned compiler; inherited
aliases remain a relevant unsupported boundary. Neither review called Lean.
The follow-up finder also found that helper names could collide with a
generated local alias. Freshness now avoids generated local/state names as
well as original names; a shadowed-local regression is also tested through
an inlined call.
Only selectors with dynamic receivers add helpers. Static `this.f.selector`
keeps the existing literal form used by function-value proofs.
Generated helpers carry an `#internalEntry` marker in the existing width
metadata table, whose `#` separator cannot be a Solidity identifier. Internal
and external function-value construction, dispatch, and dynamic call-graph
analysis exclude them while direct generated calls still work. Filtering
preserves the original function-tag indexes. Kernel tests reject helper tags
and selectors. This is importer metadata, not a second state representation.
The `1a7d5b0e` history entry introduced body memoization for checking speed;
that memoization and segmented contract compilation are retained.
The final read-only skeptic confirmed that value construction, indirect
call-graph analysis and both dispatch forms respect the marker, while direct
generated calls remain available.

The final `./run-lean.sh` completed successfully: 579 library jobs, 241
TestSuite jobs and the frozen SolKey sort gate (377 taclets, 131 read-bearing
annotations). The three headline proofs depend only on `propext`,
`Classical.choice` and `Quot.sound`. Per-file MCP error diagnostics passed
for every edited Lean file. The frozen TestSuite AST is byte-for-byte
unchanged, and its no-Lean report/automation audits pass (491 automatic,
61 budgeted, 11 refuted, zero pending). The generated feature audit is current.
The final frozen corpus gate also passes: 774 obligations with no verdict or
generated-output drift. Detailed logs are recorded in the shared group status.
The documentation-path check retains its 13 pre-existing missing vendor/external
references; `git diff --check` is clean.
The existing function-type source suite still leaves `externalValue` pending.
It also stays pending with compiler selector fields removed, no generated
helpers, and original unnamed-return conventions; its expected `proved`
verdict remains unchanged. The contract reader at `3f5f3f4b` was also replayed
in a separate namespace against that original-selector AST: every lowered
contract/function field matched the current reader exactly. All other selected
function-value rows pass.
The new source suite has 13 proved rows, one internal helper row and one
deliberately pending false property. The modifier, inheritance and free/library
source tests pass. The metadata example built in 16 seconds both before and
after helper isolation. The no-build metadata source suite took 70.7 seconds
before isolation and 75.6 seconds after, while the final rebuild also ran;
this is not an isolated performance comparison.
The unfiltered orphan check reports 33 pre-existing scratch modules; the new
example is reachable. Layering remains clean. Existing artifact-cache hardlinks
for `KeySort.ilean` and `KeyTaclets.ilean` were read-only; their local build
copies were detached without changing the shared cache.

### Remaining declaration work

This milestone does not close the whole declaration group. Import/remapping
resolution across source units, exact synthesized public getters (including
struct omissions and interface overrides), inherited external function values
with renamed model declarations, broader `using for` forms, and remaining
constructor/immutable/entry-visibility distinctions still require dedicated
implementation and validation. Existing C3, base-body, modifier continuation
and constructor implementations were inspected but are not claimed as new
work here. Abstract-contract `.interfaceId` metadata is also still refused;
the implemented inventory family is `type(I).interfaceId` for interfaces.
Raw fallback bytes and observable event logs retain their declared exclusions.
The auxiliary contract-wide `#verify`/`#counterexample` tools may still display
synthetic helper obligations when invariants are present, and `#difftest` may
enumerate helpers. The source testing API uses source import rows and does not
include these helpers. This reporting cleanup remains separate from runtime
dispatch isolation.

The next getter milestone needs one shared ABI identity for source declarations
and renamed model functions: both getters beside storage roots and inherited
external function values need it. The pinned compiler's
`FunctionType(VariableDeclaration const&)` consumes mapping keys and ordinary
array indexes, returns bytes/string whole, and omits struct mapping/ordinary
array members. Getter functions returning references also need the world's
return-value interface; the existing external-call elaborator currently
accepts primitive returns there. These interfaces should be coordinated with
contract-world before adding a second getter-only representation.
