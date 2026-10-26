# Finite source dispatch admission

Integration status (2026-10-26): included in the shared checkout. Current
combined validation is tracked in [integration.md](integration.md).
Worker handoff statuses and isolated validation results below are historical;
they neither report the current combined checks nor establish full source support.

This patch restores source admission for ordinary internal and own-external
function-value calls with scalar/function parameters and returns. It changes
source extraction and dependency closure; the intrinsic program, interpreter,
calculus and proof system are unchanged. No dependency, axiom or admission
exception is added.

`Frontend/SolcJson/Contract.lean` retains a bounded typed source signature beside
its native dispatch key. Word widths are indexed by `Fin 32` in bytes; fixed
byte widths by `Fin 32`; bool, address and nested function types have distinct
constructors. The parser consumes fuel through nested function types. Mutability
qualifiers are ignored as the existing native function-value representation
ignores them. A native key may map address to uint; equality of that key alone
never admits a call. Every native-compatible candidate must also have the exact
retained source signature.

Candidates come from the current reader's source function declarations: own,
inherited and imported free/library functions, each with a declaration ID and
its actual model name. The source candidates also include receive/fallback
entries: a matching native signature is explicitly refused because Solidity
cannot name those special entries as function values. Generated selector helpers
are absent, agreeing with native `fnSource`. Synthesized constructor-body helpers
are now added to `SolcContract.internalFuns`, so the existing production import
adds their `#internalEntry` flags after choosing the plain/full/initializer
contract assembly; native `fnSource` excludes them on every dispatch path.
Matching the native `FunDecl.sigTy?` and `extTy?` component
spelling yields a conservative superset of targets: this patch does not prune
by native `fnReachable`, known assigned values, declaration order or emitted
member membership. Every function native dispatch can select is included;
additional candidates may reject an otherwise usable source program. Their IDs
are added to the dependency graph before member ordering/emission. Existing
cycle-aware finite reachability then scans their bodies, transitive direct and
dynamic callees, selected modifiers and lexically resolved specifications.
Inherited override aliases retain both the original declaration and the
most-derived declaration target, rather than looking up a spelling globally.
Initializer and composite-constructor closures carry these dependencies too.
External dynamic calls conservatively set the writer/callback-summary flag.

This is an executable extraction boundary, not a proof of source/native
simulation or extractor completeness. Its relation to native dispatch depends
on the existing reader's type spelling and declaration-name mapping. The native
signature projection is checked against the source signature, not treated as a
replacement for it. Unknown/missing candidate signature metadata refuses a
call, rather than disappearing from its target list. Known reference parameters
have no native `sigTy?`; a dynamic signature containing references is itself
refused. Typed states still admit unspecified/unassigned function tags and the
existing dispatcher retains their revert behavior.

The following boundaries remain explicit `solidity.functionDispatch`
diagnostics:

- Reference/nominal function signatures, unknown type metadata and missing
  candidate or override declaration identities.
- A native-compatible receive/fallback special entry, which cannot legally
  be named as a Solidity function value.
- Source-kind collisions among native-compatible candidates, including
  address versus uint. All candidates are checked even if a source-text
  points-to approximation would omit them.
- External dynamic calls with several return values, matching native's limit.
- External candidates declared private/internal, and inherited/overloaded
  candidates whose generated model name differs from their source name. Native
  selector construction uses the model name; this patch refuses that mismatch
  until source selector identities are retained by the separate declarations
  work. Ordinary internal inherited dispatch remains supported.

Direct declaration-selector metadata keeps its existing header-only dependency
behavior. Stored external `.address`/`.selector` projection kinds are handled by
the separate projection patch; this change does not edit their lowering or
admission rule. Arithmetic cancellation is also separate.

## Review and validation

Worker handoff (historical): **patch_ready_unvalidated**. No Lean server, build, source proof check or
repository mutation was performed in the preparation lane. The changes are
prepared outside the shared checkout. The implementation is now included in
the combined validation tracked in integration.md.

`node --test scripts/finite-dispatch.test.mjs` checks the original FunctionTypes
positive verdicts, keeps the original false/unassigned diamonds pending, tests
clean inherited internal admission, and checks that poisoned/transitive targets,
modifier targets and target specifications remain visible to admission. The
specification regression uses excluded `block.number` and the real `solc_import`
command, invoking production specification callbacks rather than only the AST
walker. Negative cases cover address/uint collision, missing callee/candidate metadata, reference
signatures, private external targets, receive/fallback candidates and inherited
external selector renaming. A production import checks native `fnSource = false`
for synthesized constructor helpers while retaining a clean dynamic entry.
The existing SourceAdmission modifier regression changes from an unresolved
call diagnostic to the excluded block-number feature reached through its body.

Apply to a stable checkout, check Contract and the affected example with
per-file diagnostics, rebuild the frontend, and run both the new tests and the
existing `function types:` source test. The original `externalValue` proof also
needs the separately diagnosed cancellation repair; this patch preserves its
expected proved verdict. Then run the frozen source, TestSuite, sort/corpus,
feature-inventory, layering and automation gates. A read-only finder/skeptic
review remains required before considering this milestone validated.

A read-only skeptic found two issues in the first staged version: a specification
test used a supported timestamp observation and bypassed the production
specification callback; the candidate set omitted native receive/fallback entries
and unflagged constructor helpers. This staged revision corrects the tests,
includes/rejects matching special entries, and flags synthesized helpers through
the existing native mechanism. The preparation worker ran no Lean checks;
current combined validation is tracked in integration.md.

## Source external-function receiver cleanup

Imported contracts retain source declaration metadata in `Contract.funs`,
including while their functions are inlined. External function-value dispatch
uses that marker to separate the raw packed-address quotient from the receiver:
the selector is still `h - (h / 2^32) * 2^32`, while a second local captures the
real `address(rawQuotient)` conversion before the external try-call. The raw
quotient is declared `uint` so address-kind inference cannot incorrectly treat
it as already cleaned. Calls use the cleaned local, including the unknown
selector fallback. Native contracts whose declarations all have `sourceDecl =
none` retain their original lowering and wider transaction-address API.

`Examples/Tactics/FunctionTypes.lean` supplies concrete lowering controls: a
metadata-marked contract still calls itself successfully at address 7; a native
self address of `2^200` remains callable; the same deliberately out-of-EVM state
in the source lowering cleans the receiver to zero and reverts. These isolate
the conversion and preserve the existing native API. The compiler-imported
`externalValue` source test remains the end-to-end proof regression. Validation
of this integration is recorded in [integration.md](integration.md).
