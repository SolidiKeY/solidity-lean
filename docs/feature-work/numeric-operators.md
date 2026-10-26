# Resolved operator-alias patch

Integration status (2026-10-26): included in the shared checkout. Current
combined validation is tracked in [integration.md](integration.md).
Worker handoff statuses and isolated validation results below are historical;
they neither report the current combined checks nor establish full source support.

Worker handoff (historical): **patch_ready_unvalidated**. This worker produced an implementation
patch outside the checkout without running Lean, MCP diagnostics or Lake.
That preparation status is separate from the integrated implementation and
the combined checks recorded in integration.md. The broader numeric-operators group is incomplete.

## Source boundary and lowering

Solc records a used operator's resolved pure free function in the `function`
field of `UnaryOperation` or `BinaryOperation`. The reader now checks that
identity against the declaration table and emits a direct call to the existing
unique `solcFunction<ID>` helper. It never guesses a function from its name and
never executes the builtin operation as a fallback. Both minus signatures are
separate: unary `-` and `~`; binary `&`, `|`, `^`, `+`, `/`, `%`, `*`, `-`,
`==`, `>`, `>=`, `<`, `<=`, `!=` — fifteen tokens and sixteen signatures.

`operatorAlias?` in `Frontend/SolcJson/Body.lean` validates the annotation,
positive function/type identities, definition, pure/free function kind, arity,
UDVT declaration, identical nominal operand identities, and the single return
(bool for comparisons, the same UDVT otherwise). Null, malformed, missing,
nonpositive, foreign and signature-mismatched annotations fail closed. Modern
fixtures retain scalar UDVT `typeIdentifier` metadata; equality of underlying
primitives cannot establish nominal equality. Historical fixtures without this
metadata must be regenerated before they can admit used aliases. JSON remains
the existing external compiler input boundary, not another model term language.

Admission calls this same validator instead of unconditionally rejecting used
aliases. It records `operatorAliases`, and the importer adds resolved operators
to its call graph. The existing transitive execution-root scan therefore checks
the alias body's feature uses and callees; a pure alias using excluded creation
code remains excluded. Declaration-header traversal still does not execute an
arbitrary function reference. Inventory status is not used as admission policy.

Calls elaborate into the existing intrinsic `Stmt.call` and its typed frame,
callee body and arguments. `hoistArgs` now holds an earlier non-simple argument
before hoisting any later argument. This closes the failure-order hole where a
later cast, fixed-array-length bounds check, narrow guard or modular guard could
run before an earlier pending expression. Bare names keep the existing
effect-sensitive policy; literals and existing immutable captures need no new
capture. Primitive captures preserve their source byte/address/enum/function
metadata as well as their bit width, preventing newly held bytes2 struct
arguments from losing their right-padding conversion to bytes4. No runtime term, rule, soundness theorem or evaluator
is replaced. Aliased operands use the call path's left-to-right capture in both
compiler pipelines; ordinary builtin binary operations keep their selected
pipeline order. Alias calls remain inside lazy boolean and conditional branches.
The callee keeps its own checked/unchecked body, including when called from an
unchecked expression. Discarded results still execute the call and preserve its
failure. `pureExpr` treats an alias as a call, so the older conditional-callee
rewrite cannot silently duplicate or reorder it.

Scalar UDVT registration now accepts the existing narrow integer, fixed-bytes,
boolean and address representations, including payable addresses. Narrow UDVT
parameter entry bounds use the resolved underlying spelling instead of the
nominal source name. A discarded UDVT binary/conditional result uses that
resolved scalar type. This does not add a nominal runtime sort or erase any
intrinsic statement/formula: nominal legality is checked at the compiler input
boundary, while widths and byte/address metadata use the existing elaborator.

## Regression targets and performed checks

`tests/operators-0.8.38/OperatorAliases.sol` deliberately assigns custom meanings
that disagree with builtin arithmetic and comparisons. Its modern AST fixtures
cover both pipeline selections. `Examples/Tactics/OperatorAliasesImport.lean`
contains complete intended proof scripts for all sixteen signatures, distinct
UDVTs with equal underlying primitives, bool/bytes2/int16/address/payable
underlyings, nested aliases, one capture of incrementing operands, lazy boolean
and ternary branches, custom division/remainder accepting zero, callee wrapping,
checked callee failure under an unchecked caller, discarded unary/binary calls,
left-operand revert/panic priority, and a false builtin-style assertion. It also
checks admitted feature reports and transitive exclusion of an alias body.

The same Lean module includes malformed-AST tests for missing/null/wrong
annotations, wrong arity/prefix/token, absent or distinct nominal identities,
wrong result type, non-pure/non-free/undefined targets. Admission and lowering
must both reject them. A universal `customZero` correctness proof and a concrete
refutation of `falseBuiltin` are supplied. None of these Lean scripts has been
checked by this worker.

The worker did execute the standalone `scripts/check-operator-aliases.mjs`
against the exact solc 0.8.38 SHA-256 pin
`6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`.
All **38 EVM executions**, **8 upstream rejection cases**, and both fixture
metadata checks passed. Failure vectors compare actual revert bytes, including
Panic(0x01), Panic(0x11), and empty reverts. This reference uses external test
packages outside the Lean package and proves no compiler/model correspondence.
The compiler rejection cases also pin their expected diagnostic type and code.
Both modern fixtures were generated by the patched script into the worker's
private files directory; the real checkout was never written.

The integrator's intended checks are per-file Lean diagnostics for Body,
Contract, Admission, Syntax/Elab/Stmt, Syntax/Elab/Values and
OperatorAliasesImport, the new kernel proof/AST tests,
headline `#print axioms`, then the normal library/TestSuite/frozen-sort and
structural gates. Re-run the independent reference with:

```sh
node scripts/check-operator-aliases.mjs SOLJSON_FILE NODE_MODULES_DIRECTORY
```

`origin/master` was inspected: its 52 newer commits change frame/loop and
calculus APIs but not these importer files. This patch does not restate a frame
or loop API. It uses the current source-import examples' `Prog.run`, `spec!`
and `Modality.afterRunTR_not_panic` APIs; their compatibility still needs the
integrator's kernel check after merging. Shared-file base bytes accompany the
patch for three-way merging with concurrently finishing source-admission work.

## Remaining scope

This is a connected scalar-alias milestone, not completion of all numeric IDs.
UDVT fields/aggregate shapes still depend on the ordinary struct/type metadata
interfaces; nominal enums, recursive aggregates and general function dispatch
remain separate work. Conditional function callees with aliased/effectful
arguments remain explicitly refused by the existing conservative rewrite.
General signed shifts/complements, contextual literal promotion and nested numeric
positions remain separate work. Failure ordering is repaired here for argument
lists; other independent expression-hoist policies remain unchanged.
Solidity itself rejects UDVT compound assignment aliases; the reference pins
that rejection instead of inventing overload semantics. Likewise, ambiguous
same-scope overloaded function names in a using directive are rejected upstream;
the implementation resolves accepted bindings by compiler ID.

After validation, the integrator should update the operator-alias inventory row
and generated evidence consistently. This unvalidated worker does not upgrade
shared feature status or claim that source acceptance is a soundness theorem.

## Read-only patch review

Read-only finder and skeptic reviews identified the later-prefix failure-order
hole and the scalar byte-kind loss exposed by stricter argument captures. The
patch addresses both and includes focused source/native regressions. Native
checked tests use full-width overflow to distinguish assertion panic from a
bounds revert; unsigned division by zero is not guarded by `checked`, so it
would not establish that distinction. Source division/bounds/modular reference
cases pin exact EVM panic codes, while their ordinary Lean runs only assert
failure. These tests do not claim a general panic-code correspondence theorem.

Extra necessary captures can enlarge elaborated programs and change output
pins. `git log` records `1a7d5b0e` (one callee body elaborated/quoted once) and
`63ac4b63` (split Elab); this patch preserves both designs. The worker has not
measured Lean checking cost and has not raised heartbeat limits. Reviewers did
not edit the real checkout or invoke Lean; final kernel validation and output
pin/performance assessment remain the integrator's task.
