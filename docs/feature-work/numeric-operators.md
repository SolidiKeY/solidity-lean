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

## Group 03 upstream revalidation (2026-10-26)

This independent repair starts from `origin/master` at
`006fcd593f5beeb540e7adf2bc76de4638566924` on branch
`codex/group03-operators`. The managed executor is `/workspace/solidity-lean`;
`/workspace/.setup/activate.sh` supplies Lean 4.24.0 and Lake
5.0.0-src+797c613. `lake build Solidity.KeySort` succeeded both before and after
switching to the requested base. The runner verified all 11,622 pinned archive
files. The first runner invocation hit its five-minute cold dependency-build
limit before executing a fixture; a separate logged build of
`Solidity.Tools.Upstream` completed, without changing execution/proof limits.

All fourteen assigned paths were reproduced individually with `--batch-size 1`
and separate output directories before editing. Seven already matched every
required pipeline on current master. The old corpus results remain historical
observations on `cadb628c`, not current failures.

The patch reuses existing declaration-indexed alias/call machinery:

* Scalar constant substitution now admits the same supported resolved scalar
  types as UDVT registration. Its existing ID lookup and source cast retain
  narrow widths, bytes padding and address kind. This fixes constants such as
  `Int constant ONE` with underlying `int8`, previously omitted as storage.
* Builtin signed complement at the source boundary becomes `intN(-1) - x`.
  Aliased operators are resolved first and keep their original callee. The
  operand occurs once and the exact signed width remains explicit. The checked
  integer identity `~~~x = -1 - x` and signed-range closure prove that the rewrite
  handles both endpoints without an intermediate negation overflow. Intrinsic
  operator definitions, runtime rules and their soundness proofs are unchanged;
  this does not extend native signed `~` syntax.
* Replay selects the canonical ABI signature attached to the imported function's
  source declaration, requiring a selected external entry. It no longer compares
  a nominal source name such as `Fixed` against ABI `int128`. Internal helpers
  cannot capture an ABI call. Rows without a source declaration retain the
  existing signature fallback used by native controls. A present declaration
  without a canonical signature does not fall back.
* An inconclusive runtime call retains the completed observations, the current
  blocked vector and the precise fuel/panic/return diagnostic. It remains blocked
  before expectation comparison. This repairs reporting, not runtime semantics.

`tests/upstream/Operators.lean` checks source constants, signed 8/64/256-bit
endpoints, checked single-evaluation operands, unchecked minimum boundaries,
byte padding, a false assertion and nominal overloads colliding with an internal
ABI-shaped signature, in both pipelines. Its ten printed theorem axiom sets are
subsets of `propext`, `Classical.choice`, `Quot.sound`. The new fixture was produced
with the SHA-checked 0.8.38 compiler; its source SHA-256 is
`a611b835995d4beda5a9dbc666c26b59f52b1a465de3d2dd7e2eff01bc186e25`.
The final two replay regressions additionally pin observation retention after a
successful stateful call followed by fuel exhaustion or generic panic.

The source/expectation archive, snapshot manifest and historical results are
unchanged. No dependency, axiom, `sorry`, heartbeat override, representation
refactor, spelling-based operator dispatch or Bridge change was added. General
inline assembly remains excluded: these cleanup fixtures need dirty-word and
machine-memory semantics, not another alias lookup. Huge recursive failure
vectors cannot pass merely because execution exhausts resources.

### Final assigned-fixture outcomes

Every filename below has prefix
`test/libsolidity/semanticTests/operators/userDefined/`. Historical status was
broken for all fourteen; “before” is the fresh current-master reproduction.

| Fixture | Before | Final legacy / viaIR | Disposition |
| --- | --- | --- | --- |
| `all_possible_operators.sol` | broken | working / working | repaired |
| `all_possible_user_defined_value_types_with_operators.sol` | working | working / working | already fixed on master |
| `attaching_and_defining_operator_with_same_function.sol` | working | working / working | already fixed on master |
| `consecutive_operator_invocations.sol` | working | working / working | already fixed on master |
| `fixed_point_udvt_with_operators.sol` | broken | working / working | repaired |
| `multiple_operator_definitions_different_types_different_functions_separate_directives.sol` | working | working / working | already fixed on master |
| `multiple_operator_definitions_same_type_same_function_same_directive.sol` | working | working / working | already fixed on master |
| `operator_definition_shadowing_builtin_keccak256.sol` | working | working / working | already fixed on master |
| `operator_parameter_and_return_cleanup_between_calls.sol` | broken | excluded / excluded | expected exclusion: inline assembly |
| `operator_parameter_cleanup.sol` | broken | excluded / excluded | expected exclusion: inline assembly |
| `operator_precendence.sol` | broken | working / working | repaired |
| `operator_return_parameter_cleanup.sol` | broken | excluded / excluded | expected exclusion: inline assembly |
| `recursive_operator.sol` | broken | blocked / blocked | ABI repaired; loop fuel exhausted |
| `unchecked_operators.sol` | working | working / working | already fixed on master |

The three assembly cases retain raw runner status `broken` with every
`variants[].gaps[].status` equal to `excluded`; the table labels their actual
admission boundary rather than claiming Lean support. The recursive report
retains both completed `testUnary` observations in each pipeline and the
`99999999999` input at which loop fuel is exhausted. Subsequent vectors remain
unexecuted, so the complete fixture is blocked. No expected failure is inferred
from exhaustion.

The broad value-type fixture already passed on master. An intermediate rerun
timed out under concurrent verification; that evidence is retained. Its final
serial rerun passed both modes with the original 120,000 ms per-process timeout
and 1,000 loop fuel (238.135 seconds including both modes and setup).

Full before/intermediate/final reports, per-source SHA-256 values and exact
argument lists are saved in [group03-results.json](../../tests/upstream/group03-results.json).
The final model SHA-256 is
`0e9eb4d5e568b5b51a223d5e3be435b34088b20a7e4176112e4ce32e8ef23b8f`.
The current-master before hash is
`c86945ed62a18ffccf0b72b291c6271f44462f7b1d60b101e73fd2ec565c8699`.
Historical model hashes remain in the original results. All stages use compiler
SHA-256 `6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`,
archive SHA-256 `9200f2a26b08be5b77faf877c44f5cfbf5ea95f1bccc45dae559d2fbc7cefb2d`,
and unchanged runner SHA-256
`c860ec034b8dbf26c632f45a0c52c215df9eda9fc2fd10e3c3f8b84f4a37d468`.

### Reproduction and review

```sh
cd /workspace/solidity-lean
source /workspace/.setup/activate.sh
lean --version
lake --version
lake build Solidity.KeySort
node scripts/solidity-upstream.mjs verify
node scripts/solidity-upstream.mjs run \
  --compiler /workspace/.setup/soljson/soljson-v0.8.38+commit.1835d247.js \
  --filter test/libsolidity/semanticTests/operators/userDefined/all_possible_operators.sol \
  --batch-size 1 --out .lake/upstream/group03-recheck/all_possible_operators
node --test --test-isolation=none scripts/solidity-upstream.test.mjs
lake --no-build lean tests/upstream/Replay.lean -- --tstack=131072
lake --no-build lean tests/upstream/Operators.lean -- --tstack=131072
node scripts/check-automatic.mjs --strict
node scripts/check-orphans.mjs
node scripts/check-layers.mjs
scripts/check-testsuite.sh --complete --solkey tests/migration/solkey/keyext.solidity.examples
scripts/check-solkey.sh --key tests/migration/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key
```

Each of the other thirteen exact filters and its distinct output directory is
recorded as an executable argument list in the evidence file. Do not reuse
`tests/upstream/results` for retries. Fixture generation uses
`scripts/solc-ast.mjs --compiler-file FILE --compiler-sha256 SHA --source
tests/operators-0.8.38/OperatorBoundaries.sol --out FILE --no-wrapper`
with `--via-ir` for the IR fixture.

Lean MCP diagnostics were not exposed. Configured per-file commands checked
Body, Contract and Upstream with `lake --no-build lean FILE -- --tstack=131072`.
Their wall times were 32.920 s, 32.471 s and 3.073 s respectively. Final focused
operator controls took 10.499 s and final replay controls 5.047 s. No heartbeat
limit was raised. The 14 adapter tests, strict automation (491 automatic,
61 budgeted, 11 refuted, zero pending), reachability (667 modules, zero orphans),
layering (143 core modules, zero frontend reach), frozen TestSuite audit and
frozen sort check (377 taclets, 131 read-bearing annotations) passed. The
documentation-path check retains its 13 baseline missing references outside
this patch.

Independent read-only finder and skeptic reviews inspected the actual patch,
metadata hashes, nominal lookup, signed range/effects and native fallback. The
skeptic required the selected-external-entry guard, which is implemented and
covered by the internal/external overload collision. A final skeptic pass
confirmed that observation retention cannot turn inconclusive execution into
a matching expected failure. Neither reviewer opened a Lean worker. No
confirmed review issue remains.

The shared integration dependencies are limited to the scalar constant filter
in Contract, signed source complement in Body, and declaration-bound ABI lookup
plus blocked-prefix evidence in Upstream. No unpublished group patch is required.
Runtime fixture agreement is observational evidence; only the stated algebra
and concrete regression claims are kernel proofs, not a universal solc/model
correspondence theorem. Compiler acceptance is reference-solc evidence.
