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

## Group 04: signed shifts, powers and literal typing

Task branch: `codex/group04-signed-numeric`, based on `006fcd593f5beeb540e7adf2bc76de4638566924`.
The attached managed executor passed the runtime gate with Lean 4.24.0,
Lake 5.0.0 and `lake build Solidity.KeySort`. All eleven assigned historical
rows reproduced as frontend import gaps in both required pipelines before edits.
The archived upstream bytes and historical result directory are unchanged.
Shared integration points are limited to `Frontend/SolcJson/Body.lean`,
`Frontend/SolcJson/Contract.lean` and `Syntax/Elab/Values.lean`; the runner is
unchanged, and this branch assumes no unpublished work from another group.
The optional Bridge and obsolete SolKey reader are untouched.

Signed shifts retain the left operand's type and the count's unsigned type.
Right shifts saturate counts at 256 before converting the count to the existing
signed primitive operation. Already-validated literal counts fold to an integer
literal, retaining the existing decision fragment and its proved/refuted pins;
nonliteral counts keep the saturating value expression. `shr_literal` proves the
folded count equivalent. `tests/upstream/group04/ShiftFragment.lean` pins both
verdicts, kernel coverage and rejection of a negative literal count. Left shifts use the operand's word and read the
result back at its signed width. Literal bases retain solc's recorded result
type; the exponent/count does not choose their sign. Colliding local declaration
names, including named returns, are renamed using their declaration identities.
This preserves the inner `x` in the cleanup fixture instead of capturing the
named return. Compiler legality checks remain enabled.

Checked signed power composes existing intrinsic value constructors in
`Syntax/Numeric.lean`: unsigned magnitude, unsigned power, parity, an exact
signed range check and two's-complement result conversion. Zero and unit
magnitudes evaluate the exponent but avoid recursive power evaluation for huge
exponents. The negative result may have magnitude 2^255; a positive result may
not. An invalid signed result uses a signed-overflow witness, preserving the
arithmetic-overflow tag rather than introducing division-by-zero classification.
No statement, value, formula or state representation is replaced. No rule,
axiom, external core dependency or heartbeat limit is added. Existing general
soundness theorems apply to the emitted constructors; numeric lowering proofs
are in `Semantics/NumericLowering.lean`. `checkedSignedPower_correct` names the
actual emitted tree in an arbitrary typed state, assumes successful operand
evaluation, and compares `toOption.map val`; it proves numeric results/range
failure rather than general panic payload or source/compiler equivalence.
The old signed-left-shift exclusion in `Examples/Tactics/Operators.lean` is
replaced by a positive calculus theorem for the same operation.
The negative unsigned-index control in `Examples/Tactics/Decide.lean` still
rejects `values[-1]`; its output pin now records the signed/unsigned type
mismatch produced by literal negation typing.
No Lean MCP diagnostics tool was exposed in this executor. Per-file checks used
`lake env lean --tstack=131072` on the edited modules and source controls; the
final library build checks their imports. Printed proof dependencies contain
only `propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx`.

`tests/solc/SignedNumeric.sol` and its two pinned 0.8.38 ASTs cover negative
operands, signed right shifts, 8/16/256-bit values, oversized unsigned counts,
parity, minimum integers, checked overflow, unchecked wrapping, operand effects,
literal contexts and return/local shadowing. `Examples/Tactics/SignedNumericImport.lean`
checks both imports, runtime observations and kernel-checked positive and exact
negative halt controls. Full-width native controls separately pin the new signed
range witness: ordinary overflow reverts, while the model-only `checked`
extension panics through its arithmetic guard. Large runtime observations are not universal correctness
theorems. The reference-only rejection checks are reproducible with:

```sh
source /workspace/.setup/activate.sh
node scripts/check-signed-numeric.mjs /workspace/.setup/soljson/soljson-v0.8.38+commit.1835d247.js
```

These check two accepted compilations and eight exact diagnostic rejections:
signed counts, signed exponents, negative unsigned literals and illegal narrow
literal-power returns. They establish reference-solc behavior, not Lean coverage.

Read-only finder and independent skeptic reviews used no Lean workers. They
identified declaration collisions, unsigned-count saturation, the overflow
witness's panic tag, ambiguous negative controls and the need for typed-tree
composition proofs. The confirmed implementation/control issues were repaired.
The final finder and independent skeptic recomputed the current model/report/log
hashes and confirmed that literal folding cannot drop effects: its recognizer
accepts only a numeral or its negation, after unsigned validation. They found no
remaining concrete issue and used no Lean workers.
The helper repeats pure value evaluation; nested powers can amplify checking or
runtime costs. This retains the existing hoisting schedule and does not prove
all possible dual-failure priority cases. Generic magnitude-power overflow
beyond uint256 still shares the existing lack of precise self-call panic data;
this milestone does not claim general self-call panic-payload equivalence.
The model-only `checked`/`ignoringOverflow` extensions can inspect the new signed
overflow witness; no claim is made that this repairs unsigned-power guards there.

Final exact fixture results (both legacy and viaIR): **11 broken → 11 working**,
with **224 retained observations**, zero already-fixed cases, zero assigned
expected exclusions and zero assigned adapter/resource blocks. Complete reports,
source/model/compiler/runner hashes and every exact command are in
`tests/upstream/group04/validation.json` and its before/after report files.
The historical `tests/upstream/results` directory is untouched. Preliminary
runs interrupted by rebuilding are inconclusive and are not used for these
statuses.

| Fixture basename | Before | After legacy / viaIR | Observations per mode |
| --- | --- | --- | --- |
| `exp_cleanup_nonzero_base.sol` | broken | working / working | 1 |
| `shift_left_larger_type.sol` | broken | working / working | 1 |
| `shift_overflow.sol` | broken | working / working | 5 |
| `shift_right_negative_literal.sol` | broken | working / working | 12 |
| `shift_right_negative_lvalue_assignment.sol` | broken | working / working | 12 |
| `shift_right_negative_lvalue_int16.sol` | broken | working / working | 12 |
| `shift_right_negative_lvalue_int32.sol` | broken | working / working | 12 |
| `shift_right_negative_lvalue_int8.sol` | broken | working / working | 12 |
| `shift_right_negative_lvalue.sol` | broken | working / working | 12 |
| `exp_literals_success.sol` | broken | working / working | 8 |
| `exp_neg.sol` | broken | working / working | 25 |

Every rerun used the complete snapshot path with `--filter`, `--batch-size 1`
and its own `.lake/upstream/group04-final-corpus/<basename>` output directory; no
execution or proof limit was raised. The runner's compiler SHA-256 is
`6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`.
The source archive SHA-256 remains
`9200f2a26b08be5b77faf877c44f5cfbf5ea95f1bccc45dae559d2fbc7cefb2d`.

Before model SHA-256: `c86945ed62a18ffccf0b72b291c6271f44462f7b1d60b101e73fd2ec565c8699`.
After model SHA-256: `6cf546e6a38a8770512372698b2d89d8dcb6588132c18ad093acc4e03fdcccfc`.

The eleven final runner invocations took 35.543 seconds in total (2.980–3.801
seconds each, including both modes and runner setup). The final source-control
file checked in 5.191 seconds, with maximum child RSS 848,136 KiB, with no
concurrent Lean build. These are measured costs, not a controlled speedup
comparison. `git log` records `1a7d5b0e` (one callee body elaborated/quoted once)
and `63ac4b63` (split elaboration); this patch preserves both designs.

Passed gates: archive verification (11,622 files), 14/14 runner regressions,
existing five Lean replay checks, final numeric source/kernel controls, exact
reference-solc controls, reachability (670 modules), layering (144 core modules,
zero frontend reachability), strict automation (491 automatic, 61 with budgets,
11 refuted, zero pending), and frozen TestSuite audit. Frozen SolKey
473da8944c sort checking passed (377 taclets, 131 read-bearing annotations).
The documentation-path checker retains its 13 pre-existing missing references.
Final broad gates passed: `lake build Solidity solkeycheck SolkeyTestSuite SolidityCorpus`
(692 jobs), then `./run-lean.sh` and the frozen corpus parity check without
`--update`. Long build logs, including nonfinal repair attempts, are retained
compressed under `tests/upstream/group04/logs`; their classifications and hashes
are in the validation record. The full decision example retained its original
proved/refuted and coverage pins. Its build took 1,228 seconds; the unchanged
array-decision example took 2,303 seconds. No proof limit was raised.

Corpus parity exposed two genuine improvements: the existing signed-base even
and odd concrete controls now have kernel proofs. Only their generated Lean
proofs, verdict records and scoreboard changed. Their pre-existing
`b = minusTwo` concretization notes remain; this adds no new concretization and
claims no general corpus-function theorem. The frozen source is untouched.
Corpus totals are now 72 proved, 35 unsupported and 101 unported outside the
TestSuite's 552 derived, 11 refuted, one excluded and two skipped obligations.

The implementation is saved locally on the task branch; no pushes or merges
were performed. All eleven final fixture reports were refreshed after the
corpus proof generation changed the model digest, retaining the same 224
observations. `tests/upstream/results` and the pinned archive remain unchanged.
