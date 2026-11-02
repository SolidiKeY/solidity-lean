# Assurance: trust gates, the certified memory compiler, closer extensions

The [full compiler roadmap](coverage-plan.md) requires these trust gates across
the completed source-to-executable-EVM proof closure. The compiler fragments and
premises recorded here describe existing results, not full-profile compiler
correctness. Named proof gaps cannot satisfy the roadmap's completion gate.

The work requested by the October 2026 audit: trust gates, the memory path
of the checked compiler, and bounded closer extensions.  Milestone labels
M1–M31 are cited elsewhere (e.g. M13 in `docs/semantic-gaps.md`).  The
core stays dependency-free.

## M1 · Trust gates and non-vacuity

* **Source gate**: `bash scripts/check-trust.sh` scans every Lean source
  (corpus, TestSuite, root modules, vendored LeanTeX) and rejects `sorry`,
  bare `admit`, native proof reduction and explicit axioms.  Comments and
  string text are blanked; ordinary, interpolated and literal-text views are
  combined conservatively.  It is a lint, not a Lean parser.  Tests:
  `node scripts/check-trust.test.mjs`.
* **Inventory**: `tests/trust-inventory.json` records every
  `implemented_by`, unsafe, opaque, error-recovery and kernel-option site
  by file, code and count; a changed or added site fails the gate.  It
  makes the boundary reviewable; it does not prove a compiled override
  implements its definition.  Known: the opaque cryptographic primitive is
  a model assumption, recursive thunk elaboration uses unsafe code, and
  error-recovery tactics can introduce a synthetic `sorry` while reporting
  an error.  None may reach an audited theorem.
* **Axiom gate**: `lake env lean --tstack=131072 TrustAudit.lean` follows
  the transitive axioms of the headline theorems (correctness, callbacks,
  symbolic execution, compilation, non-vacuity); anything but `propext`,
  `Classical.choice`, `Quot.sound` fails elaboration.  New public theorems
  are added to it.  CI runs both gates after the whole-library build.
* **Whole-library axiom gate**: `lake env lean --tstack=131072
  scripts/AxiomAudit.lean` (CI, after the build) reads every constant
  declared in a `Solidity` module that `import Solidity` reaches (the
  default library; not the `SolidityCorpus`/`SolkeyTestSuite` modules): a
  safe one may reach only `propext`,
  `Classical.choice`, `Quot.sound`; an `unsafe` (or `partial`) one may also
  reach `lcProof` only if listed by name in its `exemptUnsafe` (the six
  compiled memo/cache twins behind `@[implemented_by]`, through
  `unsafeCast`/`unsafeBaseIO`); a new one, or a stale exemption, fails.
  It replaces lean-action's `axiom-audit`, whose single allow list cannot
  exempt unsafe twins without exempting theorems too.
* Parser assertions are `#guard` checks, not `native_decide` proofs; parser
  correctness is not proved.
* **Non-vacuity**: `Examples/Tactics/Nonvacuity.lean` proves the result of
  `uint x = 7;` and refutes `x = 8` at an actual typed initial state; the
  false specification's translation has no derivation, and the run returns
  normally, so revert and exhaustion explain neither witness.

## The memory path of the checked compiler (M2–M4, M8–M12, M15–M18, M20–M31)

`Compiler.compile` (`Evm/Compiler.lean`) is the single checked entry: the
core compiler where `Evm.inFrag` applies, otherwise the memory compiler
(`Memory.compileProg`, `Evm/MemoryCompile.lean`).  The result keeps code and
fragment certificate together; `Main.compiler_checked` restates the public
agreement theorem (core state and stack on the core path; the full
heap/pointer relation on the memory path).

**Representation invariants** (each a premise of the public input):

* An array's length cell precedes its elements; one base per heap identity
  (`Evm/MemoryHeap.lean`), so aliases share a base and distinct objects have
  disjoint intervals above the reserved local frame.  Structs are one word
  per member, no header (`StructRepr`, `StructHeapRepr`); arrays and structs
  are cross-separated.
* Every memory local is initialized (unset declarations are not admitted).
  `RefFieldsRepr` records each reference-valued struct member's child
  identity and pointer word.
* Allocation is a bump allocator (`Evm/MemoryAlloc.lean`):
  `StructAllocatorRepr` owns every live interval below the cursor, a zeroed
  free tail represents the fresh object's defaults, and capacity is a
  theorem premise (the generated code has no runtime capacity check): each
  single-allocation lemma needs `cursor + size + 1 < 2^256`
  (`Evm/MemoryAlloc.lean`), and the public input `AllocationInput`
  (`Evm/MemoryGrowResult.lean`) states `cursor + cost < 2^256` over the cost
  a run reaches (`cost = 0` needs no capacity).  Allocation needs frame
  base `0 < b` (cell zero is otherwise a local); non-allocating programs may
  use base zero.
* The frame bound is the peak context anywhere in the program
  (`frameNeedProg`), not the final one: temporaries of either branch would
  otherwise overwrite heap cells.
* Allocation cost is computed from the typed source and the reached
  execution prefix, not the erased certificate: each reached allocation
  costs its length plus a header (arrays) or `max 1 memberCount` cells
  (structs; zero would bypass the allocator requirement); unreachable
  suffixes after a revert cost nothing, and the cost skips interpretation
  when a suffix has no allocation (proved equal).

**Admitted** (each with inhabited public input/agreement witnesses, exact
source and target reversion, and its theorems in the axiom gate):

| M | What compiles |
|---|---|
| M2 | primitive-array reads and writes through typed pointer locals, source operand order |
| M3 | lengths, primitive declarations and defaults, local assignment, alias declaration and rebinding, nested reads in indices and RHS |
| M4 | checked operators and short-circuit Booleans over memory operands, primitive storage writes, `require`, `revert` |
| M8–M11 | `new T[](n)` declarations and allocating rebinding of primitive arrays |
| M12 | scoped blocks and statement-level `if` (only the selected branch costs) |
| M15 | `delete xs[i]` (a default write) and `delete xs` (rebinding to a fresh empty array) |
| M16–M18 | the five compound operators, standalone and captured `++`/`--` on elements and locals (`i = xs[i]++` uses the old index) |
| M20–M22 | primitive struct fields: reads, writes, aliases, mixed struct/array ownership |
| M23 | primitive-member struct defaults and constructors, allocating literal rebinding |
| M24–M25 | field deletion, compound updates and bumps on fields; whole-local struct deletion (allocating) |
| M26 | `T[] memory xs;` defaults |
| M27–M28 | typed paths through reference-valued struct fields: nested reads, lengths, child aliases, direct primitive writes, deletion, compound updates |
| M29 | assigning an existing reference to a struct member (RHS before the parent path; no copy) |
| M30 | deleting a reference-valued member to a fresh primitive array or primitive-member struct |
| M31 | storage-root to memory copies of primitive-member structs, declarations and allocating rebinding |

**Rules learned.**  Open the public premises with `Compilation.memory_input`
instead of normalizing the whole compiler result (that ran past the
heartbeats and once past 16 GiB RSS); mark a large computed compiler-result
constant `irreducible` in a fixture (the kernel still checks it); split a
large target-observation certificate into smaller programs rather than
raising budgets; a recursive compiler the kernel must reduce keeps its
endpoint type variable for structural recursion (M27).

## Closer extensions

* **M5 · Quantified premises at later counters** (`Calculus/CloseAll.lean`):
  bounded `allLeft` after the closer opens its binders, so a later local or
  anonymised loop counter instantiates a premise stated before it existed;
  no term enters an older scope.  Each normalization, candidate, guard and
  replay step has heartbeat recovery and rollback; `sol_close_all?` prints
  the applications.  It does not infer invariants.
* **M6 · Nonlinear bounds** (`Calculus/CloseNonlin.lean`): solkey's
  `multiply_inEq0`, `multiply_2_inEq0`, `square_nonneg`,
  `add_non_neg_square`.  Budgets: 256 declarations, 8 192 expression nodes,
  16 products examined; at most four atoms, eight factors, twelve
  comparisons, 128 facts; target products seed the search first.
  `sol_close_nonlin?` prints the proof.  Checked instances, not a decision
  procedure.
* **M7 · Quantified ABI memory scans**: `CloseScoped` rewrites memory reads
  and lengths through local pushes and counter assignments of input arrays;
  the final constructor pass visits at most 128 constructors at 1 000
  heartbeats each; arithmetic is tried before reflexivity.  Fixtures
  `tests/solc/ArrayScans.sol` (invariants supplied); the two-assert signed
  diamond proves by `sol_symex; sol_close`, while its `sol_prove` walk still
  exceeds the declaration budget.
* **M13 · Demanded memory reads in loop proofs**: the scoped reducer applies
  the memory taclets when a read, length or identity read is formed, before
  later writes duplicate it (`foldMem2`, bounded by `normalizationSize`,
  kept only if no larger; `foldMem2_eval` keeps failed writes' guards).
  `binomialFaithfulRowsSmall` (`tests/solc/OpenLoops.sol`,
  `Examples/Tactics/OpenLoops.lean`) proves in about 7 s with no invariant
  or heartbeat override.
* **M19 · Bounded rigid branch pruning** (`Calculus/Rigid.lean`):
  literal-local branch conditions substituted backward through their
  updates (`Hyps.rigid`, `Hyps.rigid_lift`); `Seq.refuteLanded_sound` uses
  the surviving sibling's derivation.  Each substitution is checked against
  a 512-node cap first (repeated `x := x + x` would expand); a refused
  projection keeps both branches.

## M14 · Computed memory revert operands

`RevPart.mem` carries a typed memory local: reason operands use the
`Error(string)` encoding, raw operands return the buffer, an empty raw
buffer the empty revert (`Semantics/RevertMemory.lean`).  Computed
`revert(reason)` and `require(c, reason)` lower to it (require captures the
condition first and evaluates the reason even on success).  The solc
importer recognizes only the whole-buffer rethrow
`revert(add(data, 32), mload(data))` on a byte buffer; a bytes local is not
accepted as a string reason.  Open: `RevPart.pat?` returns `none` for
computed operands, so catch reasoning falls back to an arbitrary-byte
allocation (`catchDataBox`), not the exact callee-memory relation.

## Remaining requested work

| Area | Still due |
|---|---|
| Memory compiler | Other storage paths and copies (memory-to-storage, runtime-length arrays, reference-bearing structs), reference-bearing construction and defaults, fixed and reference-element arrays and paths, nested loop bodies, remaining mixed operations. Finite-body memory loops, including enclosing blocks/branches, have typed reached-prefix capacity certificates and public simulation (`docs/compiler-verification.md`, Checked memory loops). The core path compiles loops (`Instr.loop`, `loop_sim`). |
| Loop automation | Two `SolcLoopsOpen` functions (`docs/semantic-gaps.md`, `docs/loops.md`). Support sound invariant use where missing; keep a missing invariant distinct from a false specification. |
| Quantifier instantiation | Broaden ground terms and larger loops only with bounded, checked instances. |
| Arithmetic | Broader nonlinear coverage stays outside the exact verifier's fragment (`docs/automation.md`, M6 decisions). |
| Revert semantics | Exact symbolic catch relationships; literal data outside self-call frames; broader panic-code alignment (self-calls already fail with solc's `Panic` codes, `Prog.withPanics`). |
| Exact verification | `docs/automation.md`, M7 "What is not proved". |
| Source semantics | The ledger's remaining gaps and the whole-program progress theorem (`docs/feature-work/source-soundness.md`; `abi.decode` at the decoder's types and `calldata` references to `bytes`/`string`/one-word arrays, tuple declarations (no progress theorem), inline arrays of one-word elements, `new T[](n)` and `try`/`catch` with one plain or `bytes memory` clause (no arm theorem) added by lane FU2-B, with arm theorems for locals only, `Solidity/Source/Decode.lean`, `Solidity/Source/Calldata.lean`). |


Memory-loop compiler follow-up: the full original 24-module Derived17 workload
now passes its unchanged cumulative 300-second gate (262.03 s in the original
worktree; all group outputs fresh). Scoped compiler simulations, inhabited
allocation/divergence/drop controls and actual four-mode upstream executions
pass their dedicated checks. The final full-repository `./run-lean.sh` confirmation passed (377.01 s),
including the pinned TestSuite and SolKey annotation checks.
Historical timing/resource failures and the unchanged documentation-path debt
remain explicit; sampled EVM observations do not promote source coverage.

### CI regression step after the audit fix (lane FU1, 2026-11-01)

With the whole-library axiom gate passing (workflow run 41339114510 on
master `457130f3` + the audit commit only: Build, "Audit every declaration's
axioms", "Audit headline theorem dependencies" and the editor and bridge
jobs passed), CI reached "Test source verification and regression suites"
for the first time since about 2026-10-29: 62 pass, 9 fail in
`scripts/test-solidity.test.mjs`. All nine are on master (the run carries no
other change); the last green run is 2026-10-20 (`292a4681`), 1320 commits
earlier, so a bisection (about 11 full rebuilds of 45–70 min on the lane's
VM) did not fit. Seven were reproduced locally on the lane's tree with
`SOLKEY_ROOT`, `LEAN_NUM_THREADS=1` and solc 0.8.34 as CI sets them
(`node --test --test-name-pattern=… scripts/test-solidity.test.mjs`, 25 min);
the first failing row of each:

| # | Test | First failing row | Evidence |
|---|---|---|---|
| 30 | bytesN, bytes and string | `indexOutOfRange`: pending, expected proved | proof search |
| 31 | calldata | `localAlias`: unsupported, "a calldata slice ordinary alias without a known calldata origin" (`Syntax/Elab/Context.lean`, `sliceStmts`, since `c31e76b6`) | the import prints `function «localAlias»(uint[] calldata «xs») { uint[] calldata «ys» = «xs»; … }`; the same text in `contract!{}` elaborates, so the import's path loses the calldata roots (`Syntax/Contract.lean` `calldataRoots`) — not the `roMentions` refusal of `099bfbe1` |
| 40 | full frozen TestSuite function table | "maximum recursion depth has been reached", compiler IR check failures at `SolTests.TestSuite._list._lam_0`, then `(interpreter) unknown declaration 'SolTests.TestSuite.report'` | CI log only |
| 42 | quantified consequents / omitted bodies | `omittedModifier`: excluded, expected unsupported | `excluded` is a documented gap status (`docs/solidity-testing.md`); which change moved the row is not identified |
| 43 | specification parameter renaming | `tryScopeExit`: pending, expected proved | proof search; fixed in lane FU2-A (below) |
| 44 | unsupported ledger frames | `ledgerGap`: "solidity.specificationSyntax: <input>:1:14: expected ';'" instead of "ledger locations in assignable" | the specification parser now rejects the clause before the ledger check |
| 45 | constant specifications | `quantifiedShadow`: pending, expected unsupported | admission changed: a refusal became an open obligation |
| 57 | solkey solc/open ports | `tryArgumentSideEffect`: pending, expected proved | CI log only |
| 60 | revert data | `reasonBytes`: pending, expected proved | proof search |

None is in the lane's files (the reproduction includes the lane's changes,
and CI showed the same failures without them).

**Fixed afterwards (lane FU1, separate commits):**

* **31** (`974dd1de`): the import elaborates each obligation body through
  `sol_raw!`, whose slice pass had no calldata roots, while `contract!{}`
  passes the function's `calldata` parameters (`calldataRoots`); since the
  origin check of `c31e76b6` that refused `uint[] calldata ys = xs`.
  `sol_raw_calldata!` (`Frontend/Import.lean`) passes the roots and keeps
  the parameter declarations (`uint[] memory xs;`, which would shadow the
  root) outside the pass. `localAlias` elaborates; the `roMentions` refusal
  of `099bfbe1` is untouched. The test then stops at `sliceRead`,
  `sliceOfSlice`, `slicePast`: pending, "open proof goals" (below).
  **Reverted at integration (2026-11-02):** the roots also admit named-argument
  reverts with a calldata array (`uint[] calldata solcErrorCaptureN = v`,
  `SolcJson/Body.lean`), which `tests/upstream/AggregateErrorControls.lean`
  and `AggregateErrorBoundary.lean` pin as refused ("without a known calldata
  origin"), with no replay evidence for the admitted path; and test 31 still
  fails on its slice rows. Master keeps the refusal; reapply together with
  replayed error-encoding vectors and updated pins.
* **44** (`a48fd85f`): in the testing import a specification that does not
  parse became a `solidity.specificationSyntax` scope rejection, raised
  before the named refusal "ledger locations in assignable clauses are not
  modelled"; a ledger `assignable` clause (`net(msg.sender)`) now keeps that
  refusal.
* **42, 45** (`5630c5fd`, stale expectations against documented
  classifications): the first failing row of 42 is `omittedModifier` (its
  modifier's general Yul, the S00 exclusion `solidity.inlineAssembly`,
  reported as `excluded`, a gap like `unsupported` per
  `docs/solidity-testing.md`); `quantifiedShadow` in 45 (`\forall uint COUNT;
  COUNT == 2` beside a constant `COUNT = 2`) is read with the quantifier
  binding `COUNT` (scoped specifications), so the false claim stays
  `pending` and is never proved through the constant.
* **40** (`9ff01fd7`): the testing import compiled a contract's
  source-declaration table as one list literal, nesting as deep as it is
  long; solkey's `TestSuite.sol` exceeded the default recursion depth. The
  table is defined in chunks of 64. The test passes locally (3m46s); it was
  not run locally without the change.

Rerun of the nine on the lane head (`9ff01fd7` + this record, 22:40 UTC):
40, 42, 44, 45 pass; 30, 31, 43, 57, 60 fail on their first `pending` row
(`indexOutOfRange`, `sliceRead`, `tryScopeExit`, `tryArgumentSideEffect`,
`reasonBytes`). The full gate after these fixes: default 1041 jobs and
TestSuite 286 jobs built, solkeycheck at its baseline 37.

**Lane FU2-A (2026-11-02), rows 43 and 57: fixed / passing.** With the
pinned soljson installed (`SOLKEY_ROOT`, `LEAN_NUM_THREADS=1`), the CLI goal
dump of `SpecBindings.tryScopeExit` (`inspect … --show goals`) showed one open
`ProvesC` leaf: the loop's preservation goal in the `try` success clause,
valid and closed by `ProvesC.plain` then `sol_leaf`/`sol_close`. The callback
walk never tried `plain` there: `CallbackWalk.movesAt` skips it wherever the
goal mentions `Stmt.tryCall` (7a6120d's guard against an ordinary-proof
attempt on every capture before a `try`), and the body's end
`Fml.invPost m hu ω κ φ post B`, with no break test (`B` reducing to `none`),
still carries the enclosing `try` in its unread continuation `⟨ ω κ ⟩ φ`,
although it is `post` alone. `CallbackWalk.liveFml` drops that continuation
before the scan; a break test keeps it. No rule, closer or soundness change:
`plain` still checks `callsBack = false` by `rfl`. FU2-D's unreduced
`Val.wk … .lower` terms were the leaf's printing (escapes), not the cause;
the `dsimp` tried on them was not needed and is not kept. Regression:
`TryCatch.scopeExitKeepsAge` (the same function in `contract!{}`, binder `a`;
the row's specification, `Panic` loop and shadowing `age` go through the
import only). `node --test --test-name-pattern="specification parameter
renaming|solc/open self-calls" scripts/test-solidity.test.mjs`: 2 pass (43
and 57). Reviews: the guard is narrowed only under a body's end without a
break test (7a6120d's speed motivation otherwise kept; an earlier draft also
ignored `Hyps.freshC` indices and was dropped as unneeded); only the first
such end is inspected, which can keep `plain` skipped where it could run,
never the reverse; full build and SolkeyTestSuite green.

**Open: proof automation** (31's slice rows; 30 and 60 fixed by lane FU2-D, 43 and 57 pass since lane FU2-A), each "open
proof goals" in a `box` obligation. For `sliceRead` (`t = xs[1:]; assert(t[k]
== xs[1 + k])`) the CLI's goal dump (`action: inspect`, `show: goals`) leaves
`read(memory, base[(k < len - 1 ? 1 + k : len)]) == read(memory, xs[1 + k])`
without the bounds facts that would close it or make the read revert: a
closer gap, not an admission change. For `indexOutOfRange` (`bytes4 b =
"abcd"; bytes1 x = b[i];` with `i >= 4`, expected to revert) the leaf keeps
`b[i]`'s lowering `((b >> 8 * (3 - i)) % 256) / (i < 4 ? 1 : 0)` as a plain
update `se3 := se4 / se8` and ends at `false = true`: the zero divisor's
revert branch is not taken by the search (the leaf also prints raw `‹Tm…›`
escapes for `subW`/`mulW`, a printer gap). Not bisected (see above).

### Lane FU2-D (fu2-20261102): the five rows diagnosed, 30 and 60 fixed

Bisecting by rebuilding is not affordable here (each step is a 45–70 min
full rebuild; the last green CI run, `292a4681`, is about 1,300 commits back).
Instead each row's first open goal was reproduced with the CLI goal dump
(`node scripts/solidity-lean.mjs inspect FILE --function F --show goals
--no-build`, `SOLKEY_ROOT` set) and its cause traced to the commit that
introduced it, from the history of the code it names (`git log -S`).

| # | Row | Cause | First failing commit | Owner | State |
|---|---|---|---|---|---|
| 30 | `indexOutOfRange` | `bytesAt` (`Syntax/Elab/Values.lean`) lowered `b[i]` of a `bytesN` at a symbolic index to `uint8(((b >> 8 *% ((N-1) -% i)) % 256) / (i < N ? 1 : 0))`. The walk keeps the division as an update; behind the symbolic shift the closer does not refute it: in a scratch reproduction `sol_close_eval` times out on the leaf, while the same zero divisor without the shift closes. A missing reading, not a refactor. | not identified: the function was added in `4dd2d9d0` and its row in `f9a1cf42` (2026-10-20, both after the last green CI run), asserting `proved`, so it presumably closed when written; the lowering is `1789394d`'s, unchanged since (`63ac4b63` only moved it), so a later closer or walk change stopped it closing, not identified without rebuilds | FU2-D | fixed: `#bytesIndex` (below) |
| 31 | `sliceRead` | see "Open: proof automation" above | — | `fu2-calldata-access` | not this lane's |
| 43 | `tryScopeExit` | still pending on the lane head. Its open goals are the loop invariants inside the `try`'s success clause (`age >= 0 && i <= 1`, `age` the `returns (uint age)` binder): they reach the leaf as unreduced `(Val.wk (Thin.keepAll …) v).lower` terms (printed as `‹…›` escapes), which the closer does not evaluate, so even `se3 < 1 ⟹ se3 + 1 <= 1` stays open. A binder weakening in the try's frame, not a closer rule. | not identified (the row is in the last green run, `1f02521b`) | `fu2-frame-returns` | handed over |

| 57 | `tryArgumentSideEffect` | proved on the lane head with the test's `--self-address 0x…DeaDBeef` (every row of that test passes, `trySuccessKeepsStorageUnsound` and `callKeepsStorageUnsound` pending as pinned). Its callee has no literal reason and no `bytesN` index, so this lane's changes do not reach it: most likely fixed on master before the base, plausibly by `48db830` (the revert of the calldata-root import change that FU1's run carried). | not identified | `fu2-frame-returns` | passes here; not rerun at the base |
| 60 | `reasonBytes` (also `reasonOfBranch`, `reasonPastCustom`) | `ea06b814` ("Solidity features", 2026-10-26) made the solc import print every string literal that has a `hexValue` as `hex"…"` (`byteLiteralText`, `SolcJson/Body.lean`), where it printed the quoted `value` before. `require(false, "boom")` then parses as `requireReason` (a reason expression) instead of `requireMsg`, so the self-call's callee reverts with the reason in a fresh memory `bytes` (`revertData [.mem …]`); `CatchKind.datas` knows no data of a memory part, and `catchDataStep` binds the reason as any bytes (`Fml.allocAll`). A refactor regression, inferred from `ea06b814`'s diff (not rebuilt at `ea06b814^`; nothing else in it touches the require/revert path). The test (`75dc97b4`, `aa47a432`, 2026-10-21) is after the last green CI run, so it never ran green in CI; it asserted `proved` when written. | `ea06b814` (inferred) | FU2-D | fixed: literal reasons (below) |

Not a cause: every self-call `try` is read under the callback reading
(`Fml.callsBack` is `true` for any `tryCall`, since `1a10f08b`); this is as
designed, and the rows close under it once the data is literal.

**Row 30, `#bytesIndex`.** A symbolic index of a `bytesN` is now
`uint8(#bytesIndex(b, i, N))`, which `hoist` (`Syntax/Elab/Arms.lean`) reads
as `b` and `i` held in fresh locals, `require(se < N);` (in a self-call's
callee, or a frame that keeps failure data, `Panic(0x32)`'s data, the code
of an array index, `Checked.idxPG`; the old divisor panicked with `0x12`),
then the byte `(b >> 8 *% ((N-1) -% se)) % 256`. The `require` rule's
branches are KeY's `inBounds`/`outOfBounds` (`docs/lean-key-rule-map.md`); no
calculus rule was added. A literal index is unchanged (checked by the
elaborator). The printer gap is closed: `dl{}`/`tm{}` print and read `+%`,
`-%`, `*%`, `>>`, `<<` at `uint` (`Calculus/RuleSyntax/{Grammar,Schemas,Print}.lean`,
`Calculus/SurfaceNotation.lean`), so the leaf has no `‹Tm…›` escape.

**Row 60, literal reasons.** `revertReason`/`requireReason` of a literal
(`"m"` or `hex"…"`, `RawExpr.bytesLit?`) is elaborated as `Error(string)`'s
literal data (`revertData [.bytes (encodeError bytes)]`), nothing allocated,
in every frame, as the memory reason carried its data in every frame
(`memoryRevert`); `requireReason c m` is `if (c) {} else { revert … }`. The
callee's data is literal again, `CatchKind.datas` lists it, and the `catch`
reads the reason. Pinned by `Examples/Tactics/ComputedRevert.lean`
(`unicode_hex_reason_exact`, unchanged) and the RevertData rows.

**Results on the lane head** (`runSolidityTests`, `SOLKEY_ROOT` and
`LEAN_NUM_THREADS=1` as CI sets them): `tests/solc/Bytes.sol` every row proved
(`indexOutOfRange` included); `tests/solc/RevertData.sol` every row proved
(before: `reasonBytes`, `reasonOfBranch`, `reasonPastCustom` pending);
`SolcPaymentsOpen.sol` (row 57) as pinned; `SpecBindings.sol` (row 43) all
as pinned but `tryScopeExit`.

**Reviews** (read-only finder and skeptic, no Lean server). Confirmed and
fixed: the record above now says that rows 30 and 60 never ran green in CI
and that `ea06b814` is inferred; `docs/semantic-gaps.md` ("Revert data") now
says that a byte-literal reason carries its data in every frame while a
quoted `"m"` keeps the empty-data lowering outside a self-call (one source,
two readings, differing only in data no modality reads; the existing pin
`unicode_hex_reason_exact` needs the former); under `pp.sol.pushArithmetic`
an `int` shift printed as `>>` would read back as the `uint` one, so the
shifts and wrapping operators now print only at `uint`
(`Calculus/PrintTerm.lean`). Not confirmed: a flat struct with an enum member
decoding unchecked in `sol{}` — the struct table has no `#enum` row
(`StructEnc.valueRowsOf`), so the member is a plain `uint` either way (the
recorded limitation). Recorded, not changed: enum-typed mapping keys of a
public getter get no `paramEnums`.

**Gates on the lane head.** `./run-lean.sh` (69m32s): default target 1041
jobs and `SolkeyTestSuite` 286 jobs built, solkeycheck at its baseline 37.
Lean server clean on `TrustAudit.lean` and `scripts/AxiomAudit.lean`; no new
`sorry`, axiom, `native_decide`, `implemented_by` or heartbeat change, and no
new headline theorem (no pin added). Node: `test-solidity.test.mjs` tests for
rows 30, 57 and 60 and the new `EnumArrayDecode` pin pass, row 43's fails on
`tryScopeExit` (above); `finite-dispatch.test.mjs` 34/34;
`solidity-upstream.test.mjs` 25/25; `check-g07` at its baselines (axiom-pin
drift, `check-doc-paths` 48); `check-automatic --strict` 491 / 61 / 11
refuted / 0 pending; `roadmap-g03-ledger.py --check` clean after `--write`
and its `abiDecode` sentence updated. Elaboration of the touched modules did
not slow (`Syntax/Elab/Arms` 130 s → 89 s, `Examples/Tactics/Bytes` 105 s →
108 s, `RevertData` 206 s → 232 s, within run-to-run noise); the core edits
(`Calculus/RuleSyntax`, `Calculus/PrintTerm`) are syntax and printer rows,
undoing no speed-motivated change.
