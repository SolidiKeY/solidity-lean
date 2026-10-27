# SolKey migration

How this package follows solkey upstream: the frozen inputs, the tooling that
re-pins them, the decisions the migrations made that are still in force, and
the parity gaps that remain.

**The pin is solkey `473da8944c`** (`tests/migration/solkey.pin.json`, the
snapshot in `tests/migration/solkey`). At it `Calculus/KeyTaclets.lean`
lists 377 program taclets, `RuleShapes.unclaimedTaclets` gives a reason for
each one the rule table does not claim, `migrationPendingTaclets` is empty,
and `solkeycheck` is at zero (131 read-bearing annotations). The TestSuite
fixture is imported from the same snapshot (`docs/testsuite-proofs.md`;
`TestSuite/Report.lean` has the counts). Upstream has moved on since:
`git -C ../solkey log 473da8944c..` is the next delta.

## The snapshot

The snapshot holds the tracked Solidity and `.key` examples, the core `.key`
test fixtures and their Solidity input, the rule resources, and the
compiler's Gradle pin. `snapshot.json` pins each file's SHA-256 and the
upstream commit; `solkey.pin.json` pins the manifest's hash. The compiler
binary (soljson 0.8.34) stays outside the package and is checked against the
snapshot's Gradle SHA-256. No package dependency is added.

Snapshots are immutable: re-importing the same revision verifies and reuses
it, and the tool refuses a destination that pins another revision or is not
empty, or whose file scope changed. Everything downstream reads the snapshot,
not `../solkey`: the taclet inventory, the sort check, the solc fixtures'
source and commit, `solkey-port.mjs` and the baseline runner.

## Re-pinning to a newer solkey

One reviewable change; do the steps in this order.

1. **The rule delta.**
   `node scripts/solkey-migration.mjs rules ../solkey <old> <new> > tests/migration/rule-delta-<new>.json`
   records added, removed and changed rule bodies (deleted rule files
   included; comments ignored, string contents and branch labels kept
   verbatim). Every added or changed program taclet gets a `Taclet`
   constructor of the same name (`.claude/rules/rule-table.md`), a merge
   recorded in `RuleShapes`, or an `unclaimedTaclets` entry with its reason;
   each gets a row in `docs/lean-key-rule-map.md`. Non-program theory
   (`structRules.key`, `memoryRules.key` lemmas) is ported as closer clauses
   or recorded as subsumed by the typed state.
2. **The snapshot.** Replace `tests/migration/solkey` and its `.pin.json`:
   `node scripts/solkey-migration.mjs snapshot ../solkey <new> tests/migration/solkey`,
   then `node scripts/solkey-migration.mjs verify tests/migration/solkey`.
3. **The inventory.** `node scripts/solkey-migration.mjs generate-taclets`
   regenerates `Calculus/KeyTaclets.lean`. It is imported by
   `Calculus/RuleKit.lean`, so this rebuilds the rule table and everything
   above it. Re-partition `RuleShapes.taclets_partitioned` (claimed,
   `unclaimedTaclets`, `migrationPendingTaclets`).
4. **The sorts.** Update `SortCheck/Annotations.lean` until
   `./scripts/check-solkey.sh --key <rules>` reports zero, `<rules>` the
   snapshot's
   `keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key`. The script deletes the
   built checker before building it: Lake 4.24 restores a cached executable
   only when the destination is absent, so a stale one could otherwise run.
5. **The fixtures.** Re-import `TestSuite.sol` and the other solc fixtures
   from the new snapshot (`node scripts/solc-ast.mjs --solkey tests/migration/solkey --soljson <dir>`;
   `docs/testsuite-proofs.md`, "The pipeline"), re-pin `Report.lean`, and
   derive or refute the new obligations.
6. **The corpus.** `./scripts/check-corpus.sh --update`, then
   `./scripts/check-testsuite.sh --solkey tests/migration/solkey/keyext.solidity.examples`.
   `docs/corpus-parity.md` is regenerated, never edited.
7. **The feedback.** Re-check `docs/solkey-feedback.md`'s items against the
   new snapshot.
8. `./run-lean.sh` and the gates of `AGENTS.md`.

## The source baseline

The runner proves every imported function of every snapshot source and
compares the outcomes with an expectation manifest:

```sh
lake build Solidity.Frontend.Testing
node scripts/solkey-migration.mjs baseline tests/migration/solkey /tmp/listing.json ../solkey/keyext.solidity.core/build/soljson listing
node scripts/solkey-migration.mjs expectations tests/migration/solkey /tmp/listing.json tests/migration/expectations.json
node scripts/solkey-migration.mjs baseline tests/migration/solkey /tmp/proofs.json ../solkey/keyext.solidity.core/build/soljson proof
node scripts/solkey-migration.mjs compare tests/migration/expectations.json /tmp/proofs.json
node scripts/solkey-migration.mjs summary /tmp/proofs.json
```

- Reports checkpoint after each source and proof batch. Large contracts run
  in batches of 32 rows, each under the normal subprocess limit; a failed
  batch keeps its results and marks the rest unattempted. The Lean command
  takes `from N count K`; the JavaScript API `batchSize`. Process errors
  carry exit code, signal and timeout.
- Expectations target a proof for the positive suites and a proof-open
  result for upstream's `open` and `unprovable` directories. Proof-open means
  the prover did not close the obligation, not that it is false. Timeouts and
  process errors always fail; `illegal/nocompile` sources need an actual
  compiler diagnostic (`compileRejected`). Unsupported imports are migration
  failures, not accepted baselines.
- Comparison rejects a wrong commit or mode, incomplete source coverage,
  missing, duplicate or unexpected rows, changed outcomes and errors; an
  empty expectation set cannot pass. Updating the expectations is a
  reviewable change, never an acceptance of observed failures.
- **Expected-open is not falsity.** Some upstream-open rows prove in Lean
  for a stated reason: checked arithmetic reverts before `assert(false)` (the
  seven `unprovable/Unprovable.sol` boxes), bounded values and truncating
  casts, better lowering. Others prove only under the no-callback reading
  (`trySuccessKeepsStorageUnsound`, `callKeepsStorageUnsound`,
  `tryArgumentSideEffect`) and stay callback-compatibility gaps. A
  source-derived expectation policy must tell the two apart, not whitelist
  observed statuses.

The last uniform audit (`tests/migration/proof-2026-10-16.json`, its
`.summary.json`, `.implementation.json` and `comparison-2026-10-16.json`)
ran at `048a74de51`, before the binding, negation and `473da8944c` changes;
it fails strict comparison and does not describe the current tree. No
uniform audit has run at `473da8944c`. The other JSON files in
`tests/migration/` are older checkpoints.

## Decisions in force

- **Push semantics.** Since `d85018517f` every empty push saves only the
  length (`save(storage, sp.length, sp.length + 1)`, no `delAt` of the
  appended slot), so a slot past the end is exposed as it is: no clean-tail
  invariant in general. `pushSlot` (`Semantics/Storage/Ops.lean`) keeps a reference slot as it is (a
  primitive slot past the end is the default on every `wt` storage); the rule
  text and printer use upstream's length save. A claim about the pushed row
  is false from a storage with a dirty tail: TestSuite's seven
  `SYMBOLIC_TAIL_OPENS` obligations are refuted (`TestSuite/Refuted.lean`),
  as they stay open upstream. A contract that exposes nothing keeps clean
  tails (`ReachableBy.cleanTail`, `docs/options.md` O6), and the source
  runner states its obligations under `cleanTail(storage)` (`reading:
  clean`). A reference-element push exposes an old slot, so the concrete
  admission tier does not count it (`Op2.exposes`).
- **Read bounds** (`Calculus/ReadBounds.lean`). The closer and
  `LTm.literalRead` admit 24,000 nodes and 12 storage updates; where every
  storage history is concrete (`LTm.known?`: literal paths below a root
  deleted earlier, or `mtSt`, no `pop`/`shrink`/`extend`), 96,000 and 40.
  Measured first: on an undeleted `uint[][]` eliminating `len` through 1–4
  pushes grows 160, 994, 11,612, 279,608 characters, so the low bound stays
  for symbolic histories. A checked index whose check reads literally `true`
  is lowered as the plain `q[i]` (`foldAt`, `Calculus/DecideScoped.lean`);
  without that one `uint[][]` leaf had 908,084 nodes. `literalRead` checks
  the bounds before eliminating and keeps only a literal result.
- **Heartbeats per leaf.** An obligation whose leaves each close but together
  pass one declaration's `maxHeartbeats` is declared by `sol_auto_theorem`
  (`Calculus/Closers.lean`; `TestSuite/Derived20.lean`: `bitAndSymbolic`
  needs about 400k, `invariantForBreakSkipsUpdate` 270k, against 200k).
  `check-testsuite.sh` refuses a `maxHeartbeats` in the TestSuite.
- **Memory reads through a storage copy** below its root: the memory closer
  reads a copy's objects (`copyObjN`, `copyPathRd?`,
  `Theory/Typed/MemMirror.lean`) and takes a read's guards out of its
  address (`LTm.hoistA`); `TestSuite/Derived21.lean`.
- **Parallel push exhaustion.** `pushLocalExhL` reads a storage push paired
  with a local binding (an alias-returning push), the binding's right side
  required to return in the original state: model-specific resource
  handling, not an upstream taclet (`Examples/ProofTree.lean`'s `pushAlias`).
- **Automatic loop unwinding.** An unannotated loop is `LoopAnn.auto` and the
  literal upstream `whileUnwind`; an explicit `unwind 0` selects Lean's
  `loopExit` (`Taclet.not_unwindZero`). `sol_prove` tries increasing walk
  budgets up to 20,000 steps (52,640 nodes over all stages); `sol_prove?`
  writes the chosen one as `sol_prove (steps := n)`. `sol_symex` still needs
  an explicit bound or invariant. The loop rules are a restricted
  transcription: capture-free conditions, conservative frames, unsigned
  variants defined wherever the invariant holds (`docs/loops.md`).
- **Lean-only rules**, excluded from the SolKey fragment (`Stmt.inSolkey`)
  and the EVM compiler: the complex-receiver push captures, `addmod`/`mulmod`
  assignments, `storageFixedCopySave`/`pushFixedCopySave` (KeY's `Struct`
  erases the outer types Lean must convert). Each is a `LeanTaclet` with a
  rule-map row.
- **Large import tables** are compiled in segments of at most 64 cells, a
  whole-contract `Eq.refl` checked before the contract is defined: the real
  TestSuite literal exceeded the code generator's recursion depth. Scoped
  programs stay uncompiled (an import-speed decision). The generated
  `Corpus/TestSuite.lean` sets the smallest `maxRecDepth` that passes.
- **Specification import.** solkey ignores `assignable` (accepted, no frame);
  Lean's storage frame is a stronger extension, and a function with
  `assignable net(…)` is refused with its callers. solkey assumes
  `msg.sender != this` for a specified obligation; Lean does not (its
  obligations cover those states too). An invalid clause refuses its own
  body only; a refused modifier refuses its users.

## Remaining parity gaps

What the migrations left open, by kind. Each needs its execution meaning and
a kernel-checked rule agreement before integration; do not replace one by
parser lowering or accept an unsupported positive test.

- **No current audit**: a uniform listing, proof run and strict comparison
  at `473da8944c`.
- **Nested arrays** (`contracts/Array*`, open at 2026-10-17; re-run them
  since `Derived21`): copies between storage and memory read below the first
  level, default-allocated nested fixed memory arrays (the inner rows a
  declaration allocates, `initIdentity`), `pop` then `push` (excluded from
  concrete histories by design; needs a read past the live end that does not
  branch), suites that start `delete a; a.push()` (rows of unknown length
  since the length-only push; upstream needs an empty-inner precondition),
  element-type-changing copies.
- **Frontend**: calldata; effectful conditional and short-circuit calls;
  arbitrary struct layouts (`DocsBallot.Voter`); recursive structs (one
  through a mapping is excluded); recursive helper calls; immutables, narrow
  aliases and runtime casts into enums; signed powers; signed literal
  conditionals, literal conditionals nested in a branch or short-circuit
  right side (a conditional's narrow width is kept only when both arms are
  compile-time constants); unchecked push arithmetic and the value of a push
  suffix `++`/`--`; conditional reference arguments containing calls;
  duplicate storage-root names under inheritance; imports and remappings
  (the compiler helper is single-source).
- **Specifications**: ledger `assignable` frames; `\old` of memory contents
  and of calldata parameters; `assignable` rooted at a reference parameter;
  enum names and constants inside quantified or escaped clauses (kept
  verbatim); typed constant casts in loop invariants; a `\forall` clause of a
  function whose locals the import renames; comment-separated call heads.
- **Proofs**: Purchase's `abort` (its `sol_spec_prep` first `sol_close_eval`
  exhausts 200000 heartbeats in about 8 s of simplification; disabling
  definitional simplification, early rewrites, a landed-state congruence
  lemma, an opaque contract constant and an Option-native weakest
  precondition were tried and do not fix the pipeline: do not repeat them or
  raise the limit); Escrow's proof preparation; SendingEther's payments;
  `ReferenceParameters`' larger copy sequence; the inheritance diamond
  constructor's symbolic closure.
- **Callbacks and frames**: the upstream-open payment examples above need the
  callback reading; function-contract frames exclude push, pop and the
  mutating call-receiver forms.
- **Left as they are** (refusals or weaker rules, never wrong programs): a
  conditional with effects in a branch takes its capture's type from the
  non-literal branch, not solc's common type; the loop `break` flag is not
  printed, so a re-read printed lowered loop has no break test.
