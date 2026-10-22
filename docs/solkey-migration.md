# SolKey migration

The migration targets committed SolKey `048a74de51a7cfb2cf497a043658424098f91e8e`
(2026-10-15), starting from corpus pin `1b4341a303`. Local uncommitted SolKey
changes are not part of this target. The migration is in progress; importing
sources and enumerating names does not implement the missing rules.

## Paused handoff — 2026-10-16

Stop at the specification/parser binding milestone below, as requested by
the user. Full migration is **not complete**. The original request was to
port roughly one week of SolKey updates; subsequent work expanded into broad
source parity, which exceeded the requested eight-hour window. Resume only
on the user's instruction, with that scope distinction made explicit.

The current checkpoint supports renamed specification parameters and named
returns, including quantified shadows, `\old`, assignable indices and
lexically scoped loop annotations. The local 37-row binding fixture has 25
kernel-checked proofs, nine deliberately open negative checks, two expected
unsupported cases and one internal helper, with no process errors. Default
and TestSuite builds pass; the frozen sort, corpus and trust gates are recorded
in the milestone below. All 42 JavaScript test groups are covered by the full
run plus the corrected targeted rerun, with no implementation change between
them; the exact validation scope is recorded below.
All changes remain uncommitted; preserve the existing working-tree edits.

Next work, when explicitly resumed:

1. Re-establish the **weekly update** boundary from `tests/migration/rule-delta.json`
   and the two pinned commits. Separate changed/new taclets and their required
   regressions from older whole-repository gaps. The 345-name inventory and
   zero sort disagreements do not prove complete semantic coverage.
2. Run focused upstream checks of ERC20 `mint`/`burn` and other obligations
   previously refused solely for renamed specifications. This milestone's
   new report covers a local regression fixture; it is not a new upstream audit.
3. Address remaining gaps needed by that weekly delta. Current broader gaps
   include nested fixed-array copy conversions, arbitrary struct layouts,
   ledger `assignable` frames, quantified loop invariants, calldata and
   effectful conditional/short-circuit calls. Each requires its execution
   meaning and kernel-checked rule agreement before broad integration; do not
   replace them with parser lowering or accept unsupported positive tests.
4. Profile proof preparation only for required blocked examples. Purchase's
   first `sol_close_eval` exhausts the existing budget. The investigation at
   the end of this document records rejected prototypes; none was integrated.
   Do not repeat them or raise heartbeat limits to hide the problem.
5. Once the scoped changes pass targeted gates, run a fresh listing/proof
   audit and strict comparison. The saved 112-source audit predates the
   negation and binding compiler fixes. Its counts must not be presented as
   validation of the current implementation.

## Resumed — 2026-10-17

**Scope.** The target stays the weekly update `1b4341a303..048a74de51`
(25 SolKey commits). It has two parts: the rule delta in
`tests/migration/rule-delta.json`, and 79 added or modified Solidity
sources. Those sources are almost the whole 112-source audit (950 of the
1,032 proved rows, 140 of the 162 pending), so "weekly delta" and "source
parity" largely coincide; the distinction that remains is that pre-existing
whole-repository gaps (calldata, short-circuit calls, recursive structs) are
in scope only where a weekly source needs them. Upstream has moved seven
commits past the pin (`473da8944c`, 2026-10-16); they are out of scope
until a repin.

**Step 1, the rule delta, is complete at the rule level.** All 22 added and
7 changed program taclets have rule-map rows: 21 are `Taclet` constructors
of the same name, and `newArrayCaptureStorageRoot` is merged into
`newArrayCapture` (`RuleShapes`). The
changes are: `noFixedArrayElement` dropped from the delete and `storagePopSave`
taclets (Lean never had it; the rule-map note is updated), the appended slot
reset (`delAt(…, sp[sp.length])`) in `storageLocalRootPushBind` and
`storagePushLengthSaveReferenceElement` (both already Lean's form), and
`nonMappingElement` added to `storagePushLengthSaveReferenceElement`
(the mapping-element case is `storagePushLengthSaveMappingElement`). The
`structRules.key`/`memoryRules.key` delta (`wf*`, `fixed*`, `selectOnShape*`,
`selectStDelNode{Element,Member,Size}`, `shapeAtSize`, `sizeOfMap`) is the
shape/well-formedness theory of an untyped storage; the rule map records it
as subsumed by the typed `Storage C`. The 12 new `proofs/*.key` files prove
those lemmas in KeY and have no Lean counterpart to check.

**Step 2, renamed specifications upstream.** Run through the testing entry
point against the pinned snapshot: benchmark and real-world `ERC20.mint` and
`ERC20.burn` (four rows, unsupported in the 2026-10-16 audit for renamed
locals) are now **proved** (3.4–6.3 s each). `DocsBallot.delegate` is no
longer refused for renaming; it now stops at the struct-layout gap (struct
`Voter` is not in the struct table).

**Step 3, nested storage arrays (the `contracts/Array*` suites).** solkey
closes each index's `inBounds` branch at its statement, so its paths are
plain `at(i)` and its reads walk the writes one at a time. Lean's
reduction kept every checked index as `atIn(S, q, i)`, the whole storage
inside the path, so each later write copied it: one `uint[][]` leaf had
908,084 nodes against the 24,000-node bound. Four changes, none in the
rules or the run, each with its evaluation lemma:

- `foldAt`/`foldNext`/`foldRead3` (`Calculus/DecideScoped.lean`): a checked
  index whose check reads as literal `true` (the existing bounded
  `literalRead` on `seq(atIn(S, q, i), true)`) is lowered as the plain
  `q[i]`; `q[q.length]` at a literal length likewise. `foldAt_eval`,
  `foldNext_eval`, `foldRead3_eval` (`Calculus/DecideTyped.lean`).
- `LTm.retsS` looks through comparisons and `&&`/`||` (`BinOp.isCmp`,
  `binopT_isSome`) and through `seq`/`kite` of returning terms, so `seqL`
  drops guards such as `0 < find(storage, a.length)` that a delete leaves.
- `TSegs.hasFrom` (`Calculus/Decide.lean`): `has` at a starting-storage path
  is `has` at its last dynamic index; a member, a key and a fixed index in
  range below it are always there on a typed storage (solkey's
  `wfFixedSize`/`selectOnShape*`, subsumed by `Storage C`; `findM_atF`,
  `TSegs.hasFrom_eval`). The typed `has` lemmas moved from `Closer.lean`.
- A second admission tier (`Calculus/ReadBounds.lean`): where every storage
  history is concrete (`LTm.known?`: updates at literal paths below a root
  deleted earlier, or `mtSt`, and no `pop`/`shrink`/`extend`), the closer
  and `literalRead` take up to 96,000 nodes and 40 storage updates; else
  the old 24,000/12. Measured first: on an undeleted `uint[][]` the
  elimination of `len` through 1–4 pushes grows 160, 994, 11,612, 279,608
  characters, so the old bound stays for symbolic histories. A first
  version that admitted `pop` ran away on `Examples/Tactics/Dangling.lean`
  (a dangling alias writes past the live end, whose slots a delete keeps);
  `Op2.exposes` excludes those updates.

Results against the pinned snapshot, through the testing entry point (no
regression in any row):

| Suite | 2026-10-16 audit | Now |
|---|---|---|
| `ArrayMatrixDD` | 13 pending | 8 proved, 5 pending |
| `ArrayMatrixDF` | 11 pending, 1 not run | 8 proved, 4 pending |
| `ArrayMatrixFD` | 10 pending | 7 proved, 3 pending |
| `ArrayMatrixFF` | 1 proved, 8 pending | 5 proved, 4 pending |
| `ArrayCubeDFD` | 9 pending | 9 proved |
| `ArrayCubeFDF` | 11 pending | 7 proved, 4 pending |
| `ArrayCubeDFDMemory` | 4 pending | 4 pending |
| `ArrayMatrixConversions` | 2 proved, 3 pending, 3 unsupported | 5 proved, 3 unsupported |
| `ArrayCopyShapes` | 4 proved, 1 pending, 2 unsupported | 5 proved, 2 unsupported |
| `ArrayMappingShapes` | 3 proved, 1 pending | 4 proved |
| `FixedLengths` | 10 proved, 2 pending | 10 proved, 2 pending |
| total | 20 proved | 68 proved, 26 pending, 5 unsupported |

The default build (322 jobs) and the TestSuite (`Report.lean`: 511
derived, 1 pending) pass; one pin moved (`Examples/Tools.lean`, a guard
now dropped) and the oversized-input regression of
`Examples/Tactics/Decide.lean` grew past `concreteSize`.
`Examples/Tactics/NestedArrays.lean` is the regression for the shape.
The corpus, sort and JavaScript gates were not rerun.

A read-only finder review found no soundness defect (every new twin has its
link theorem; the evaluation lemmas state equality). It found three cost
risks, all repaired: `boundsOk` tested concreteness before size; a history
counted as concrete with a value read from the memory, a read below a root
never deleted, or a path through a mapping's key (a delete keeps a mapping's
entries); and the early index probe ran on unknown histories too, where the
reduction used to stay lazy (`LTm.foldable` now gates it). Stale
docstrings were corrected. The results above are after the repairs.

What stays open in these suites, by cause:

- **Nested copies between storage and memory** (`storageToMemoryCopiesDeeply`,
  `memoryToStorageCopiesDeeply`, `memoryRowAliasBecomesIndependentStorageRows`
  in every shape; all of `ArrayCubeDFDMemory`): the memory closer reads one
  level of `copySt(m, select(S, a))` (`readFromCopyToStorage`), not the
  identity of an inner copied row. A closer feature, from
  `structMemoryRules.key`.
- **Default-allocated nested fixed memory arrays** (`memoryAssignmentSharesWrites`
  in `DF`, `FF`, `FDF`: `uint[2][2] memory m; m[0][0] = 11; …`): within
  the bounds (6,828 nodes in `FF`), but the memory closer answers `false`:
  it does not read the inner rows a declaration allocates with its
  parent. A memory-closer feature (`initIdentity`, `structMemoryRules.key`).
- **`pop` then `push`** (`ArrayMatrixDD.popPushAtDepth{1,2}…`): excluded
  from concrete histories by design; needs a read of slots past the live
  end that does not branch.
- **Frontend**: three element-type-changing copies and a struct layout
  (unsupported, unchanged).

## Toward SolKey `473da8944c` (2026-10-17)

Upstream moved seven commits past the pin. Its rule delta
(`node scripts/solkey-migration.mjs rules ../solkey 048a74de51 473da8944c`)
adds 32 program taclets (bitwise `&`, shifts, discarded expressions, local
and copy assignment values, `loopNormalize`, call-receiver reads and pops,
`memoryIndexWriteStorageRefRhsCapture`), changes 14, and adds
`newFromCopySt`, `fixedDelNodeIndex`, `selectStDelNodeIndex`,
`wfDelNodeIndexRight` and integer lemmas.

**Push semantics (done).** `d85018517f` made every empty push length-only:
`storagePushLengthSave`, `…ReferenceElement`, `storageLocalRootPushBind`,
`storageLocalPrimitivePushBind` and the compound pushes write
`save(storage, sp.length, sp.length + 1)`, no `delAt` of the appended
slot, so a slot past the end is exposed as it is (no clean-tail invariant
in general; solkey's `StorageDangling` suite closes, as on its EVM runner).
A claim about the pushed row is false from a storage with dirty tails, so
the push fixtures went pending; a contract that exposes nothing keeps clean
tails (`ReachableBy.cleanTail`, `docs/options.md` O6), and the runner states
its obligations under `cleanTail(storage)`, where they prove again
(`reading: clean`). The
048a74de51 port had made Lean reset the slot; this change reverts that:

- `Storage.pushSlot` keeps a reference slot as it is (a primitive slot past
  the end is the default on every `wt` storage, `tightH`, so it starts
  there); `Obs.reset`, `TVal.resetA`,
  `resetRd`, `SFun.reset` are gone, `pushSlot` reads as `extend`.
- The rule text, notation and printer use upstream's length save, which
  elaborates to `pushSlot` for every element kind; `UpdElem.extend` and
  `Upd.pushBindMapping` are the same updates.
- `Examples/Tactics/StorageDangling.lean` (was a refutation module in
  `Counterexamples/`) and `Examples/Tactics/Dangling.lean` now prove the
  resurrection claims in every state; `PushReceiver.lean`'s dirty-entry
  pins flip.
- The source-runner fixtures that read a row of an empty reference push
  (`PushReceiver`, `PushSources`, `MemoryPush`, `StorageReturns`,
  `PushBindings`) are open from a well-formed entry; their pins in
  `scripts/test-solidity.test.mjs` read so since 2026-10-20.
- TestSuite: five obligations that read an appended reference slot as its
  default are pending, as they stay open upstream (`SYMBOLIC_TAIL_OPENS`):
  506 derived, 6 pending at the old fixture.
- A push of a reference element exposes an old slot, so the concrete
  admission tier (`LTm.known?`) no longer counts it (`Op2.exposes`). The
  nested-array suites that start `delete a; a.push()` read rows of unknown
  length again, upstream's "needs an empty-inner precondition".

**Repin and the new taclets (done).** The snapshot moved to `473da8944c`
(`tests/migration/rule-delta-473da8944c.json`): `KeyTaclets.lean` lists
377 taclets, 341 claimed and 36 unclaimed with reasons
(`RuleShapes.unclaimedTaclets`), `migrationPendingTaclets` is empty and
`solkeycheck` is at zero.

- Signed `&`, `|`, `^` and `>>` read the operands in two's complement
  (`uintBitwise`, `wordOf`, `signedOf`); `<<` stays at `uint`.
- An assignment is a value (`(x = e)`, `x += e`, `RawExpr.assign`), an
  effect under `&&`/`||` runs only where solc evaluates it, a discarded
  value (`a + b;`, `x.pop;`) is held in a fresh local, and a storage
  reference assigned to a memory element is copied first.
- A `return` in a modifier ends that modifier alone (`wrapMods`), and an
  effect or a call in a conditional's branch runs in that branch only
  (`T se; if (c) { se = a; } else { se = b; }`, `ternaryToIf`); a
  conditional callee `(c ? f : g)(x̄)` is imported as `c ? f(x̄) : g(x̄)`.
- The closer has `intDiv.key`'s signed-remainder bounds, its sign and
  multiple lemmas, and `binaryLemmas.key`'s `binaryAnd*` lemmas
  (`Calculus/CloseLemmas.lean`).
- `whileInvariantBox` reads the loop's `break` flag (`\getLoopBreak`,
  `loopBreak`): an iteration that breaks goes on to the rest; the walk splits
  the body's goal by `andRight` (`Proves.andIntro`).  Lean also asks `¬broke`
  of the first goal, which solkey's lowering gives.
- A loop invariant may have quantified clauses, `\forall T x; a -> c`
  (`RawInv`, `LoopQ`, `invFml`), read by the box rule as `∀`.
- `structRules.key`'s `delNodeIndex` lemmas and `structMemoryRules.key`'s
  `newFromCopySt` are subsumed (rows in `docs/lean-key-rule-map.md`): Lean's
  `delete` already clears the live range and keeps the slots past it.

TestSuite at `473da8944c` (`Report.lean`): **617 functions, 546 derived,
17 pending, 54 other**; every function imports but the struct recursive
through a mapping.  Of the pending rows, ten are open in solkey too: its
`SYMBOLIC_TAIL_OPENS` (the four `testEmptyPush*`/`testFixedShape*` and the
three complex/composed push receivers) and the `unprovable*` rows.  The
other seven:

- `bitAndSymbolic`, `invariantForBreakSkipsUpdate`: every leaf closes, but
  together they need more than one declaration's `maxHeartbeats` (about
  400k and 270k against 200k), mostly `sol_close_eval` on leaves that repeat
  the prefix; `Examples/Tactics/Operators.lean` proves the `&` lemmas on one
  leaf, and `check-testsuite.sh` refuses a `maxHeartbeats` in the TestSuite.
- `memoryIndexWriteStorageRefRhsCapture`,
  `memoryIndexWriteStorageStructCopy` and
  `memoryIndexWriteStorageRefImpureIndex`: memory reads through a storage
  copy below its root (the memory closer reads one level); the last one's
  search runs away.
- `invariantClosedFormSum`: a diamond leaf whose length witnesses (`∃ a,
  len = some a`) the closer does not pick.
- `invariantQuantifiedOverPrefix`: imports and runs; its preservation leaf
  needs the old `∀` instantiated through the write's frame (`values[q]`
  diverging from `values[i]`), which the closer does not do.

**Review pass (2026-10-17).** A read-only finder and skeptic over
`3dc319e9^..7c2dad3d` confirmed three defects, now fixed:

- A conditional callee was imported with its condition before its
  arguments; solc's legacy pipeline evaluates the arguments first.  The
  import now refuses one whose condition or arguments have an effect
  (`condCalleeOk`, `pureExpr`).
- Renaming an inlined callee's locals reached below a quantifier's binder
  of the same name (`RawInv.mapM`); quantified clauses are now renamed only
  by `RawInv.rename`, which stops at the binder (pinned in
  `Examples/Tactics/Loops.lean`).
- A loop lowered twice (its `_;` filled into a modifier's loop) lost its
  `break` flag; `lowerLoop` keeps it.

Left as they are: a conditional with effects in a branch takes its capture's
type from the non-literal branch, not solc's common type (a refusal, never
a wrong program); the `brk` flag is not printed, so a printed lowered loop
re-read has no break test (a weaker rule, not an unsound one); a
`\forall` clause of a function whose locals are renamed by the import is
unsupported (`rewriteLoopBindings` reads a program expression).

## Reproduce the inputs

The committed snapshot contains 274 files: the tracked Solidity and `.key`
examples, core `.key` test fixtures and their Solidity input, the rule resources,
and the compiler's Gradle pin. It contains 112 Solidity sources.
`tests/migration/solkey.pin.json` independently pins the
snapshot manifest's hash; the manifest pins each file's SHA-256 and upstream
commit. The compiler binary remains outside this package and is checked against
the snapshot's Gradle SHA-256. No package dependencies are added.

```sh
node scripts/solkey-migration.mjs snapshot ../solkey 048a74de51 tests/migration/solkey
node scripts/solkey-migration.mjs verify tests/migration/solkey
node scripts/solkey-migration.mjs rules ../solkey 1b4341a303 048a74de51
node scripts/solkey-migration.mjs generate-taclets
```

Snapshots are immutable. Re-importing the same revision verifies and reuses it;
a different revision requires a new destination. The source commit recorded by
`solc-ast.mjs` comes from the snapshot, not this repository's enclosing Git tree.
Relative compiler paths are resolved before loading the compiler.

`tests/migration/rule-delta.json` records added, removed and changed rule bodies.
The comparison includes deleted rule files, ignores comments and preserves
string contents, including whitespace in branch labels. The generated program
inventory contains 345 taclets. The current rule table claims 330 and records
fifteen architectural exceptions; `migrationPendingTaclets` is empty after
registering the three call-receiver rules. This partition checks names, not
complete source support: effectful call-receiver operands and other semantic
boundaries remain required migration work. The three existing loop rules have
been reviewed and registered under their upstream names with explicit
restrictions below. The inventory is not a coverage claim.

## Run the suites

```sh
lake build Solidity.Frontend.Testing
node scripts/solkey-migration.mjs baseline tests/migration/solkey /tmp/listing.json ../solkey/keyext.solidity.core/build/soljson listing
node scripts/solkey-migration.mjs expectations tests/migration/solkey /tmp/listing.json tests/migration/expectations.json
node scripts/solkey-migration.mjs baseline tests/migration/solkey /tmp/proofs.json ../solkey/keyext.solidity.core/build/soljson proof
node scripts/solkey-migration.mjs compare tests/migration/expectations.json /tmp/proofs.json
```

Baseline reports checkpoint after each proof batch and source, with the complete source list,
completed sources, commit, mode, per-function results and errors. Large contracts
are tested in batches of 32 imported rows, each with the normal subprocess limit.
Failed batches retain checkpointed results and explicitly mark unattempted rows.
Function signatures distinguish overloads. The Lean command accepts `from N
count K` before `listing`/`to`; the JavaScript API accepts `batchSize`.

The expectation manifest targets proofs for positive suites and proof-open
results for the upstream `open` and `unprovable` directories. Proof-open means
the prover did not close the obligation; it does not prove a specification false.
Timeouts and subprocess errors always fail comparison. Deliberately noncompiling
sources in `illegal/nocompile` require an actual compiler diagnostic and are
recorded as `compileRejected`; process failures cannot satisfy that expectation.
Existing recursive-struct exclusions remain explicit. Other unsupported imports
are migration failures, not accepted baselines. Failed imports remain required
gaps until a clean listing is reviewed and the manifest regenerated; merely
producing one row from a previously failed contract does not discharge the gap.

Comparison rejects wrong commits/modes, incomplete source coverage, missing or
duplicate function rows, unexpected rows, changed outcomes, and errors. An empty
expectation set cannot pass. Updating expectations is a reviewable change, not
an automatic acceptance of observed failures.

## Milestones and remaining work

### Inputs, inventory and baseline tooling

Implemented the immutable snapshot, hashes, rule diff, inventory generator,
strict comparison and baseline runner. The first listing attempted all 111
sources: 1,091 ready obligations, 414 unsupported rows, three exclusions,
25 skips and 128 internal helpers. It also recorded 25 source/contract errors;
13 of those are deliberate compiler-rejection fixtures. These are listing
counts, not proof counts. A refreshed listing records signatures and compiler
rejections separately.

The first proof baseline reached 157 TestSuite proofs before the whole-contract
120-second limit, leaving 386 rows explicitly unattempted. That demonstrated the
need for the batching change; it does not replace the existing 437 derivations.
The historical TestSuite AST and proof modules have not yet been repinned.

Read-only finder and skeptic reviews identified deleted files missing from the
rule diff, empty/partial/wrong-pin reports passing comparison, string content
normalization hiding branch-label changes, manifest omissions, and stale snapshot
files. The fixes include union-of-revisions enumeration, strict report metadata,
string-aware normalization, a separately pinned manifest hash and immutable
snapshot destinations. Regression tests exercise these boundaries.

### Primitive push through a complex receiver

`Solidity/Syntax/Elab.lean` now captures a complex receiver before declaration
or assignment of the primitive returned by `push()`, corresponding to
`localValuePush_unfold_leftFstReceiver`. Simple receivers retain their existing
elaboration. `tests/solc/PushReceiver.sol` exercises both forms and a false claim;
`Solidity/Examples/Tactics/PushReceiver.lean` proves initial-state execution of
both cases in the kernel. After the reference-slot reset and symbolic-read bridge repair, both the nested
and effectful receiver obligations prove over all allowed entry states. The
false assertion remains proof-open. The repaired dirty entry also has a
kernel-checked execution theorem, and a general theorem proves mapping slots
retain every entry.

### Required next milestones

- Resolve the complete fixed proof baseline's import, runtime and proof gaps;
  the import-segmentation snapshot now has a completed uniform run below.
- Repair storage-theory correspondence, especially reference-element push,
  fixed/dynamic array copying, deletion and well-formedness. The upstream
  reference push now clears the appended node; the immediate-slot reset is
  integrated in Lean. Compatible mapping-free fixed/dynamic snapshots are also
  implemented. Deeper shadow deletion and copy correspondence remain open.
- Native effectful call-receiver capture is integrated, including source,
  rule registration and ordinary/callback correspondence. Continue auditing
  unsupported source shapes; their printers retain explicit fallback forms.
  The sort-check gate matches all 131 read-bearing taclets.
- Complete frontend gaps exposed by the imported suites, including the remaining inheritance boundaries,
  broader storage returns, short-circuit calls, unsupported container widths and struct
  layouts. Modifiers, overload identity, enums and constants already have
  restricted support and regressions; unsupported cases remain visible.
- Investigate the remaining TestSuite cases: 511 obligations are derived,
  `invariantClosedFormSum` is pending, `invariantQuantifiedOverPrefix` is
  unsupported, and one obligation is excluded. Two source functions are skipped.
  A pending result is not evidence of validity or falsity. Corpus tables and
  the rule map are regenerated at each milestone.
- Complete area-specific finder/skeptic reviews and run the full validation
  commands in AGENTS.md against the pinned snapshot.

### Reference push diagnosis (before integration)

A kernel-checked scratch counterexample establishes the precise mismatch: an
empty outer array with a shadow row containing `9` satisfies `wtB`, but the
`nested` fixture fails because its first reference push exposes that old row.
The counterexample is a typed entry-state test, not a claim that a legal Solidity
program can reach arbitrary dirty shadow data. Dangling-reference executions
remain compiler-specific/undefined.

The proposed operation resets the slot at the old length using `SVal.defaultOf`
before appending it. Mappings are retained, fixed arrays keep their length,
dynamic arrays become empty, live elements before the appended slot are
unchanged, and later shadow slots are unchanged. The scratch prototype proves
its full array observation equation and preservation of every existing
hereditary run invariant. Integration must update the interpreter, observation
bridge, symbolic reads, program-rule correspondence, printers and regressions
together. The core operation and its observation/symbolic-read bridges are now integrated
and checked. The frontend and dirty-entry execution target build passes. The program rules now distinguish primitive reset, reference reset and mapping
length-only extension, including alias-binding updates. Historical proof
reclassification and broad validation remain open.

The second read-only review found runtime/heartbeat exceptions mislabeled as
proof-open results. They now report `error`, and comparison also rejects a
`pending` row whose reason is not ordinary open proof goals. Git subprocess
errors are checked separately from exit status. The receiver regression now
includes `matrix[i++].push()` in both binding forms, with kernel-checked index
and row-length observations.

Current focused verification: per-file Lean diagnostics are clear for all
changed Lean files; the frontend and execution-example targets built;
`node --test --test-isolation=none scripts/test-solidity.test.mjs scripts/solkey-migration.test.mjs`
passed all 12 tests before core reset integration; the orphan check reports 297 reachable modules and no
orphans; `git diff --check` passes. The documentation path check still reports
the six existing uncopied LeanTeX vendor references. Full migration validation
remains outstanding.

### Unchecked blocks and existing struct correspondence

The solc reader now prints `UncheckedBlock` as `unchecked { … }` through the
existing syntax and wrapping arithmetic. Source-to-proof checks prove overflow
wraps to zero and checked arithmetic resumes after the block; a false assertion
remains proof-open. The initial listing had 19 rows blocked directly by this
missing AST form. The baseline also applies the existing `Triple => FixedTriple`
renaming for TestSuite; a selected fixed-member function now lists as ready.
The testing JavaScript API exposes explicit `renaming` for other callers.

Storage review confirmed immediate-slot reset, mapping retention and fixed-array
length preservation, but identified further boundaries: deletion of deeper shadow
descendants differs from upstream, explicit `push(value)` copying is separate,
and the old dangling-resurrection derivations in `Derived13` contradict reset
semantics. Upstream moved those cases into an expected-open suite. They must be
reclassified with evidence rather than retained as proofs of obsolete behavior.

The initial diagnostic proof report is stored in
`tests/migration/proof-baseline-initial.json`, with its compact summary beside
it. All 111 sources were attempted. After replacing the interrupted TestSuite
portion with the complete batched run, it records 839 proved, 206 ordinary open,
391 unsupported, 12 runtime-error and 56 unattempted rows, plus 13 deliberate
compiler rejections, three exclusions, 25 skips and 129 internal helpers. There
are 23 process/import errors. The TestSuite source alone (including PairLib) has
456 proofs, 17 ordinary open results, 55 unsupported rows, one exclusion, two
skips and 22 internal helpers, with zero process errors. Some early diagnostic
rows predate signature reporting and therefore appear missing/unexpected in
comparison; the final baseline must be regenerated uniformly. These reports
precede reset integration and are not completion evidence.

Post-reset targeted source-to-proof results: `nested` proved in approximately
2.3 seconds, `effectfulReceiver` proved in approximately 23 seconds, and
`falsePost` stayed ordinarily open, with no subprocess errors. The before-reset
nested search was open after approximately 12 seconds; effectful receiver
search exhausted its budget. No heartbeat limits were raised.

### Length-only terms and resetting push terms

The integration review found that generic `Op2.extend` still printed as a bare
length save while its evaluator reset reused references. The two operations now
have separate interpreter helpers (`extendPlace`, `pushPlace`; `extendPlace` was
later folded into `pushPlace`), observations
(`extendA`, `resetA`) and symbolic readers (`extendRd`, `resetRd`). The mapping
agreement theorems require the mapping side condition; the overall statement
soundness theorem retains its unconditional contract. A kernel regression on
the same well-formed dirty storage checks length-only extension exposes a row
of length one and a resetting push exposes length zero. A fixed array of
mappings retains its arity and entries. Source regressions cover mapping bare
push and alias binding across a pop.

Focused build after this repair: `lake build Solidity.Frontend.Testing
Solidity.Examples.Tactics.PushReceiver Solidity.Calculus.Sound
Solidity.SortCheck.Faithfulness` passed all 125 jobs.

The finder/skeptic review of the repaired distinction found no new correctness
defect; its docstring typo was fixed. All 13 source/tooling regression tests
passed (44.5 seconds), the orphan check reports 297 reachable modules and zero
orphans, and `git diff --check` passes. The pinned sort check reports exactly
ten unannotated rules: memory-copy push and the nine pushed-element arithmetic
and increment/decrement rules. An explicitly selected missing rules file now
fails rather than silently skipping this gate.

### Source declaration identity and primitive declarations

The importer now assigns overloaded declarations distinct internal names using
solc IDs, resolves calls by their referenced declaration, and retains original
source names and parameter-type signatures in testing reports. Signature
normalization changes elementary type tokens only, preserving identifiers such
as `uint256Flavor`. The regression covers numeric, Boolean, enum and value-type
overloads, generated-name collision, and selection by source signature.

Supported constant values are inlined with a cycle guard; enums lower by their
declaration IDs and ordinals. Primitive user-defined value types lower to their
underlying types. Numeric bounds and numeric wrap/unwrap retain typed casts,
while Boolean/address values retain their already validated model types. These
features reuse the existing arithmetic calculus. Immutable values, narrow
aliases and runtime casts into enums remain gaps. An empty library can contribute
an empty result list without hiding a missing explicit function selection or
allowing an all-empty test suite to pass. The current TestSuite listing has
488 ready rows, 35 unsupported, 27 internal, two skips and one exclusion, with
no process errors. This is import coverage, not proof coverage.

The frontend finder/skeptic review exposed loss of narrow/signed arithmetic
types in bound and wrapper folding, cross-contract alias-name collisions, and
signature normalization inside identifiers. Fixes retain arithmetic casts,
resolve alias types by ID/canonical name and normalize whole tokens. Regressions
include unsigned/signed overflow and same-named unsigned/signed aliases in
different contracts, alongside Boolean/address wrappers and false claims.

The repaired frontend milestone passed all 16 regression tests in 57.8 seconds.
Finder and skeptic confirmed no further defect in the supported forms inspected.
`Stmt.sound` and the dirty-state regression theorems depend only on `propext`,
`Classical.choice` and `Quot.sound`. The documentation path check still fails
only on the six existing missing LeanTeX vendor references.

### Importing modifiers through the existing inliner

Modifier definitions and applications are now printed into `contract!` syntax
and expanded by its existing `wrapMods`. Their called functions contribute to
the dependency graph. A modified function's root obligation calls the imported
function, so testing it directly also runs its modifiers. Constructor deployment
retains modifier attributes and initializes storage before entering them.
Per-modifier local renaming and the existing inliner preserve application scopes.

The focused modifier source test passed in 7.6 seconds: arguments, first-listed
outermost ordering, continuation after a return, direct application and false
claim, delayed argument evaluation, per-application locals, multiple placeholders,
internal calls from a modifier and constructor initialization. Broader build
and review remain in progress.

Modifier import raises the current TestSuite listing to 494 ready rows and
31 internal helpers, with 25 unsupported rows, two skips and one exclusion.
The review found unsupported narrow modifier parameters could lose widths or
poison unrelated imports. Their definitions are now rejected before inclusion;
unsupported reference/narrow-array modifier parameters are localized likewise.
The fixture retains unaffected positive functions alongside these gaps.
Initializer-gap fixtures now use unsupported assembly rather than ordinary
modifiers, since ordinary modifiers are supported. Their ASTs were regenerated
with the pinned compiler.

The first default build identified stale printed counts, chain lines that still
showed a reference push as length-only, an overly broad receiver capture, and
historical dangling-resurrection claims. Count pins and reference-push chain
terms are being updated; primitive receiver capture now leaves alias bindings
to their existing calculus rule. Dangling claims require explicit refutation
and reclassification. This failed integration build is not a validation pass.

Unnamed modifier parameters now receive collision-checked synthetic names; their
arguments still evaluate, including effects. The finder confirmed this repair.
The focused modifier/initializer-gap tests passed after the narrow-parameter
guard. The module-level dangling examples now retain the original claims as
formulas with kernel-checked refutations at the initial state, rather than
asserting obsolete theorems. Their long-round capacity checks remain. Reference
push chains were updated through their merged final terms and checked.

The integrated default build now passes: `lake build` completed all 287 jobs.
All 17 source/tooling regressions pass (102.7 seconds while the broad build ran).
The orphan check reports 297 reachable modules and zero orphans;
`git diff --check` passes. These gates do not yet include the historical
TestSuite derivations or certify the remaining 25 TestSuite imports and ten
program sort-annotation gaps.

The example-integration finder/skeptic review found no assertion weakening.
Five original dangling formulas have explicit kernel refutations; the four
rounds formulas retain search/capacity guards only, and their documentation now
makes that distinction. The reference-push chains and merged final terms are
checked. The successful 287-job default build and 17-test run above supersede
the earlier failed integration run; the historical TestSuite target remains
a separate outstanding gate.

### Upstream dangling-suite reclassification

The historical `Derived13` check failed exactly four former resurrection
derivations; its remaining `testArrayCopyClearsOldElements` still checks.
The former `Counterexamples` module `StorageDangling` imported the pinned upstream
`solc/open/StorageDanglingOpen.sol` fixture and kernel-refuted all four original
obligations at the initial typed state (since `473da8944c`'s length-only push
it is `Examples/Tactics/StorageDangling.lean`, which proves them). Their obsolete `.proved` declarations
were removed from `Derived13`. Until the main TestSuite fixture is repinned,
its historical report expects 433 derived and four pending rows; that full
report still needs verification. The current source removed those four rows
from the positive TestSuite and retains them in its open suite.

### Free functions, libraries, and primitive binding grammar

Helper calls resolve by declaration ID, with collision-checked generated names
for foreign helpers. Library extension receivers precede arguments; named
arguments are ordered against the remaining parameters. Known helper member
calls also qualify as tuple sources. The dependency closure includes helper
bodies while independent report rows remain those of contracts and libraries.
Top-level free functions are helpers only, without independent test rows.
Recursive helper calls remain unsupported. Unrelated foreign helpers are not
added as contract members merely because testing mode is enabled.

The read-only finder and skeptic identified missing tuple-call recognition
and the boundary on top-level test roots. Tuple recognition was extended only
for known helper declaration IDs; arbitrary external member calls remain
outside that recognition. Documentation now states the test-root boundary.
The expanded library regression passes (5.96 seconds), including a library's
own qualified calls, direct and attached calls, named arguments, tuple returns,
receiver effects, a false claim, and recursion rejection.

A duplicate high-priority zero-argument declaration grammar caused
`uint y = values.push()` to fail macro expansion. Removing that redundant
grammar leaves the existing variadic call declaration grammar and its empty
case. The source regression passes (2.87 seconds), checking declaration and
assignment bindings, an ordinary zero-argument function call, and a false claim.
No execution or proof rule changed in this parser repair.

The main TestSuite AST now pins `048a74de51` (hash `0x6553ea1d6de3da1f`).
Its checked import summary is 551 functions: 527 elaborated, two skipped,
one excluded, and 21 unsupported. The checked scoped table contains 497
obligations. Existing derived proofs and a complete current proof report are
being checked separately; a ready obligation is not a proved one.

### Fresh-array reads and size effects

The typed value reader now observes the allocated length and recursively typed
defaults of `new T[](n)`, retaining absent elements outside the size. Its
representation proof preserves failed size evaluation. The memory closer's
new primitive-array clause composes allocation, initialized-element and
copy-read laws. It checks the exact source and memory of the copy, retains
copy definedness, and returns absence for an out-of-range index. The supporting
heap lemmas and evaluator equality are kernel-checked; there is no new axiom.

The elaborator hoists allocation-size effects before target effects, capturing
the size when the target can mutate it. Memory-local allocations use the same
capture mechanism. This changes only effectful sizes or targets; ordinary
simple-size allocations retain their existing elaboration.

The read-only finder and skeptic found no confirmed defect. Their scope review
identified nested reference-element and fixed-array copy reads as unfinished,
and requested effectful-target and memory-local size regressions. Those cases
were added. Source proof search closes the primitive root, symbolic size,
storage and memory `n++` sizes, and `matrix[i++] = new uint[](i)` evaluation
order. The false-value and empty-array assertions remain open. Nested defaults
also remain open to the closer, while seven separate kernel execution checks
confirm the interpreter's concrete results, including nested defaults and the
two failing assertions. These concrete checks do not claim general validity
of the nested-copy obligation.

The focused fresh-array source regression passes (31.5 seconds). The original
upstream `newArrayCaptureStorageRoot` assertion now has a permanent theorem in
`Derived15`; that module's 50 migration derivations build successfully. The
root capture shares the already proved `newArrayCapture` replacement and is
recorded as a merged origin for its storage-root and complex-target cases.
The partition now records 311 claimed, 19 pending and 15 architectural rules
at the 345-taclet pin. `git diff --check` passes and the module check reports
300 reachable modules, zero orphans. The full derived report remains a
separate outstanding gate.

### Parallel push exhaustion and imported-obligation inspection

The scoped exhaustion reader previously handled only a single storage update.
An alias-returning push has two parallel elements, so its three default-read
obligations remained open on the length-capacity guard. `pushLocalExhL` now
handles a storage push paired with a local binding, requiring that binding's
right-hand side to return in the original state. Its soundness theorem uses
the existing typed exhaustion semantics, which both modalities accept. This
is model-specific resource handling, not an additional upstream taclet.

The prototype and integrated soundness module check. All three original
upstream fixed-array, dynamic-array and struct return obligations now have
permanent derivations; `Derived15` builds with 53 theorems. The expanded
source regression passes (7.5 seconds) and keeps its false reference assertion
open. A kernel theorem separately checks that division by zero in a parallel
binding blocks the shortcut, for every initial array length. Mapping-alias
diamond coverage was added alongside the existing mapping preservation tests.

The read-only finder found the single-push and push-plus-local cases disjoint,
the RHS guard faithful to parallel semantics, and no additional search
recursion. It requested the failing-binding and mapping-diamond regressions
above. General multi-element updates remain outside this shortcut. The final
skeptic review and whole-suite gates are recorded separately when complete.

All 20 source and migration-tooling regressions now pass (113.5 seconds),
including the new mapping-alias diamond case. The failing-binding kernel
regression builds. A diagnostic TestSuite proof report contains 486 proved,
11 pending, 22 unsupported, 31 internal, one excluded and two skipped rows,
with zero process errors (553 rows including the companion library). Because
integration continued during that diagnostic run, the permanent derived
report and the full 112-source baseline are being checked again from the
finished code; only those final gates certify uniform results.

`#wp` and `#step` now read imported obligations through `Symex.evaluable`.
Previously a declaration without executable code failed the inspector's
compiler, even though symbolic execution could read its value. Two output
pins on a noncomputable declaration pass, as do the existing tool examples.

### Complete fixture inventory and corpus parity

The snapshot was extended at the same commit with 45 core test inputs:
44 `.key` files and the helper-only `FieldBox.sol`. Every original one of
the 229 manifest entries was verified byte-for-byte unchanged before installing
the reviewed extension. The final manifest pins 274 files and 112 Solidity
inputs. The snapshot tool now rejects a stale file scope explicitly. The
old-scope baseline was stopped and restarted against this complete manifest.

The imported corpus reads TestSuite's own compiler declarations after checking
the source hash. This excludes three foreign helpers and includes two external
functions the old header parser missed. Its commit comes from the verified
snapshot, not the enclosing Lean repository. The checked report is now
486 derived, 11 pending and 54 other rows; all 14 historical proof modules
rechecked serially. The separate no-Lean trust/parity audit passes with
514 obligations, plus two skipped functions and 35 internal helpers.

The finder identified 64 substantive `.key` proof fixtures and two expected-open
core fixtures omitted from the old table. These are now explicit unported rows,
with provenance and no claim of counterexample or proof. The seven core smoke
fixtures have truthful loader/taclet-test descriptions. The generator verifies
that every problem-bearing `.key` input in the snapshot has an inventory row.
The single old storage fixture was deleted by the target upstream commit and
is removed from the current table. Generation succeeds with 723 rows:
486 derived, 53 proved by the existing concrete corpus, 100 unported,
70 unsupported, 11 pending, one excluded and two skipped. Full corpus
re-probing and the 112-source proof baseline remain required gates.

The read-only skeptic confirmed the snapshot counts, declaration scope,
duplicate-name rejection, commit validation and preservation of open gaps.
The default build found one stale pin: `pushAlias` now closes after the
parallel exhaustion repair. Its example now pins a closed leaf and a kernel
derivation; the complete proof-tree example module checks.

Both final inventory reviewers confirmed all 723 rows are accounted for with
no duplicate suite/contract/function key and no new proof or falsity claim.
The default build (289 jobs) and full TestSuite target (144 jobs) pass.
`./run-lean.sh` then fails at the expected sort gate: 345 program taclets,
131 read-bearing, 121 annotated and the ten genuine missing rows listed
above. This is not a successful complete migration gate. The six pre-existing
LeanTeX vendor doc-path findings also remain. The orphan check is clean
(300 reachable modules), and `git diff --check` passes.

The corpus re-probe found stale verdicts from its older checks: 17 concrete
cases now prove (decrements, unsigned powers, array lengths and allocations,
and conditional memory sources). Their existing statements are retained;
signed power cases remain unsupported with their current type error. The
imported-contract root pin also needed the nine newly added storage roots.
Re-pinning and the full corpus build are being checked separately before
these gains are accepted.

The updated corpus gate passes: `check-corpus.sh --update` re-probed the
statements and built `SolidityCorpus`. The table now contains 70 concrete
kernel proofs and 53 unsupported rows (the total remains 723). Concrete
proof rows carry explicit verification evidence in the reason column,
preserving six TSV fields without trailing empty-field whitespace.

### Loop correspondence lane

The three existing proved loop rules now reside in `Taclet` under the current
upstream names: `whileUnwind`, `whileInvariantBox`, `whileInvariantDiamond`.
The statement dispatcher, runtime semantics and annotation defaults are
unchanged. Explicit replay and totality checks follow the moved constructors.
The exclusive inventory partition is 314 claimed, 16 pending and 15 excused;
the six genuinely Lean-only rules remain separate. Paper-rule coverage is
unchanged: the loop rules are upstream rules outside that printed table.

This is a restricted transcription. Lean keeps bounded unwind metadata,
capture-free conditions, boolean-expression invariants, conservative frames
and unsigned variants. The variant must be defined where the invariant holds,
a stronger requirement than the upstream skolem antecedent. Wider formula
invariants and integer variants are not claimed. The name table records the
reviewed correspondence and checks inventory coverage; the existing kernel
theorems establish soundness.

The finder and skeptic found no semantic or overlap defect, and requested
clearer restriction and inventory wording. The printer needed its existing
invariant-label path enabled for `Taclet`, preserving the upstream branch
labels after the move. Output pins now distinguish 164 upstream constructors
from six Lean-only ones. The dispatcher, partition and printed classifications
build, and all loop, rule, proof-tree and tool example modules build. Observed
checks in the isolated lane: Rules 4.3 seconds, Taclet 21 seconds, rule-existence
10 seconds, loop examples 23 seconds. These timings are not a controlled
before/after benchmark. All 15 derived-proof modules and the full SolkeyTestSuite target passed in
the isolated lane before integration. The full 112-source pre-integration
proof baseline is preserved separately; it is not a validation of later edits.

### Enum specifications and cached-worktree source tests

The solc importer already resolves program enum members by declaration ID, but
raw NatSpec enum names were left unresolved. Contract, function and loop
clauses now resolve whole dotted enum names from the validated declarations'
ordinal order. Canonical names are available across the source unit; short
names come only from the defining contract/library or source unit. Inlined
helper annotations use their defining scope, recovered from retained member
IDs because the trimmed fixture omits solc's `scope` field.

State variables, parameters, returns and local declarations block substitution
of the same head, and ambiguous aliases remain unresolved. The finder and
skeptic identified foreign-helper scope, escaped binders and comment-separated
quantifier binders as capture risks. All were fixed and pinned. Clauses
containing quantifiers or escaped identifiers stay verbatim: supporting enum
resolution there requires the specification parser, rather than more lexical
substitution. This restriction keeps unsupported clauses visible.

The new source fixture covers distinct library/caller enum ordinal orders,
contract invariants, file/canonical names, loop annotations and true/false
postconditions. A separate check inspects the imported helper's actual clause;
four parameter/quantifier shadow cases must report errors. All four unchanged
upstream `real-world/Enum.sol` specifications prove. The complete source and
migration-tool regression suites pass: 23 tests in 129.4 seconds.

The runner now checks temporary files with `lake --no-build lean`, which
supplies Lake's artifact-cache import map. A clean worktree need not contain
local copies of its cached imports, so plain `lake env lean` could fail despite
a successful build. A failed or timed-out tool job also terminates its own
process group with SIGKILL on Unix, preventing orphaned Lean descendants from accumulating
during an unattended baseline. The descendant-timeout regression passes,
including a ready descendant and parent that both ignore SIGTERM. All 24
source/tooling regressions pass on the integrated checkout (125.2 seconds).

### Full baseline and review of upstream-open results

The frozen pre-loop/enum proof baseline attempted all 112 sources and is kept
as `tests/migration/proof-baseline-before-loop-enum.json`. It records 876 proved,
200 pending, 257 unsupported, 44 error and 36 unattempted rows; also 157 internal,
25 skipped, three excluded and 13 genuine compiler rejections. There are 28
source/process error records, which overlap with per-row errors and must not be
added as separate obligations. A complete newer listing covers all 112 sources,
with 1,151 ready, 262 unsupported and 12 import-error records. The expectations
were regenerated from that listing, independently of proof outcomes. Strict
comparison still fails: 12 required import gaps, 532 changed outcomes and 28
error records. The migration is not complete.

The finder and skeptic reviewed all 25 proofs in upstream `open`/`unprovable`
directories against their source comments and Lean's execution semantics:

| Cases | Finding |
|---|---|
| OZMath `tryDiv`, `tryMod`; constructor `baseConstructorArgumentsSelfMul`; four modifier examples | Fml.Valid arithmetic or lowering improvements over the upstream proof strategy. |
| Five unsigned/environment bound examples; two truncating-cast examples | Fml.Valid consequences of Lean's bounded values and casts. |
| Seven checked-overflow/underflow boxes in `Unprovable.sol` | Fml.Valid boxes because checked execution halts before `assert(false)`, as the upstream source explicitly describes for the EVM. |
| Payment examples `trySuccessKeepsStorageUnsound`, `callKeepsStorageUnsound`, `tryArgumentSideEffect` | Depend on the ordinary no-callback model. They are not unconditional Solidity guarantees and remain required callback-compatibility gaps. |
| `SolcTypesOpen.ternaryLiteralOverflow` | A genuine frontend type-fidelity bug: solc's `uint8` conditional width was lost, allowing an incorrect returning diamond. |

Expected-open directories are therefore not a specification of falsity. A
future source-derived expectation policy must distinguish legitimate Lean
improvements from callback-model restrictions; it must not whitelist observed
statuses. The current strict failures preserve this review boundary.

### Loop integration gate

The full build found an obsolete theorem claiming no upstream taclet can run a
loop. After registering the three loop rules that statement is false. The
replacement `Taclet.not_unwindZero` and the public strictness theorem isolate
the actual remaining witness: `unwind 0`, which selects Lean's `loopExit`.
The conservative `inSolkey` predicate remains loop-free; it is sufficient,
not necessary. The reviewed replacement and headline theorem build, as do
the full package and all imported-suite proofs. `./run-lean.sh` gets through
both builds and fails only on the ten recorded missing sort rows. The
cache-aware, non-updating corpus check passes with all 723 rows unchanged.

### Conditional literal widths

The open-result audit found that the importer discarded solc's narrow type
for a conditional with literal arms. In `ternaryLiteralOverflow`, both
conditionals have type `uint8`; their addition must halt on overflow before
the `uint16` target can receive 318. The importer now preserves that narrow
result with the existing typed cast/capture before surrounding arithmetic.
It does so only when both arms are solc compile-time constants. Typed-variable
arms already retain their widths, and redundant casts would reject previously
supported nested conditionals or short-circuit expressions.

The unchanged upstream overflow diamond now stays pending with no import
errors. Source regressions prove the corresponding box halt, unchecked result
62, and explicitly widened result 318. They also retain nested typed-variable
conditionals and short-circuit reads, while a signed-variable overflow diamond
stays pending. Signed literal conditionals, literal conditionals nested in a
branch or short-circuit RHS, and branch effects remain explicit unsupported
boundaries. No false proof is accepted as a semantic deviation.

The finder and skeptic found no remaining false-proof or evaluation-order
defect in this restricted repair. All 24 source/tooling regressions pass in
the isolated lane (132.7 seconds); the final added boundary cases pass in the
focused source-types check (11.7 seconds). Full integrated gates are rerun
after the repair because its captures can change imported proof programs.

### Complete baseline after conditional-width repair

`proof-baseline-current.json` attempted all 112 sources against the same
implementation: all 125 source hashes in its `.implementation.json` sidecar
were unchanged at completion. The summary records 843 proved, 182 pending,
247 unsupported, 35 error and 115 unattempted rows, plus 148 internal,
25 skipped, three excluded and 13 compiler rejections. The 34 source/process
error records overlap with row outcomes. Strict comparison records 12 required
import gaps, 578 changed outcomes and 34 errors; it still fails.

The imported TestSuite remains 486 proved and 11 pending. Across the wider
corpus, interrupted jobs leave more rows unattempted than in the earlier
baseline. Some jobs hit the process timeout; others terminate without a Lean
diagnostic. This run therefore does not establish a proof-coverage regression
or improvement from its aggregate totals. Interrupted rows need isolated
rechecks, and the runner should retain process exit/signal metadata. The
original report is preserved; interrupted jobs are not reclassified as pending.

### Sequential-update prerequisite

The nine native compound/increment push rules first append/reset the new
slot, then read and save it in a second storage update. `Premise.updates U V`
now preserves this shape as two nested updates, with an explicit intermediate
context. Both ordinary and callback sequents, their strategy walkers, quotation
and printers carry the pair in that order. Each update remains parallel
internally; this does not silently merge them.

`PairLands` links the successful updates through one typed intermediate state.
`PairFails` records an ordinary failure in either stage and explicitly excludes
exhaustion. These give `Premise.sound_updatesH` and `holdsC_updates`, with only
the standard three axioms. Neither proof changes a statement's execution.
Permanent notation examples distinguish sequential result five from parallel
result twelve, check declarations in either stage, and kernel-check quotation
across the intermediate scope.

Finder and skeptic found a first-stage declaration scope limitation in the
initial macro. It is fixed and pinned in both declaration positions; their
follow-up review found no remaining defect. This is prerequisite support only:
no native suffix taclet is registered by it. Guarded division/remainder,
general reset/read/save agreement, capture order, the typed statement forms
and full rule integration remain work for the push port. Coverage counts stay
314 claimed, 16 pending and 15 architectural, with ten missing sort rows.

The package build passes (289 jobs), and all imported-suite proofs pass
(144 jobs). The new ordinary/callback agreement theorems use only `propext`,
`Classical.choice` and `Quot.sound`. Orphan checking passes after removing
the ignored scratch prototypes; their code is retained outside the checkout.

### Process-failure reporting

The complete baseline exposed failed processes whose warning output hid
their termination outcome. The runner now includes the exit code, signal,
OS error code, timeout flag and configured deadline in each tool error,
alongside the diagnostic text. Compiler and Lean report errors retain this
metadata. A process can report both an OS error and an exit/signal outcome;
the header retains every available part rather than discarding one.

The exit-with-output, signal-with-output and descendant-timeout regressions
pass. In the first complete regression run, 24 of 25 tests passed and one
Lean subprocess exited 135 without a Lean error message while other checks were
running. Its isolated rerun passed in 7.6 seconds; the original failure is
retained in the log. The earlier 112-source report remains unchanged and
predates this runner edit. Its completion hash check describes that earlier
implementation, not the current working tree.

Final integrated verification passes both Lean builds (289 and 144 jobs),
the non-updating 723-row corpus check, imported-suite parity and orphan
checking. All 25 source/tool regressions pass in an isolated run (132.4
seconds). The sort checker still reports exactly the ten documented missing
push annotations. Documentation path checking still reports the six existing
references to uncopied upstream files in `vendor/LeanTeX/VENDOR.md`.


### Native push interpreter and update agreement (isolated lane)

The native push lane now has separate typed `Stmt.pushOpAssign` and
`Stmt.pushIncDec` forms. A compound suffix evaluates its source first,
resolves the array once, resets/appends the new slot, then applies the checked
operation. Increment/decrement suffix statements discard their expression
value. Ordinary `OpLoc` is unchanged, so its existing no-allocation and
termination theorems retain their original meanings.

`Calculus/SoundPush.lean` proves general agreement against those actual typed
runs, with no storage well-formedness premise: the two update stages land
through the appended state or fail in the corresponding stage. It also proves
source-first and receiver-once capture and connects every arm to
`Stmt.stepSound_arms`. The hereditary storage invariants, weakening, no-panic,
callback determinism and fuel semantics cover the new statement forms.
`Examples/Tactics/PushSuffixRun.lean` checks unsigned failures, zero divisors,
signed decrements and recycled primitive slots against the actual constructors.

The EVM compiler conservatively excludes both new forms from its supported
fragment, while counting one push for either statement. Its simulation theorem
still checks under its existing 10000-heartbeat limit. Impossible fragment
cases now use `Option.noConfusion` directly; no checking limit was increased.
The compiler-IR probe confirms source-before-append evaluation, but this stage
does not establish an EVM correspondence for the new statements or remove the
existing capacity approximation.

This is an isolated implementation milestone, not an integrated native taclet
port. The following stage supplies the DIV/MOD outer guard and its premise
notation. Native statement schema notation, rule registration/coverage/sort
rows, source elaboration and returned prefix/postfix values remain unfinished.
The main checkout's previous migration counts and complete baseline remain
unchanged.

Verification in the lane:

- `lake build Solidity.Calculus.SoundStep Solidity.Evm.Correct Solidity.Typing.HeredRun`: pass, 68 jobs.
- `lake build Solidity.Examples.Tactics.PushSuffixRun`: pass, 48 jobs, 18 permanent kernel-checked examples.
- Combined reviewed rerun of the soundness dispatcher, 18 regressions, storage invariants, EVM proof and quotation: pass, 70 jobs (`/tmp/migration-native-push-reviewed-final.log`).
- Axiom inspection through a scratch Lake target: pass, 69 jobs. Both pair agreements, both arm soundness theorems, the soundness dispatcher, hereditary invariant preservation and EVM simulation use only `propext`, `Classical.choice`, `Quot.sound` (`/tmp/migration-native-push-reviewed-axioms-build.log`). The scratch source is retained outside the checkout.
- Orphan checking: pass, 302 reachable modules. `git diff --check`: pass.

The read-only finder and skeptic found no semantic or soundness defect. Their
regression import finding is fixed; failure examples now pin `halt? = some .revert`
exactly. The lane will be integrated only after the native table and guarded
replacement shape are checked.


### Guarded division/remainder push updates (isolated lane)

`Premise.guardedUpdates c U V` carries SolKey's outer conditional: the true
branch keeps both sequential updates; the false branch is `revert();` followed
by the original continuation. `pushOpStep` now uses it for DIV/MOD. ADD/SUB/MUL
and the discarded prefix/postfix statements keep the unguarded pair.

`Premise.GuardedUpdatesRuns` requires a condition that reads no callback,
`UpdatesRuns` on its true branch and a `TRes.Sim` of revert on its false branch.
General ordinary and callback soundness preserve those conditions. The zero
simulation is proved against the actual typed run for every numeric source and
starting storage; it permits the interpreter's existing capacity exhaustion,
never a successful or panicking zero-divisor run. At full capacity with a zero
divisor the guarded diamond premise is stronger than the execution meaning,
so this is a sound rule rather than a claim of exact halt equality.

Both sequent systems and their soundness proofs carry the guarded branch.
The ordinary strategy walker prunes a refuted branch and reconstructs its
proof with `closeFalse`; it keeps both updates in the true branch. Rule
selection, proof-tree selection and short `apply split` replay recognize the
new premise. Quotation retains its intermediate context. The printer emits
`if se != 0 then ({U} {V} ⟨[ ]⟩) else (⟨[ revert(); ]⟩)`.

The read-only finder and skeptic identified a notation dependency on binders
literally named `p` and `hp`. `Tm.zeroLike` now infers the numeric type from the
left term and finds its proof by type; alpha-renamed and fully concrete
roundtrip regressions cover the defect. Generic signed and unsigned guards,
actual DIV/MOD dispatcher shapes and a declaring/dropping intermediate scope
are checked in `Examples/Tactics/PushSuffixGuards.lean`. Native rule names and
SolKey-fragment coverage are still unregistered; full package validation and
main integration remain pending.

A broader targeted check also found the relocated `Storage.find_save_same`
still duplicated in `Calculus/TermLaws.lean`. The higher declaration is removed,
preserving the same theorem API at the lower storage layer. The native
statement printer now builds a normal member call expression, avoiding a
`.push()` lexer token conflict.


Reviewed guard verification:

- `lake build Solidity.Examples.Tactics.PushSuffixGuards Solidity.Examples.Tactics.PushSuffixRun Solidity.Calculus.ProvesDerive`: pass, 113 jobs (`/tmp/migration-native-push-guard-reviewed-final.log`). Includes six guard examples, two quotation/printer checks and the 18 native interpreter examples.
- Scratch axiom inspection: pass, 113 jobs (`/tmp/migration-native-push-guard-axioms.log`). General guarded ordinary/callback soundness, zero-divisor simulation, both proof-system soundness results and the statement dispatcher use only `propext`, `Classical.choice`, `Quot.sound`.
- Finder/skeptic follow-up accepts the typed-zero fix; the reserved local-name compile error is repaired and the new regressions pass. No remaining semantic defect was identified in this stage.
- Orphan checking: 303 reachable, zero orphaned; `git diff --check`: pass. The axiom probe is retained outside the checkout.

The target remains solkey `048a74de51a7cfb2cf497a043658424098f91e8e`,
verified unchanged and clean. This lane has not been integrated into main;
full rule-table/fragment coverage and full-package migration gates are pending.

### Native push rule registration (isolated lane)

The nine numeric push compound-assignment and discarded increment/decrement
rules now have their upstream names in `Taclet`, exact dispatcher replay,
coverage replay and origin rows. The shared RHS capture claims the existing
five general compound-assignment capture origins. Two complex-receiver
captures are explicitly `LeanTaclet` extensions, excluded from the SolKey
fragment. Fragment preservation and ordinary/guarded sequent conversion are
checked. This registers kernel correspondence; source elaboration and complete
reader/printer roundtrips remain pending.

The exclusive inventory is now 323 claimed, seven pending and 15 architectural
taclets; the separate Lean extension inventory has eight rules. The paper's
119 printed rows are unchanged. Sort annotations cover 130 of the 131
read-bearing taclets. The remaining unannotated rule is
`storagePushMemoryCopySource`.

The live sort check exposed a scanner omission: after recording an outer
read it skipped reads nested inside its arguments. The scanner now visits
those reads too, with two kernel-checked regressions for nested `find` and
legacy `valAt`. The existing `storageLocalPrimitivePushBind` annotation gains
its previously hidden two size reads; each new numeric suffix has five
annotated reads. This fixes accounting rather than suppressing a mismatch.

Reviewed verification:

- Native rule/coverage/sort targets: pass, 59 jobs (`/tmp/migration-native-push-coverage-sorts.log`).
- SolKey sequent conversion: pass, 74 jobs (`/tmp/migration-native-push-solkey-sequents.log`).
- `lake build Solidity.Examples.Tactics.PushSuffixRules`: pass, 89 jobs, including eleven permanent registration/admission examples (`/tmp/migration-native-push-rule-regressions.log`).
- Live `lake exe solkeycheck`: exit 1 for the single remaining memory-copy annotation gap; the new nine rows and corrected primitive-binding row agree (`/tmp/migration-native-push-sortcheck-reviewed.log`).
- Read-only finder and skeptic found no confirmed correspondence, soundness or admission defect. Their missing default import for the eleven new examples is fixed.
- Scratch axiom inspection: pass, 90 jobs; rule replay, coverage, callback validity and all nine numeric read-sort theorems use only the standard `propext`, `Classical.choice`, `Quot.sound` axioms (`/tmp/migration-native-push-registration-axioms.log`). The scratch source is retained outside the checkout.
- Orphan check: 304 reachable modules, zero orphaned; `git diff --check`: pass.

The full `lake build Solidity` with that default import failed at
`Examples/Tools.lean`'s `#check_rule_text` pin
(`/tmp/migration-native-push-registration-root.log`). The checker prints
165 of the 174 native constructors without scoped escapes: the nine new
suffix replacements still need their reader/printer completion. The Lean
extension count pin also expects six instead of eight. The check is retained;
its expected output is not weakened to accept escaped rule replacements.
Main integration, source support, complete rendering and full corpus migration
gates are pending.

### Native push rendering and typed text roundtrips (isolated lane)

The nine native replacement lines now write their literal arithmetic
operators, including `%`, rather than generic operator placeholders. The
native push reader recovers the numeric element type from the statement:
matching arithmetic on an indexed `find` uses that type, while `size + 1`
and `size - 1` remain unsigned. The recognizer covers indexed reads in these
native replacements; it does not itself enforce the canonical appended-slot
path. Dispatcher correspondence still kernel-checks the complete replacement.

The rule printer enables that typed arithmetic only while printing a native
push premise; the option is restored afterward. Outside this context, signed
arithmetic retains the existing escape boundary. `%` has term syntax and
precedence alongside multiplication/division and reads as checked `BinOp.mod`.

`Examples/Tactics/PushSuffixRules.lean` now prints each of the nine complete
rule judgements in compact and KeY long form, reparses the actual text,
elaborates it and checks definitional equality with the original judgement.
These eighteen roundtrips complement the strict no-scoped-escape rendering
inventory; they do not replace it. Its output pin is updated only after all
174 native, eight Lean-extension and three callback rules pass the inventory.

Verification:

- `lake build Solidity.Examples.Tactics.PushSuffixRules Solidity.Scratch.PushNativePrint`: pass, 95 jobs (`/tmp/migration-native-push-print-roundtrips.log`); eighteen typed text roundtrips, eleven constructor/admission regressions and the strict complete rendering inventory pass.
- `lake build Solidity`: pass, 286 jobs (`/tmp/migration-native-push-rendering-root.log`), including the updated `Examples/Tools.lean` pin and the default regression imports. This resolves the preceding library rendering failure.
- Read-only finder and skeptic found no confirmed defect in the nine native replacements or the typed reading/printing changes. The recognition scope and complementary rendering gates are recorded above.

Source elaboration, full TestSuite/corpus gates and main integration remain
pending. The raw expression type represents function calls by name and cannot
represent an indexed receiver's `push()` lvalue. Source integration therefore
needs explicit raw push suffix statements corresponding to the native typed
statements, plus the source grammar and traversal/elaboration cases.

### Push suffixes through compiled Solidity source (isolated lane)

`RawStmt.pushOpAssign` and `RawStmt.pushIncDec` retain the receiver separately
from the value expression. Both `.push()` token spellings and ordinary dotted
method-call spellings parse, including indexed receivers and unparenthesized
postfix forms. The elaborator emits the existing numeric native statements;
compound RHS effects run first, and a value read before an effectful receiver
is captured. Unchecked push arithmetic and returned increment/decrement values
remain unsupported rather than acquiring checked/discarded semantics.

`tests/solc/PushSuffixes.sol` is compiled by the pinned solc 0.8.34, with AST
hash `0x1afe1b8baa8f36f1`. The default-imported
`Examples/Tactics/PushSuffixSource.lean` pins all 22 functions as elaborated
and checks 22 kernel propositions. They cover all nine signed forms,
unsigned success/underflow, all indexed forms, RHS effects before an index
increment, a pure RHS captured before a receiver call, false assertions and
exact zero-divisor/underflow reverts. A nonzero primitive shadow is explicitly
shown to fail the tight entry check; its run tests the reset on arbitrary
typed storage, not a claim that it is valid public entry storage.

The finder and skeptic confirmed a source-order defect during review:
fresh-shaped user names such as `se1` were treated as already captured
temporaries. Source import now supplies roots, parameters and recursive raw
read/declaration names through `ElabScope.mutableFreshNames`, reserves capture
indices beyond them and retains the provenance across inlined calls. A state
root is always mutable in either reading. Written derivations retain their
special convention for fresh-shaped locals. Positive and false-result
regressions cover source locals, parameters, state variables and ordinary
binary arithmetic; both reviewers accept the repair.

Verification and remaining integration work:

- `lake build Solidity.Syntax.Elab`: pass, eight jobs (`/tmp/migration-native-push-source-elab-1.log`).
- `lake build Solidity.Syntax.Splice`: pass, eleven jobs (`/tmp/migration-native-push-source-capture-scope.log`).
- Source and native-rule targets after the provenance repair: pass, 139 jobs (`/tmp/migration-native-push-source-fresh-capture.log`), including the 22 source checks and eighteen typed text roundtrips.
- The first full runner passed its default build (294 jobs) but stopped at the stale TestSuite import pin (`/tmp/migration-native-push-source-run-lean.log`): four previously unsupported upstream functions now elaborate, making 531 elaborated and 17 unsupported of 551 functions. That import pin is updated, and scoped obligations increase from 497 to 501.
- Three new upstream obligations close with the native strategy in `TestSuite/Derived16.lean`. The signed three-push obligation remains a required pending proof. Its twelve residual leaves exceed `Seq.closeSize` before elimination, with storage depth seven (`/tmp/migration-native-push-signed-size-4.log`); no limit is raised. An attempted full reduction and bounded leaf search timed out and are retained only as outside-checkout prototypes.
- The fresh full runner passed the default build (294 jobs) and imported TestSuite (146 jobs), including the three new derivations and the verified report pin of 489 derived, twelve pending and 50 other (`/tmp/migration-native-push-source-reviewed-run-lean.log`). It exits 1 only for the remaining `storagePushMemoryCopySource` annotation gap.
- The regenerated 723-row corpus has 489 derived, twelve pending, 49 unsupported, 70 concrete proofs, 100 unported, one excluded and two skipped. The parity audit passes with 23 trust-checked modules (`/tmp/migration-native-push-source-reviewed-parity.log`). Generation uses the frozen snapshot so its revision metadata stays `048a74de51`.
- The enlarged obligation table exposed an elaboration-depth failure in its last corpus corollary. Explicit program arguments and tactic wrappers did not fix it; those attempts are removed. Inspection of Lean's prelude (`Init.Prelude`) confirms the default depth is 512. The generated corpus uses the minimal passing local `maxRecDepth` of 513, retaining the table representation and all heartbeat/search limits. `lake build SolidityCorpus` passes, 154 jobs (`/tmp/migration-native-push-source-corpus-depth513.log`). The strict live corpus re-probe also passes (`/tmp/migration-native-push-source-corpus-depth513-final.log`).
- `SOLKEY_ROOT=/home/guilherme/projects/solkey node --test scripts/test-solidity.test.mjs scripts/solkey-migration.test.mjs`: all 25 pass, zero skipped (`/tmp/migration-native-push-source-tool-regressions-final.log`). The explicit root is necessary because the isolated worktree has no sibling SolKey checkout.
- The final read-only finder and skeptic accepted the three new proofs, the unchanged corollary bridge and the documented remaining boundaries. Main-checkout integration remains pending.

### Push milestone integrated into the main checkout

The reviewed lane changes are integrated into the main working tree, with
all 70 changed/new files checked byte-for-byte against the lane before the
final checks. No commit or push was made. The remaining memory-copy sort row
now records its two old-size reads; the annotation table covers all 131
read-bearing taclets. This does not claim the native memory-copy rule: the
seven correspondence gaps in `migrationPendingTaclets` remain pending.

Integration exposed a stale generated executable after Lake restored a
newer artifact from its shared cache. Lake 4.24's executable restoration
copies only when the destination is absent. `scripts/check-solkey.sh` now
removes only its generated checker executable before building, so the check
runs the current artifact. The first main run's ten annotation failures
came from that old executable; restoring the current one reduced them to
the single missing memory-copy row before that row was added.

Verification in the main checkout:

- `./run-lean.sh`: exit 0; default build 294 jobs, TestSuite 146 jobs, and zero sort mismatches (345 taclets, 131 read-bearing, 131 annotated), `/tmp/migration-native-push-main-reviewed-run-lean.log`.
- `./scripts/check-corpus.sh`: pass, 723 rows, `/tmp/migration-native-push-main-corpus.log`.
- `./scripts/check-testsuite.sh`: pass; 23 trust-checked modules and the unchanged report of 489 derived, twelve pending and 50 other, `/tmp/migration-native-push-main-parity.log`.
- Lean diagnostics for both changed sort-check files: no errors. `node scripts/check-orphans.mjs`: 306 reachable modules, zero orphans; `git diff --check`: pass.
- Read-only finder and skeptic accepted the exact two-read annotation and generated-file refresh. Their accounting correction is applied: 131 rows comprise 105 value-bearing rows and 26 other rows.

Remaining work includes the seven native correspondence gaps, the signed
three-push proof and the eleven earlier pending TestSuite proofs, alongside
the broader source/import and corpus gaps. Successful checks at this
milestone do not establish completion of the migration.

### Native primitive push receiver capture

The typed `Stmt.assignLocalPush` now retains a complex receiver. Its old
simple-receiver premise came from the original implementation's missing
upstream rule, not from an elaboration-speed optimization (`994582a3`).
`assignLocalPushStep` uses the existing update for a simple receiver and
otherwise binds the path once to a fresh storage alias, then appends and
assigns through that alias. The source elaborator no longer inserts that
alias before emitting the statement, so the calculus exposes the native
`localValuePush_unfold_leftFstReceiver` step.

The interpreter is unchanged. Before integration, a scratch proof established
the pushed-state equation for the receiver and target local. The integrated
`TRun.assignLocalPush_pushT`, `sound_assignLocalPushCapture` and
`assignLocalPushStep_sound` retain ordinary failure and exhaustion behavior
in every typed state, with no additional hypothesis. The simple and complex
side conditions are disjoint; capture produces a simple alias, preventing a
capture loop. Dispatcher correspondence and coverage replay pass diagnostics.

The native inventory becomes 175 constructors, with 324 upstream taclets
claimed, six pending and fifteen architectural exceptions. The paper's 119
printed rows stay unchanged; this additional native rule is outside that
table. Sort annotations remain complete at 131 read-bearing rows.

Both read-only reviewers accepted the evaluation order, typed local shift,
constructor-arity updates and applicability boundary. The source fixture now
also checks `y = matrix[y + 0].push()` with initial `y = 1`, with a false
assertion that would hold if the receiver incorrectly read the new zero.
The pinned solc 0.8.34 produces fixture hash `0x22918c5980ba66a2`.
Native rule-name pins cover both modalities and the simple update, and all
ten native push rule judgements have typed roundtrips in both printed forms.

An indexed path is complex even when its index is a literal; storage aliases
and roots are simple. The first full runner caught an incorrect literal-index
test pin, which was corrected to test the alias case without changing the
dispatcher.

Final verification:

- `./run-lean.sh`: exit 0; default library 294 jobs, TestSuite 146 jobs and zero sort mismatches, `/tmp/migration-primitive-push-capture-reviewed-run-lean.log`.
- All 25 source-runner and migration-tool regressions pass, zero skipped, `/tmp/migration-primitive-push-capture-tools.log`. The old-target source obligation proves; both false source assertions stay pending.
- `./scripts/check-corpus.sh` and `./scripts/check-testsuite.sh`: pass, `/tmp/migration-primitive-push-capture-corpus.log` and `/tmp/migration-primitive-push-capture-parity.log`. Counts remain 723 corpus rows and 489 derived/twelve pending TestSuite obligations.
- The pushed-run, capture and step-soundness proofs use only `propext`, `Classical.choice` and `Quot.sound`. The new correspondence and coverage proofs use only `propext`; global `Proves.sound` retains the same standard three axioms, `/tmp/migration-primitive-push-capture-axioms.log`.
- `node scripts/check-orphans.mjs`: 306 reachable modules, zero orphans. `git diff --check`: pass. The documentation-path check retains the six pre-existing missing vendored LeanTeX references.
- Final read-only review accepted the corrected map, compiled fixture hash, old-target regression pair and simple/complex rule pins. No confirmed semantic or scope defect remains in this milestone.

The six native gaps, signed three-push proof and eleven earlier pending
TestSuite proofs remain required work; this milestone does not complete the
migration.

### Native complex push-source capture

The dispatcher now exposes the upstream primitive and reference source
captures. A complex primitive storage read is bound to a value named
`source`; a complex reference source is bound to a storage alias of that
name before copying. Direct reference copy requires both paths simple.
The general expression capture excludes complex storage reads, so the three
source cases have disjoint side conditions. Capturing a source makes it
simple and cannot repeat the same capture. Receiver capture still precedes
source capture.

The interpreter is unchanged. `sound_pushReferenceCapture` proves agreement
in every typed state, including source resolution failure; primitive capture
uses the existing value-capture soundness theorem. The schema reader retains
typed primitive paths and the matcher checks the complete typed find after
seeding its path metavariable. Dispatcher correspondence and the recorded
coverage replay are kernel checked. The inventory is now 177 native
constructors, 326 claimed upstream taclets, four pending and fifteen
architectural exceptions. The 119 printed paper rows and 131 sort annotations
are unchanged.

The compiled ten-function `PushSources.sol` fixture checks primitive and field
reads, independent reference copies, self-copy, source effects, complex
receivers, invalid source indices and two deliberately false observations.
It uses the existing `Token` layout; this does not add arbitrary user-defined
struct layouts. Its solc 0.8.34 hash is `0xeda400449f8aace8`. Both numbered
capture chains replay through the ordinary `sol_chain`, and all twelve native
push judgements have typed text roundtrips in both printed forms.

Read-only review found that the new `source` prefix did not read back as a
fresh variable and could hide a similarly named root. The parser now retains
its identity. Freshness reserves roots at the calculus's default and fixed
prefixes, so root `source9` makes the capture `source10`. An initial overly
broad reservation of every numeric root renamed unrelated captures and broke
existing chains; narrowing it restores ordinary `flag2`/`triple2` behavior.
Custom display prefixes must avoid roots manually; `FreshNames.clashes`
checks explicit table aliases only. The freshness certificate remains an
application of `Fml.fresh_eq` with kernel-checked equalities.

Verification:

- The fixture's kernel execution checks, both capture chains and existing storage chains build in 142 jobs (`/tmp/migration-push-source-root-prefix-check.log`). Lean diagnostics for the fixture and the new `Examples/ProofTree.lean` suggestion pin report no errors.
- `./run-lean.sh`: exit 0, default library 296 jobs, TestSuite 147 jobs and zero sort mismatches (`/tmp/migration-push-source-final-run-lean.log`), including the printed suggestion pin. The initial broad-root version failed; after repair a separate run exited 135 in unchanged `RuleKit` without a source diagnostic. That module passed diagnostics and both complete retries passed.
- The ten-function source proof probe has eight proved box obligations and two deliberately open false assertions, with no errors (`/tmp/migration-push-source-proof-probe.json`). Kernel executions refute both false assertions and separately check the invalid-source revert. A source-runner regression pins these outcomes.
- The existing 25 source-runner/migration-tool regressions pass with zero skipped (`/tmp/migration-push-source-tools.log`); the added source-capture regression passes separately (`/tmp/migration-push-source-new-regression.log`).
- `./scripts/check-corpus.sh` and `./scripts/check-testsuite.sh`: pass (`/tmp/migration-push-source-corpus.log`, `/tmp/migration-push-source-parity.log`). Counts remain 723 corpus rows and 489 derived/twelve pending TestSuite obligations; 23 proof modules pass the trust audit.
- Capture and global soundness use only `propext`, `Classical.choice` and `Quot.sound`; correspondence, coverage and freshness use only `propext` (`/tmp/migration-push-source-axioms.log`).
- `node scripts/check-orphans.mjs`: 308 reachable modules, zero orphans. `git diff --check`: pass. The documentation-path check retains six pre-existing missing vendored LeanTeX references.
- Final read-only finder and skeptic reviews accepted the typed capture rules, naming repair, replay pins and verification claims. No confirmed defect remains in this milestone.

The remaining four native gaps, twelve TestSuite proofs and broader import and
corpus gaps remain required migration work.

### Native memory-to-storage push

`Src.copyMem` carries a typed memory path as the source of an existing
`Stmt.push`. The run resolves the receiver once, snapshots the memory value
with `MVal.copyMToSt`, then appends the stripped value and advances the length.
The lazy update uses the existing `push` and `copyMem` symbols. A scratch
prototype proved agreement in every typed state before integration; the
generic lowering and push-update agreement now include the new source.
Weakening, termination, no-panic, printing, both quoters and hereditary
storage invariants have their corresponding cases. No dependency or trust
assumption is added.

This fixes an actual elaboration bug. Previously memory push expanded to a
default append and an assignment whose receiver was evaluated again. With
two empty cube rows, `cube[cube[0].length].push(row)` then selected `cube[1]`
for its second lookup and reverted. The new source succeeds. The old
expansion remains a kernel-checked refutation beside that successful source;
the false receiver assertion now reaches `assert` and panics. solc 0.8.34's
IR computes one target slot and supplies it to its memory-array push helper,
matching this execution order.

The native `storagePushMemoryCopySource` has the upstream simple receiver and
memory-variable find and three-argument `copyMem(mtSt, memory, mv)` replacement.
Complex receivers use the existing generic upstream receiver capture. A
complex memory source uses the explicit Lean-only `pushMemorySourceCapture`;
an embedded memory snapshot in an internal storage assignment uses
`storageMemorySourceSave`. These two additional Lean cases are excluded from
the SolKey fragment and its admission facts. Ordinary memory-to-storage
assignments still elaborate to `Stmt.assignFromMem`. The EVM fragment
conservatively excludes memory-source pushes and assignments.

The inventory becomes 178 native constructors, 327 claimed upstream taclets,
three pending, fifteen architectural exceptions and ten Lean constructors.
The paper's 119 printed rows stay unchanged; the native memory-copy row is
in the KeY tier outside that table. All thirteen native push judgements have
typed roundtrips in both printed forms. Dispatcher coverage was generated
under the existing bounds in 45,437 ms, then stored as a replay; it is not
searched on each check.

The nine-function compiled `MemoryPush.sol` fixture has hash
`0x0477c52e82f8eb49`. It covers independent array and struct copies, a
recycled slot, the changing receiver, complex memory paths, three false
observations and an invalid memory index. All initial-state kernel checks
pass; the source proof probe has six proved box obligations, three pending
false assertions and zero errors. Review identified the initially missing
complex-memory cases, which were added and kernel checked.

Verification:

- The frozen `./run-lean.sh` passes: default library 297 jobs, TestSuite 147 jobs, and 345 taclets with all 131 read-bearing annotations matching (`/tmp/migration-memory-push-pinned-run-lean.log`). `SOLKEY_RULES` points to the immutable snapshot because the sibling checkout acquired unrelated uncommitted changes during this milestone.
- All 27 source-runner and migration-tool regressions pass, with zero skipped (`/tmp/migration-memory-push-tools.log`, 333 seconds). The initial restricted-cache invocation failed at file level; the final shared-cache run passes.
- The frozen corpus and TestSuite parity checks pass (`/tmp/migration-memory-push-corpus.log`, `/tmp/migration-memory-push-pinned-parity.log`): 723 rows, 489 derived and twelve pending TestSuite obligations, with 23 proof modules audited.
- Lean diagnostics for `MemoryPush.lean` and the new `ProofTree.lean` suggestion pin report no errors. The source probe has six proved box obligations, three false assertions pending and zero errors (`/tmp/migration-memory-push-proof-probe.json`).
- Lowering, capture, push-step, hereditary-invariant and global soundness proofs use only `propext`, `Classical.choice` and `Quot.sound`; correspondence and coverage use only `propext` (`/tmp/migration-memory-push-axioms.log`). Its cache-save warning does not affect the kernel checks.
- `node scripts/check-orphans.mjs`: 309 reachable modules, zero orphans. `git diff --check`: pass. The documentation-path check retains six pre-existing missing vendored LeanTeX references.
- Final read-only finder and skeptic reviews accepted the semantics, native rule shape, explicit Lean-only boundaries and expanded complex-memory regressions. Their confirmed stale eight-rule prose count is corrected to ten.

Earlier full-run attempts exposed stale printer and missing conservative EVM
cases, now repaired. One attempt failed in the existing void-call example;
direct parsing and elaboration succeeded, and the unchanged splice module
passed diagnostics, its isolated build and the final complete runner. No
source fix is claimed for that transient failure.

Three call-receiver taclets, twelve TestSuite proofs and wider source/import
gaps remain required work. This milestone does not complete the migration.

### Full source-runner function tables

The uniform listing exposed a code-generation failure before any TestSuite
proof search: testing mode retains all callable declarations, while the
ordinary import retains only those needed by calls. The resulting large
contract literal exceeded Lean's code-generator recursion depth. A minimal
empty-function table did not reproduce it; the real TestSuite literal did.

The importer now compiles large list fields in segments of at most 64 cells,
retaining each original head and its order. A whole-contract equality is
checked by `Eq.refl` in the kernel before the compiled contract is defined.
Fresh macro-scoped names keep helpers separate from source declarations.
Small tables retain their original expressions. Scoped programs remain
uncompiled, preserving the earlier import performance decision; no limit or
dependency is raised.

The scratch prototype compiles the real 550-entry callable table in about two
seconds. The frozen source-runner listing retains all 551 TestSuite function
rows, with 501 ready obligations, seventeen unsupported, thirty internal,
two skipped and one excluded. The source also has two PairLib rows, retained
separately. The added full-TestSuite listing regression passes in 23 seconds
(`/tmp/migration-import-segments-regression.log`).

The full frozen runner passes: library 297 jobs, TestSuite 147 jobs and all
131 sort annotations (`/tmp/migration-import-segments-run-lean.log`). The
parity/trust gate passes with the same 489 derived/twelve pending obligations.
Read-only finder and skeptic reviews accepted segmentation, its boundary
cases, generated names and the kernel equality certificate; no confirmed
defect remains. The full 28-test tool run passed 27 tests; memory push hit
the existing 120-second subprocess limit while the baseline was running
(`/tmp/migration-import-segments-tools.log`). It had taken 105 seconds in the
earlier successful run. Splitting that regression into three-function proof
batches passes all nine expected outcomes in 118 seconds total, under the
same per-process and proof limits
(`/tmp/migration-import-segments-memory-batched.log`). Thus all 28 scenarios
are checked across the full and focused runs; the full run's timeout is
retained, not reclassified as proof-open.

The frozen corpus passes (`/tmp/migration-import-segments-corpus.log`), with
309 reachable modules, no orphans and a clean `git diff --check`. The
documentation-path gate still reports the six pre-existing missing vendored
LeanTeX references. The real-table prototype's whole-contract certificate
depends on no axioms (`/tmp/migration-import-segments-certificate.log`). Final
finder and skeptic verification reviews accepted the distinction between the
full-run timeout and focused batched success.

The uniform listing and proof baseline both finished all 112 sources in the
isolated `migration-baseline-20261015` worktree. All 340 captured implementation
files match the final hash audit. The reports are retained as
`tests/migration/listing-baseline-current.json`, `proof-baseline-current.json`,
its `.summary.json` and `.implementation.json`, and `comparison-current.json`.
This fixed implementation precedes the storage-return changes below.

The proof report records 872 proved, 199 pending, 254 unsupported, 157 internal,
25 skipped, three excluded and thirteen deliberate compiler rejections. It
also retains 33 error rows, 52 not-run rows and 28 source/contract errors.
Completing the source traversal is not a passing migration gate. Comparison
against the existing expectations fails: twelve unaccounted imports, 531
changed outcomes, three missing rows and 28 errors. Neither the existing
expectations nor failures are automatically accepted by this refresh.

Expectations also need semantic review. Seven box cases in the upstream
`unprovable/Unprovable.sol` prove in this model: checked overflow/underflow
reverts before `assert(false)`. That source explicitly calls them unprovable
under SolKey's unbounded integers. These are candidates for documented
checked-arithmetic deviations, not evidence that every changed outcome is
acceptable. The three missing PiggyBank rows correspond to a recorded
`lake exited 135` process failure and require a separate rerun; no code-level
cause is established by this report.

### Typed storage-return foundation

`CallRet.storage` adds a single typed storage return. Entry creates an unset
alias; return exports the callee's pointer by identity, restores caller locals
over any heap growth, and retains the callee's global effects. The general
inlining and argument-capture agreement proofs cover failures and allocation.
The specification rule quantifies the exported pointer; its existing
`Prog.within` restriction still excludes alias-binding bodies, so this does
not claim unrestricted function-contract support.

The solc reader retains the return's `storage` location. Function-return
parameters use their own grammar, leaving external try/catch parameter
locations unchanged. Source declarations and rebinding consume the exported
alias. The return-type representation has no map-free or allocation premise.
EVM compilation explicitly excludes this new return form. No dependencies,
proof limits or axioms are added.

Pinned upstream `ExpandFunctionBody` declares a storage return with an unset
default and preserves its data location; `internalCallExpand` therefore keeps
its existing correspondence. Direct `f().push()`, `f().push(e)` and `f().pop()`
remain explicit unsupported imports and all three native taclets remain pending.
They require a receiver AST and its own capture rule, rather than frontend
hoisting that would conceal the correspondence gap.

`StorageReturns.sol` and its compiler-pinned AST retain fourteen rows: five
helpers, six supported public cases and three unsupported call receivers.
Kernel execution checks cover identity and getter-once effects, rebinding,
an indexed return with a non-simple argument, caller memory over callee heap
growth, callee reversion and a false independent-copy claim. These are
initial-state execution checks, separately from universal call soundness.

Read-only finder and skeptic reviews found two printer omissions. Printing a
single exported call as a source declaration created an extra alias on reread;
printing the call and binding separately exposed an implicit fresh name in
`#solc_show`. Both expression and string printers now combine a call with its
following alias binding, and bare calls retain their single exported alias.
Chain text uses the same combination. Four programs round-trip through both
printer paths and the actual elaborator with identical typed expressions.
The corrected paths and skip counts were independently reviewed.

The final finder also found the open-tail fallback (`ppPartsS`) omitted that
combination. It now merges adjacent storage calls and bindings too. Four
additional checks send actual prefixes and a typed schematic continuation
through that fallback, preserve the continuation's identity, and re-elaborate
the prefix at its original program type with identical expressions. These
check prefix/continuation preservation, not arbitrary whole-formula roundtrips.

Per-file Lean diagnostics and all six execution/eight replay checks pass.
The new inlining, argument-capture, storage-contract and general call-contract
theorems use only `propext`, `Classical.choice` and `Quot.sound`. The final
audit also checks `Stmt.sound` and `Proves.sound` with the same axiom set
(`/tmp/migration-storage-returns-axioms.log`).

The focused compiled-source runner also passes all fourteen expected outcomes:
five internal helpers, five proved public obligations, one false assertion
pending and three unsupported call receivers (28 seconds,
`/tmp/migration-storage-returns-source-probe.log`). The ordinary frozen
TestSuite import now reports 532 elaborated and sixteen unsupported, with
`valuesRef` retained as internal. Its caller remains unsupported. The public
489 derived/twelve pending obligations and 723-row corpus are unchanged;
their regenerated pins retain the new caller diagnostic.

Final verification after all confirmed printer and coverage fixes:

- `./run-lean.sh` with the frozen `solidityProgramRules.key`: 298 default
  jobs, 147 TestSuite jobs, 345 taclets and all 131 read-bearing annotations
  pass (`/tmp/migration-storage-returns-final-verified-run-lean.log`). Earlier
  attempts exposed missing exhaustive coverage/fragment cases and stale
  diagnostic pins, now fixed. A directory supplied as the sort-check path
  caused a configuration error; the final run uses the required file path.
- All 29 source-runner/migration-tool tests pass, zero skipped, in 321 seconds
  (`/tmp/migration-storage-returns-final-tools.log`). This is a complete run
  after the open-tail fix, not a combination of partial runs.
- Frozen corpus and TestSuite parity/trust audits pass: 723 rows, 489 derived
  and twelve pending public TestSuite obligations; 23 proof modules audited
  (`/tmp/migration-storage-returns-corpus.log`,
  `/tmp/migration-storage-returns-parity.log`).
- All 310 modules are reachable, with no orphans. `git diff --check` passes.
  The documentation-path gate retains the six pre-existing missing vendored
  LeanTeX references.
- Final read-only finder and skeptic reviews confirm the alias/export
  semantics, explicit EVM/function-contract boundaries, closed and open-tail
  printer fixes, source-outcome pins and exhaustive call/fragment cases. No
  further confirmed defect remains in this foundation.

This milestone does not implement the three native call-receiver taclets or
discharge the wider migration baseline. The historical baseline retains its
failures and is labeled before these storage-return changes. Its finished
temporary worktree has been removed; the unrelated clean-tail worktree and
sibling SolKey checkout are untouched. No commit or push was made.

### Native call-receiver semantics: integration in progress

`Stmt.callReceiver` retains the getter and a typed `ReceiverOp` until its
own strategy capture. The runtime calls the getter once, exports its storage
alias, then reads the push source and performs the array operation. It removes
the temporary alias while preserving caller locals and callee heap growth.
`callReceiverCapture` adds the explicit `sp` binding of the native replacement;
both that binding and the getter's hidden return alias end with the statement.
No frontend path emits this constructor yet.

The frozen solc 0.8.34 IR probe runs the getter before a storage-reading push
argument and before `calls++`. The current operand type contains pure typed
sources only. Effectful operand captures still need a representation that
defers those effects until after the getter; ordinary argument hoisting before
the getter would violate that ordering. The probe is retained at
`/tmp/migration-call-receiver-order.sol` and
`/tmp/migration-call-receiver-order.ir`.

Per-file diagnostics pass for the typed statement/quoter/runtime,
`NoPanic`, `RunWk`, `RunFuel`, `RunFrame`, `Semantics/Callback`, `HeredRun`,
`Blocks`, `Step`, `SoundCalls`, `SoundStep` and `StmtSound`. The preservation
proofs cover assertion detection, extra caller locals, fuel approximation and
hereditary storage invariants. The callback relation continues the getter's
callback outcome and propagates halts or a violated invariant before any array
operation; deterministic inclusion and callback-free agreement check too.
Function-contract frames still exclude this mutating receiver form, consistently
with their existing exclusion of ordinary push/pop.

`CallReceiver.callReceiver_capture_run` proves the integrated capture agrees
with the integrated statement for arbitrary getters and typed states, including
failure, unset aliases, memory-copy sources and heap growth. Its ordinary rule
soundness is integrated into `Stmt.stepSound`; `Stmt.sound` passes its existing
axiom guard. Explicit axiom checks on the capture agreement and receiver rule
soundness report only `propext`, `Classical.choice` and `Quot.sound`.
The scratch prototype retains eight kernel execution checks, including a new
check of the integrated default push, plus the universal bridges to the actual
constructor and capture definition.

This is a semantic milestone, not a completed native taclet port. The three
native taclets remain pending in the inventory. Their schema/constructor
registration, coverage and callback capture correspondence, remaining quoters
and printers, source elaboration and effectful operands are unfinished. A full
repository gate has not been run for this partial integration; downstream
exhaustive tables still need its constructor. The previous section's passing
full gates apply to the earlier storage-return foundation only.

Read-only finder and skeptic reviews accept this semantic foundation with no
confirmed defect. Both checked the actual capture bridge, removal of both
temporary aliases, arbitrary getter failures and heap growth, caller-local
weakening, fuel approximation, hereditary invariants, callback halt/violation
propagation and freshness of the hidden return/argument/body names. Neither
review ran builds or the Lean server. Neither review accepts native registration,
frontend or printer completion. The axiom output and prototype are retained in
`/tmp/migration-call-receiver-semantic-axioms.log` and
`/tmp/migration-call-receiver-semantic-prototype.lean`.

### Native call-receiver registration and source integration

The three `storage{PushValue,Push,Pop}_unfold_leftCallReceiver` taclets now
have native constructors, exact `toStep` replay proofs and exhaustive strategy
coverage. Their schema parser checks the same getter, operation, operand and
fresh receiver in the find and replacement. Negative pins reject a changed
getter or operation. The generic printer displays upstream's explicit
`aliasType storage sp = fc; sp.push(e);` capture rather than exposing the
constructor tree. The inventory now has 181 native constructors, 330 claimed
upstream names, zero pending names and fifteen architectural exceptions. The
three new constructors are in the KeY tier; the paper's printed rule list is
unchanged.

The elaborator retains direct `f().push()`, `f().push(e)` and `f().pop()` as
`Stmt.callReceiver`. Getter arguments are captured before the call; the typed
push source is read after it. An operand whose hoisting produces effects is
explicitly rejected until a deferred typed computation can represent those
effects after the getter. This is a required gap even though all three rule
names are registered. Function-contract and EVM exclusions remain explicit.

Both expression and string printers round-trip eight storage-return programs
with identical typed expressions. Eight open-tail prefix checks preserve the
schematic continuation too. The expanded seventeen-function `StorageReturns`
fixture has sixteen elaborated rows and one explicitly unsupported effectful
operand. Eleven initial-state execution checks cover getter-before-source
evaluation and refute the opposite order. Compiled proof-runner expectations
also require that true order claim to prove, the false claim to stay open and
the effectful operand to retain its precise unsupported diagnostic. The native
TestSuite `storagePushPopCallReceiver.proved` is a kernel-checked `sol_prove`
derivation, independently of those execution checks. The verified report now
records 490 derived, twelve pending and 49 other functions; the import has 533
elaborated and fifteen unsupported rows, and declares 502 scoped obligations.
Regeneration from the frozen snapshot changes the caller's corpus row from
unsupported to derived: 723 rows, with 490 derived, twelve pending, 48
unsupported, 70 concrete proofs, 100 unported, one excluded and two skipped.

Per-file Lean diagnostics pass for registration, coverage, both quoters and
printers, fragment preservation, explicit EVM boundaries, frontend, examples,
the new derivation and its report pin. Final verification:

- `./run-lean.sh` with the frozen rule file passes: 298 default jobs, 147
  TestSuite jobs, 345 parsed taclets and all 131 read-bearing annotations
  (`/tmp/migration-call-receiver-run-lean.log`). The first default build found
  the stale 178-rule rendering pin; its corrected 181-rule pin checks every
  native rule's printed line.
- All 29 source-runner and migration-tool tests pass, zero skipped, in 336.5
  seconds (`/tmp/migration-call-receiver-tools.log`). The expanded source
  fixture proves the true getter-order claim, retains the false claim as open
  and checks the exact unsupported-effect diagnostic.
- Frozen corpus and TestSuite parity/trust gates pass
  (`/tmp/migration-call-receiver-corpus.log`,
  `/tmp/migration-call-receiver-parity.log`). The audit checks 23 proof modules
  and accounts for all 514 public/external functions plus two skips. No
  expectation is changed to accept a new unsupported case.
- The added scoped obligation grows the indexed table from 501 to 502 entries.
  The initial corpus build reached its final corollary's recursion-depth limit
  at 513 (`/tmp/migration-call-receiver-corpus-depth513-failure.log`). The
  generator retains the observed twelve-frame allowance above the table
  length, with the ordinary default as a floor; this is not a universal depth
  bound for future term shapes. At the current 502 entries, 514 passes
  per-file diagnostics and the complete corpus gate. No heartbeat or
  search budget changes. The earlier build and 29-test results remain valid;
  the changed generator is checked by the rerun corpus/parity gates.
- All 310 modules are reachable with no orphans. Temporary prototypes were
  preserved outside the source tree in
  `/tmp/migration-call-receiver-scratch-20261015/`. `git diff --check` passes.
  The documentation-path check still reports the same six missing vendored
  LeanTeX files.

Read-only finder and skeptic reviews accept the native registration, source
ordering, conservative boundaries and expanded regressions. Their confirmed
stale counts in the authority rule map and module map are corrected. The
generator review accepts the empirical lookup allowance with the qualification
above. `AGENTS.md` now points its sort-check status to the verified frozen pin.
Neither
review ran builds or the Lean server; the command evidence above is separate.

This milestone does not discharge effectful operands, callback capture
correspondence, the twelve pending TestSuite proofs or the wider source and
storage-theory gaps. The uniform historical baseline remains labeled before
storage-return changes and retains its failures; its expectations have not
been silently repinned. The migration remains in progress. No commit or push
was made.

### Deferred-operand foundation

`Solidity/Semantics/DeferredSource.lean` now retains an operand as an intrinsic
`Prog C Γ Δ` prefix and a `Src C Δ T`. Evaluation runs the prefix, snapshots
the source and drops its temporary locals while preserving caller writes and
heap growth. General weakening laws preserve additional caller locals,
including captured storage aliases. Programs remain interpreted; this does
not undo the earlier uncompiled-program decision (`ec01aeb7`).

`DeferredSource.callProgram_sound` proves agreement with an actual typed
program containing the getter call, explicit storage-alias declaration and
scoped prefix followed by the existing push statement. It quantifies over
arbitrary typed getter bodies, arguments, operand prefixes and entry states.
The returned alias is validated before operand effects, so an unset getter
result reverts before a panicking prefix can execute. This is ordinary-run
agreement, not callback or calculus correspondence.

`Solidity/Examples/Tactics/DeferredSource.lean` adds twenty-one kernel execution
checks for pre/post-increment, calls, storage and memory snapshots, prefix and
getter failures, caller-local preservation, allocation and combined getter /
operand heap growth. Both modules are imported by the default root. The
earlier prototype, including the accepted three-family mutual-inductive
experiment, is preserved in `/tmp/migration-deferred-source-reviewed.lean`.

Verification: both modules and the root have clean per-file diagnostics.
`./run-lean.sh` passes with 300 default jobs, 147 TestSuite jobs and all 345
taclets / 131 read-bearing annotations matching the frozen snapshot
(`/tmp/migration-deferred-foundation-run-lean-verified.log`). The first
sandboxed attempt stopped at Lake's read-only shared artifact cache; the
verified rerun has cache access. Axiom audits of `Operand.run_wk`,
`expandedPush_atAlias` and `callProgram_sound` use only `propext`,
`Classical.choice` and `Quot.sound`
(`/tmp/migration-deferred-foundation-axioms.log`). The module graph has 312
reachable modules and zero orphans, and `git diff --check` passes. The
documentation-path check retains the same six missing vendored LeanTeX paths.

Native `ReceiverOp`, source elaboration and printers do not yet consume this
foundation: `f().push(i++)` retains its explicit unsupported diagnostic. An
arbitrary prefix can contain callbacks, so callback integration must execute
it through `ExecP`, propagating halts and invariant violations. The migration
counts and wider outstanding gaps remain those of the preceding milestone.

Read-only finder and skeptic reviews accept the promoted foundation and all
twenty-one retained checks, with no confirmed defect. Neither ran builds or
the Lean server. The `Syntax.Elab` dependency supplies `Prog.join`; this is
an upper-layer laws module, not a module the low-level syntax or interpreter
can import directly. Native integration must keep its representation and
interpreter below these laws. No commit or push was made.

### Deferred capture with callback prefixes

`Solidity/Semantics/DeferredCallback.lean` now gives an exact relational
decomposition of the explicit getter/capture/prefix/push program. Generic
sequence, singleton and block laws connect actual `ExecP`/`ExecS` derivations;
`pushBlock_iff` executes an arbitrary operand prefix through `ExecP`, then
runs only its final push deterministically. `callProgram_iff` adds the
getter's callback execution and alias validation, in both directions.
`execCall_run` admits the ordinary deferred run unless a callback exit breaks
the invariant. Halts and invariant violations suppress later stages, and
scope ends retain the composed heap extension.

The scope is explicit: `ExecAfterGetter` already carries the two hidden
aliases of the captured program. These laws do not yet compare that with an
independent direct callback execution carrying only the returned alias.
That native capture correspondence needs a callback weakening bridge. No
native syntax, schema, printer, frontend or `ProvesC` rule is changed here.
Effectful call-receiver source operands remain unsupported.

`Solidity/Examples/Tactics/DeferredCallback.lean` adds nine checks, including
a non-identity callback resume that changes the pushed source from `0` to
`9`, both in a prefix block and in a complete actual getter/capture program.
Other checks cover getter and prefix invariant violations, an unset alias
reverting before a callback-bearing prefix, a violation suppressing a
division-by-zero source, and a resumed prefix whose allocation survives its
scope end. Their relational witnesses and concrete observations are checked
by the kernel. Both modules are imported by the default root; the scratch
prototype is archived at `/tmp/migration-deferred-callback-reviewed.lean`.

Per-file diagnostics pass for both modules, the ordinary foundation's updated
cross-reference and the root. The frozen `./run-lean.sh` passes: 302 default
jobs, 147 TestSuite jobs, 345 taclets and all 131 read-bearing annotations
(`/tmp/migration-deferred-callback-run-lean.log`). The three headline
theorems' axiom audits use only `propext`, `Classical.choice` and `Quot.sound`
(`/tmp/migration-deferred-callback-axioms.log`). There are 314 reachable
modules and no orphans; `git diff --check` passes. Documentation-path checks
still report the same six missing vendored LeanTeX paths. The TestSuite,
corpus and wider migration counts are unchanged.

Read-only finder and skeptic reviews accept the promoted laws, default-root
wiring and nine regressions, with no confirmed defect. The finder identified
the two-alias scope limit during prototyping; the module and this milestone
record it explicitly. Neither review ran builds or the Lean server. Native
integration and the wider migration remain in progress. No commit or push
was made.

### Callback weakening through fresh typed locals

`Solidity/Semantics/CallbackWk.lean` proves general forward callback
simulation (`Stmt.exec_wk`, `Prog.exec_wk`) through any local thinning and
background typed environment. It covers the complete current syntax, with
no payment-free or fragment restriction. `CWkRel` preserves exact halts and
invariant violations; successful outcomes retain the added locals weakened
along the heap extension. Internal calls reuse their closed callee's callback
execution and lift the caller's returned locals across allocations. Transfers,
sends and all try branches preserve callback storage/net choices and invariant
facts. Paying loops use induction on the callback derivation, with body
weakening supplied by the structural program proof. The mutual headline
theorems discharge every helper's `WkP` premise.

`Prog.exec_afterAlias` specializes this to a fresh storage alias and the
program's scope end. The original callback run has a corresponding weakened
run with that alias retained, after temporary locals are removed. This proves
forward simulation only. Applying it to direct deferred operands and proving
the reverse direction of native capture correspondence remain outstanding;
native syntax, source support and `ProvesC` are unchanged.

`Solidity/Examples/Tactics/CallbackWk.lean` adds three concrete regressions.
A fresh unset alias does not replace the original push receiver: resumed
storage still yields `9` and the allocated object survives with heap length
one. A broken invariant still propagates. An allocating prefix drops its
memory temporary while retaining the fresh alias and grown heap. These reuse
the existing callback programs rather than add duplicate source fixtures.
Both modules are imported by the default root. The prototype is archived at
`/tmp/migration-callback-weakening-reviewed.lean`.

The new module, example and root have clean per-file diagnostics. After reducing
the module's import to `Semantics/Callback.lean`, its earlier worker remained
in elaboration; a fresh importing file checked the dependency successfully,
as required by the import-change guidance. The import-change `lean_build`
then restarted the language server and passed; direct module diagnostics
also passed on that fresh server. The full frozen `./run-lean.sh`
passes with 304 default jobs, 147 TestSuite jobs and all 345 taclets / 131
read-bearing annotations (`/tmp/migration-callback-weakening-run-lean.log`).
All three public headline theorems use only `propext`, `Classical.choice` and
`Quot.sound` (`/tmp/migration-callback-weakening-axioms.log`). The module graph
has 316 reachable modules and zero orphans; `git diff --check` passes. The
documentation-path check retains the six missing vendored LeanTeX paths.

Read-only finder and skeptic reviews accept the full forward proof, its
promotion, the acyclic imports and three regressions, with no confirmed
defect. Neither ran builds or the Lean server. Migration counts and wider
gaps remain unchanged. No commit or push was made.

### Reverse callback weakening and exact correspondence

`Solidity/Semantics/CallbackUnwk.lean` proves reverse callback simulation for
every current statement and program. Its internal judgements quantify any
extended initial state and local thinning; the public `Stmt.exec_unwk` and
`Prog.exec_unwk` recover a run of the original syntax from an execution of
the weakened syntax. There is no payment-free or fragment hypothesis.
Transfers, sends and try branches retain the same arbitrary resumed storage
and ledger choices. Closed callees retain their callback derivation and heap
extension. Paying loops use a proof-only view with fixed loop parameters;
both translations to and from the existing callback judgement are proved.
The structural mutual theorem discharges every helper's body hypothesis.

`CWkRel.right_unique` proves that the original outcome and the unchanged
background locals determine the weakened outcome. Combined with forward and
reverse simulation, `Stmt.exec_wk_iff` and `Prog.exec_wk_iff` state exact
callback correspondence through local thinning. `Prog.exec_withoutAlias`
recovers a program's callback run and scope result after removing a fresh
storage alias, complementing `Prog.exec_afterAlias`.

`Solidity/Examples/Tactics/CallbackUnwk.lean` adds four regressions. Their
weakened executions are built directly from callback constructors rather than
generated by forward weakening. A push reads resumed `calls = 9` and retains
an allocation; an invariant violation remains exact; a paying loop allocates
and exits after its callback changes the guard; and a prefix retains its
allocation after removing its memory temporary and the fresh alias. The
module and examples are imported by the default root, with no new dependency.

All affected modules and the root have clean per-file diagnostics. The full
frozen `./run-lean.sh` passes with 306 default jobs, 147 TestSuite jobs and all
345 taclets / 131 read-bearing annotations
(`/tmp/migration-callback-reverse-run-lean.log`). The import-change
`lean_build` also passes and restarts the language server. All seven headline
proofs and four regressions use only `propext`, `Classical.choice` and
`Quot.sound` (`/tmp/migration-callback-reverse-axioms.log`). The module graph
has 318 reachable modules and zero orphans; `git diff --check` passes. The
documentation-path check retains its six missing vendored LeanTeX references.
The reviewed prototype is archived at
`/tmp/migration-callback-reverse-reviewed.lean`.

Applying the correspondence to direct deferred operands and native capture
remains required work. Native syntax, source support and `ProvesC` are
unchanged; effectful call-receiver operands remain explicitly unsupported.
The twelve pending TestSuite obligations and wider migration gaps remain.

Read-only finder and skeptic reviews accept the full reverse proof, both iff
directions, fresh-alias scope recovery, promotion and four directly constructed
regressions, with no confirmed defect. Neither ran builds or the Lean server.
The reviewed checkpoint is `/tmp/migration-callback-reverse-reviewed.tar.gz`;
it captures the complete uncommitted working tree relative to HEAD rather
than an isolated patch to apply over concurrent edits. No commit or push was
made.

### Direct deferred callbacks agree with the actual capture program

`Solidity/Semantics/DeferredCorrespondence.lean` now applies forward and
reverse callback weakening to deferred receiver capture. Its direct semantics
are independent of the explicit capture: `DirectCall` executes the getter once,
`DirectAfterGetter` validates its returned alias before running any operand
effect, and `ExecPushAt` runs the original caller-context prefix while holding
the validated `SRef` outside its locals. `finishAt` reads and strips the final
source after callbacks, then checks capacity and pushes before dropping prefix
temporaries. Caller writes, heap growth, exact halts and invariant violations
are retained. No payment-free or prefix-fragment hypothesis is required.

`finishAt_wk` transports direct completion through any local thinning.
`finishPush_atAlias` proves the explicit push reads the protected alias after
the callback prefix; the proof derives its value from the scoped outcome
relation rather than assuming the prefix leaves arbitrary caller locals alone.
The one-alias, two-alias and direct-prefix iff lemmas remove exactly the two
hidden captures. `captureProgram_direct_iff` and `callProgram_direct_iff`
relate every outcome of the actual typed capture programs to the independent
direct semantics in both directions. `directCall_run` admits the ordinary
interpreter's result unless a callback exit violates the invariant.

`Solidity/Examples/Tactics/DeferredCorrespondence.lean` adds five regressions:
an independently constructed direct prefix observes resumed `calls = 9` and
retains an allocation, then derives a matching actual capture; an unset getter
reverts before a broken callback invariant and `1 / 0`; a prefix violation
suppresses the bad source; an independently constructed capture execution is
recovered as a direct call; and a memory-reference operand copies `47` into
storage with heap length one and the getter's counter incremented exactly once.
The new semantic and example modules are imported by the default root.

All affected modules and the root have clean per-file diagnostics. The frozen
full runner passes with 308 default jobs, 147 TestSuite jobs and all 345 taclets
/ 131 read-bearing annotations
(`/tmp/migration-deferred-correspondence-run-lean.log`). The import-change
`lean_build` passes and restarts the language server. All eleven headline
semantic lemmas and five regressions use only `propext`, `Classical.choice` and
`Quot.sound` (`/tmp/migration-deferred-correspondence-axioms.log`). The graph has
320 reachable modules and zero orphans; `git diff --check` passes. The
documentation-path check retains the six missing vendored LeanTeX paths.
The reviewed prototype is archived at
`/tmp/migration-deferred-correspondence-reviewed.lean`.

Read-only finder and skeptic reviews accept the substantive correspondence,
promotion and independent witnesses, with no confirmed code defect. The
skeptic identified stale descriptions of the semantic application as pending
in the weakening docs and module map; those now point to the completed
correspondence module. Neither reviewer ran builds or the Lean server.

Native effectful call-receiver statements, their printers, source import and
use by `ProvesC` still require integration. The existing native pure receiver
statement and source rejection are unchanged. The twelve pending TestSuite
obligations and wider import/storage-theory gaps remain. No commit or push was
made. The reviewed working-tree checkpoint is
`/tmp/migration-deferred-correspondence-reviewed.tar.gz`.

## Native effectful receiver integration

The isolated `migration-native-deferred` lane connects the deferred semantics
to source, the native rule table and both proof systems. The imported
`StorageReturns.receiverEffectfulOperand` now elaborates, passes its initial-state
execution check and closes its scoped box obligation by `sol_prove`.

`Stmt.callReceiverPush` retains a typed private prefix and its final source.
The getter runs once; an unset alias reverts before the prefix; the source is
snapshotted before capacity checking and storage push. Prefix locals end after
the source is read, while caller writes and heap growth survive.
`ReceiverValue` lets the existing
`storagePushValue_unfold_leftCallReceiver` constructor cover pure and deferred
operands without a duplicate upstream name. Dispatch, coverage, ordinary
soundness and SolKey fragment preservation include the new statement.

`NativeDeferred.capture_run` proves ordinary agreement with the actual named
capture program. `NativeDeferred.capture_iff` proves exact callback agreement,
including getter failures, unset aliases, prefix callbacks and invariant
violations. `ProvesC.unfoldReceiver` uses this correspondence, with callbacks
permitted in either the getter or the operand. Global callback soundness,
forward/reverse weakening, fuel approximation and hereditary storage invariants
cover the new constructor. It remains outside the existing EVM compiler fragment,
as does the earlier pure call-receiver statement.

Four source execution tests and both printer roundtrips cover sole increments
and primitive calls, caller-local mutation and private scope exit. Four native
callback tests cover resumed storage with allocation, unset getter precedence,
violation before a bad source and a copied memory reference. Arbitrary typed
prefixes execute and have capture correspondence, but their Solidity-expression
reconstruction is limited: unsupported shapes retain explicit fallback rendering.
Read-only finder/skeptic review found two over-recognition cases in the printers:
private-temp dependencies and empty deferred prefixes. Typed dependency checks
and regressions now make both cases fall back; both reviewers accepted the fixes.

Final isolated validation passed: 313 default build jobs, 149 TestSuite jobs,
345 parsed taclets and all 131 read annotations against frozen SolKey
`048a74de51a7cfb2cf497a043658424098f91e8e`. Sixteen audited headline and regression
theorems use only `propext`, `Classical.choice` and `Quot.sound`. Module reachability
passes at 325 modules; the documentation-path gate retains the six previously
known missing vendor LeanTeX references. The integration patch is
`/tmp/migration-native-deferred-integration.patch` and the axiom audit is
`/tmp/migration-native-deferred-axioms.log`.

The reviewed changes are integrated into the main working tree, with its
pre-existing uncommitted edits preserved. Final merged-tree confirmation is
complete: the same 313 default jobs, 149 TestSuite jobs and frozen sort check
passed in `/tmp/migration-native-deferred-main-run-lean.log`. The twelve pending
TestSuite obligations and wider import/storage-theory gaps remain; this is not
completion of the migration. No commit or push was made. The working-tree
checkpoint is `/tmp/migration-native-deferred-reviewed.tar.gz`.

## Automatic loop unwinding

Unannotated source loops now use `LoopAnn.auto` and the literal upstream
`whileUnwind` schema. The same constructor carries either automatic mode or
an explicit remaining bound (`LoopUnwind`); explicit zero still uses Lean's
exit check. Execution ignores this metadata. Quotation, weakening, dispatch,
coverage, ordinary soundness and the SolKey-only fragment include automatic
loops. Named walks seed the mode from the find and check the complete taclet
type before accepting it.

The scoped branch closer can refute a branch from symbolic hypotheses, such
as a required storage length, without the old ground-expression gate. It
still supplies a checked contradiction for every branch closed. Bounded
residue soundness is proved for an arbitrary walk budget. Default `sol_prove`
tries increasing budgets up to 20,000; the stages can attempt 52,640 nodes in
total. `sol_prove?` and `#solkey_derive?` retain the selected budget in
`sol_prove (steps := n)`, which replays one walk. No heartbeat or closer limit
was raised. Structural `sol_symex` still needs an explicit loop bound or
invariant to avoid expanding both automatic branches before closing leaves.

`Derived17.lean` proves nine previously pending upstream obligations: counting,
body-local declarations, while/for break and continue, do-while, storage-array
writes and a return through nested loops. They use fixed replay budgets of
512 steps, or 1,024 for the nested return. The TestSuite report now records
499 derived, three pending and 49 other functions. The remaining pending
obligations are `storagePushCompoundSigned`, `invariantForCountsArrayLength`
and `invariantClosedFormSum`. Wider import and storage-theory gaps remain;
the migration is not complete.

The mandatory read-only finder/skeptic review identified a printer that hid
concrete bounds and suggested proofs that repeated adaptive retries. Both
were fixed and accepted on follow-up. Four actual roundtrips through both
source printers preserve automatic, zero, before-bound and after-bound modes.
Boundary checks cover an infinite loop exhausting a small budget, a completed
loop with a false postcondition leaving a goal, an automatic proof using
SolKey rules alone, and rejection of out-of-range replay budgets. Existing
zero-bound examples and chain lines now state their bounds explicitly.

The isolated proof module built in 91 seconds. All thirteen audited loop,
pruning, replay-soundness and regression theorems use only `propext`,
`Classical.choice` and `Quot.sound`
(`/tmp/migration-auto-loops-axioms.log`). The frozen corpus check passes at
723 obligations: 499 derived, three pending, 48 unsupported, 70 concrete
proofs, 100 unported, one excluded and two skipped
(`/tmp/migration-auto-loops-corpus.log`). TestSuite trust/parity and module
reachability pass (326 reachable, zero orphans). The documentation-path check
retains the six known missing vendor LeanTeX references.

The changes are integrated into the main working tree. Final merged-tree
confirmation passes: 313 default build jobs, 150 TestSuite jobs, and all 131
read annotations across 345 parsed taclets against frozen SolKey
`048a74de51a7cfb2cf497a043658424098f91e8e`
(`/tmp/migration-auto-loops-main-run-lean-final.log`). The first package pass
found stale proof-suggestion pins, which were corrected before this final run.
All 486 modified/untracked migration files matched the isolated lane byte for
byte, preserving the main checkout's prior edits. The working-tree checkpoint
is `/tmp/migration-auto-loops-reviewed.tar.gz`. No commit or push was made.

## Bounded demanded storage reads

The signed three-push obligation now has a kernel derivation in
`TestSuite/Derived16.lean`. Its execution was already correct; twelve residual
leaves exceeded the closer's tree-size limit because each later write copied
earlier storage-read history. Applying the existing read eliminator when a
primitive `find` or array `len` is formed resolves known literal observations
before that duplication. Storage updates remain lazy terms.

`LTm.literalRead` first checks the input against the existing 24,000-node and
depth-12 limits, then attempts elimination. It retains only a literal result;
symbolic or oversized reads keep the exact original term, so later hypotheses
can still normalize them. The existing counters moved without changes into
`Calculus/ReadBounds.lean`, shared by this operation and `Seq.checkCore`.
No budget, heartbeat limit or execution semantics changed. This is a bound on
each input read, not a whole-proof runtime guarantee; repeated eligible reads
and dead operands still incur eligibility work.

`LTm.literalRead_eval`, `foldRead2_eval` and `Fresh.foldRead2` prove exact
evaluation and freshness, including undefined reads. They integrate into the
existing `Tm.toL_drel` and `Tm.toL_fresh` proofs. This schedules the same
SolKey data-structure read clauses earlier and adds no program taclet or
independent decision procedure.

Read-only finder/skeptic review caught two issues in the initial prototype:
elimination preceded the bounds, and replacing symbolic reads changed forms
that existing proofs depended on. Bounded, literal-only normalization fixes
both; the follow-up reviewers accepted it. Regressions retain unknown lengths,
reject depth thirteen and a 32,767-node input, preserve a dead short-circuit
operand, and leave a false signed assertion open. Existing symbolic-key and
storage-dependent loop proofs also pass.

The recorded compiled walk changes from twelve leaves in 184 ms to zero
leaves in 125 ms with the final bounded implementation. These are focused
measurements, not a package-wide speed claim. Eight audited general and
headline theorems use only `propext`, `Classical.choice` and `Quot.sound`
(`/tmp/migration-demand-reads-axioms.log`). Isolated validation passes:
314 default build jobs, 151 TestSuite jobs, 345 parsed taclets and all 131 read
annotations against frozen SolKey `048a74de51a7cfb2cf497a043658424098f91e8e`
(`/tmp/migration-demand-reads-run-lean.log`). The regenerated corpus and
TestSuite trust/parity checks pass at 500 derived and two pending obligations.
The pending invariant diamonds and wider import/storage gaps remain required
work.

The changes are integrated into the main working tree with its existing edits
preserved. Final merged-tree confirmation passes: the same 314 default jobs,
151 TestSuite jobs and frozen sort check
(`/tmp/migration-demand-reads-main-run-lean-final.log`). Reachability passes
at 327 modules with zero orphans. The checkpoint is
`/tmp/migration-demand-reads-reviewed.tar.gz`. No commit or push was made.

## Anonymous locals in the counting invariant

`invariantForCountsArrayLength` now has a checked derivation in
`TestSuite/Derived17.lean`, using a fixed 256-step walk followed by the shared
`sol_close`. The invariant anonymises the loop's written locals through a
dependent function. Their integer observations still carry unsigned bounds,
but the closer previously left those bounds inside the intrinsic types and
left optional length reads behind existential witnesses.

The new fallback exposes exact unsigned/signed range facts, eliminates
existential/conjunction hypotheses with checked single-branch proofs, and
substitutes identified read witnesses before retrying the existing arithmetic
closer. It follows `exLeft`, `andLeft` and `applyEq`; intrinsic range facts are
explicitly Lean-only in the rule map. No execution semantics, program taclet,
heartbeat or dependency changed. Each range scan charges at most 8,192 local
declarations/expression visits and adds at most 128 facts. Witness elimination
charges 8,192 declarations across all scans and performs at most 128 cases.
The two range scans and subsequent simplification/arithmetic have separate
costs; these are inspection limits, not a whole-proof runtime guarantee.

Read-only finder/skeptic review caught uncharged context scans, possible
metavariable assignments during type classification, and goal handling after
simplification closed the focused goal. The final implementation charges the
scans, skips unresolved types, recognises both subtype projection forms and
preserves following goals. Both reviewers accepted the fixes. Six regressions
in `Examples/Tactics/Loops.lean` cover dependent unsigned/signed reads, nested
optional witnesses, multiple goals, unrestricted integers and negative signed
values. All per-file checks pass.

Isolated validation passes: 314 default jobs, 151 TestSuite jobs and the frozen
345-taclet/131-read sort check (`/tmp/migration-anon-closer-run-lean.log`).
The range lemmas use only `propext`; the headline invariant theorem uses only
`propext`, `Classical.choice` and `Quot.sound`
(`/tmp/migration-anon-closer-axioms.log`). Regenerated corpus and TestSuite
trust/parity checks pass at 501 derived and one pending obligation
(`/tmp/migration-anon-closer-corpus.log`,
`/tmp/migration-anon-closer-parity.log`). Reachability remains 327 modules with
zero orphans. The documentation check retains the six known missing vendor
references. `invariantClosedFormSum`, wider imports/storage gaps and a fresh
complete source comparison remain required work; this is not migration
completion.

The milestone is integrated into the main working tree with prior edits
preserved. Final merged-tree validation passes with the same 314 default jobs,
151 TestSuite jobs and frozen sort check
(`/tmp/migration-anon-closer-main-run-lean-final.log`). All 491
modified/untracked migration files match the isolated lane byte for byte;
merged-tree TestSuite parity and reachability pass. The checkpoint is
`/tmp/migration-anon-closer-reviewed.tar.gz`. No commit or push was made.

## Native modular arithmetic

`addmodMulmod` now imports and has a kernel-checked derivation in
`TestSuite/Derived18.lean`. The focused report checks at 502 derived,
one pending and 48 other rows. The source import has 534 elaborated and
14 unsupported functions. The isolated default build (316 jobs), TestSuite
build (152 jobs), frozen 345-taclet/131-read sort check, corpus regeneration
and trust/parity gates pass. Merged-tree validation is still in progress.

The syntax retains native three-operand nodes; the interpreter, lazy terms,
lowering bridge, quotations and printers agree on them. The intermediate
sum/product is unbounded, and a general theorem proves that a nonzero
unsigned modulus produces an in-range remainder. Literal normalization has
a general evaluation-preservation theorem. The two assignment rules are
explicit `LeanTaclet` constructors: the frozen 345-taclet upstream
inventory contains no such native rules.

`Calculus/KeyValues.lean` checks values and reference-path indices
recursively. The strengthened `Stmt.inSolkey` excludes native builtins
inside initializers, expressions, lvalues, sources, conditions and bodies.
Simple value call arguments cannot contain one; reference argument indices
are checked explicitly by `Args.keyValues`. Argument-declaration preservation
requires that recursive value check. Weakening, rule selection,
premise preservation and `Proves.solkey_iff` pass focused checking.
Preservation is checked as one generated theorem per upstream constructor,
each with the existing heartbeat budget and a fixed proof strategy; the
public theorem applies those checked lemmas. No heartbeat limit was raised.

`Examples/Tactics/ModularArithmetic.lean` covers wide intermediate sums
and products, both dynamic zero-modulus failures, discarded calls, short
circuiting and conditionals, argument effects and captured reads, ordinary
function shadowing, wrong arity/type, static zero before effect capture,
false assertions and recursive fragment exclusion. All focused checks pass.
The verified EVM fragment explicitly excludes these new operations.
Solc 0.8.34 compilation confirms the builtin zero-modulus Panic 0x12 check
and permits a declared function to shadow its name. The model retains its
documented arithmetic-failure abstraction; see `docs/solc-alignment.md`.

Read-only finder/skeptic review confirmed the recursive program-rule
boundary and the generated proofs' kernel checks. The finder caught a
failure-priority error: the compiler checks the modulus before running
the other argument effects. The frontend now captures and checks the
modulus before those prefixes. Four kernel regressions distinguish
arithmetic revert from a helper's assertion panic, including a positive
modulus and a failing modulus expression. The boundary claim is about
program rules; arbitrary formula atoms/updates can still contain native
term symbols.

The compiled-source fixture `tests/solc/Modular.sol` passes through the
actual solc AST importer and proof runner: wide arithmetic, early zero
failure, legacy argument ordering, captured reads and builtin-name
shadowing prove; an operand's assertion panic with a positive modulus
remains proof-open. The source testing table now pins 503 ready public
functions. The six headline axiom audits use only `propext`,
`Classical.choice` and `Quot.sound`
(`/tmp/migration-modular-axioms.log`); fragment preservation itself uses
only `propext`. Reachability passes at 330 modules with zero orphans.
The documentation gate retains the same six missing vendor LeanTeX paths.

The milestone is integrated into the main working tree. Final merged-tree
checks pass: 316 default jobs, 152 TestSuite jobs, frozen sort annotations,
trust/parity, 330 reachable modules and zero orphans. All 30 source-runner
and migration-script tests pass, including the new compiled Solidity
fixture. That review also corrected a stale source-test expectation:
`receiverEffectfulOperand` already proves after the earlier deferred-receiver
milestone. All 500 modified/untracked migration files match the checked
lane byte for byte. The checkpoint is
`/tmp/migration-modular-reviewed.tar.gz`. No commit or push was made.
The remaining pending invariant, unsupported call/storage cases and fresh
full-source proof comparison remain required work; this is not migration
completion.

## Reference parameters

The isolated reference lane now imports seven previously unsupported
TestSuite functions. The three public obligations (`indexParameter`,
`storageStructParameter`, `storageMappingParameter`) have kernel-checked
derivations in `TestSuite/Derived18.lean`: 505 derived, one pending, 45 other.
The source import pins 541 elaborated functions and seven unsupported ones;
506 public obligations are stated. Corpus regeneration/build and
trust/parity pass at 505 derived, one pending, 44 unsupported program rows,
70 concretely proved and 100 unported legacy rows. The isolated default
build (319 jobs), TestSuite build (154 jobs), frozen 345-taclet/131-read sort
check, reachability (333 modules, zero orphans) and corpus/parity checks
pass. The nine axiom audits use only Lean's three standard axioms;
fragment preservation uses only `propext`
(`/tmp/migration-reference-axioms-checked.log`). All 31 source-runner and
migration-script tests pass (`/tmp/migration-reference-js-tests.log`),
including the new compiled reference fixture and its explicit pending rows.
The milestone is integrated into the main working tree. Merged-tree gates
pass with 319 default jobs, 154 TestSuite jobs, frozen sort annotations,
trust/parity and 333 reachable modules with zero orphans
(`/tmp/migration-reference-main-run-lean.log`,
`/tmp/migration-reference-main-parity.log`). All 506 modified/untracked
migration files match the reviewed lane byte for byte. The checkpoint is
`/tmp/migration-reference-reviewed.tar.gz`. No commit or push was made.

`Args.snocStorage` and `Args.snocMemory` retain intrinsic local types.
Their evaluation resolves identities without allocation. Function expansion
declares formals at those locations, with a checked execution-correspondence
proof. The generalized argument-capture proof uses `RevertOnly`: pure
arguments and paths return or revert, so capture cannot skip an earlier
invalid reference. Run invariants now explicitly accept storage aliases;
the previous assertion that all call parameters were values or memory
locals has been removed. No upstream taclet or heartbeat budget changed.

The source frontend prepares reference calls in argument order, holding
each reference and scalar read before later effects. Storage-to-memory
conversion copies at that argument's point; memory-to-memory and
storage-to-storage binding alias. Direct storage-return arguments and
new-array arguments are supported. Parameter locations survive the solc
reader, raw declaration parsing and `ImportRow.paramTypes`, including
uncalled functions omitted from the contract's inlining table.

Reference clauses use storage paths or memory identities as declared.
`Calculus/RefInputs.lean` supplies a nonallocating diamond identity-update
guard for initialized source parameters: hidden binders also range over
unset locals, which actual arguments never supply. Kernel examples reject
both unset storage and memory inputs. `FunContract.allArgs` uses typed
hidden binders for references. `\old` of memory contents and calldata
parameters remain explicitly unsupported; contract application retains
its existing restriction on memory mutation and alias rebinding. Assignable
clauses rooted at reference parameters remain unsupported.

`Examples/Tactics/ReferenceParameters.lean` checks shared aliases,
parameter rebinding, mixed parameter positions, mapping writes, copy before
later mutation, invalid-reference failure before assertion panic, nested
storage returns, allocation arguments and a memory-parameter specification.
Both source printers preserve execution and stable displayed text; internal
frame names can alpha-rename when reparsed. Review found and repaired the
missing reference argument printer cases and a mapping-key type printer
that incorrectly printed a primitive key as `T`.

Final read-only finder and skeptic passes confirmed these repairs and
reported no further material soundness defect. They checked the guards,
argument preparation, source metadata, recursive fragment restriction and
conservative EVM exclusion without running Lean. Printer evidence is
initial-state execution equality and stable displayed text, not a theorem
of arbitrary-state roundtrip equivalence. The documentation gate retains
the six known missing vendored LeanTeX references.

The compiled fixture `tests/solc/ReferenceParameters.sol` proves ordinary
reference calls, nested storage returns and allocation arguments. Two
cases remain explicitly proof-open: the larger copy sequence and automatic
closure of the initialized-input guard. Copy sequencing also has a concrete
kernel execution regression; neither open proof is claimed false or proved.
Conditional reference arguments containing calls retain the frontend's
existing conditional-call restriction. These are remaining proof/frontend
work, not a claim that arbitrary reference programs are covered.

The previous native checkpoint's fresh 112-source proof audit finished:
845 proved, 126 pending, 226 unsupported, 174 not run, 35 function errors,
155 internal, 25 skipped, three excluded and 13 compiler rejections, with
42 recorded source/contract errors. Listing had completed all 112 sources
with 1,158 ready functions and 12 import errors. Several proof subprocesses
timed out or exited 135; the strict comparison fails. Artifacts are
`/tmp/migration-native-proof-current.json`,
`/tmp/migration-native-listing-current.json` and
`/tmp/migration-native-compare-current.json`. Source coverage completion is
not proof completion, and this older checkpoint is not evidence for the
reference lane. A clean final source audit remains required.

## Symbolic memory-input lengths

The initialized-memory-input obligation left open by the reference milestone
now proves with the original input guard, within the existing budgets.
`Grown.lenId` packages the existing memory-length lookup at a result type
independent of the heap typing. The closer can therefore move it across
the exact global equality of a landed state and across local pushes before
resolving an intrinsically typed reference. Its evaluator correspondence is
`rfl`; invalid or wrongly typed identities still return `none`.

`Examples/Tactics/ReferenceParameters.lean` adds an arbitrary-state
`memory_input_length` specification theorem. The compiled-source
`initializedInput(uint[])` test proves in 737 ms with the original guard;
the source regression now requires that proof. Existing fresh-array,
symbolic-size and negative source cases pass unchanged. The four axiom
audits use only `propext`, `Classical.choice` and `Quot.sound`
(`/tmp/migration-refguard-axioms.log`). No operator, taclet or heartbeat
budget changed. A guard-spelling prototype was discarded after the length
bridge alone proved sufficient.

Read-only finder and skeptic review confirmed the exact lookup semantics,
full dependent-heap equality used by normalization, acyclic imports and
terminating rewrite directions. They found no material defect. The isolated
lane passes 319 default build jobs, 154 TestSuite jobs, the frozen 345-taclet /
131-read sort check and the unchanged 723-row corpus gate. All 31 JavaScript
source tests are validated: an early run passed 23 and failed eight because
imports were still rebuilding; those eight passed after the build finished,
as did a separate retry of the early negative-injection case. Logs are
`/tmp/migration-refguard-run-lean.log`, `/tmp/migration-refguard-corpus.log`,
`/tmp/migration-refguard-js-tests.log` and
`/tmp/migration-refguard-js-retry.log`. The merged tree passes the same
319/154 build jobs and frozen sort check, TestSuite parity (505 derived,
one pending and seven unsupported public functions), 333 reachable modules
with no orphans, and `git diff --check`. Its build log is
`/tmp/migration-refguard-main-run-lean.log`. All 507 modified/untracked files
match the reviewed lane. The checkpoint is
`/tmp/migration-refguard-reviewed.tar.gz`. The larger copy sequence remains
a separately tracked open proof.

## File-level struct and library swap

The source importer now includes file-level struct declarations. The finite
intrinsic table contains the exact `FileLevelPair { uint left; uint right; }`
layout, with its rank, mapping-free and default certificates. The frozen
`fileLevelStructThroughLibrary` obligation has a kernel-checked derivation
in `TestSuite/Derived18.lean`; its axiom set is only `propext`,
`Classical.choice` and `Quot.sound`. TestSuite now has 506 derived public
functions, one pending and six unsupported, with 507 scoped obligations.

Read-only finder and skeptic review exposed two validation holes. A nested
struct's name could match the table while its actual declaration had a
different layout, and an unknown library-local declaration ID could fall
back to a same-named file-level type. Both are repaired: type nodes with
declaration IDs require an exact validated entry, nested member types resolve
by identity, and invalid dependencies propagate through a bounded number of
rounds. The table's strict rank descent excludes an accepted dependency cycle.
Unrecognized library-local layouts remain explicitly unsupported.

`tests/solc/FileLevelStructs.sol` checks library storage aliases, false
assertions, compatible contract-local shadowing and mismatched shapes.
`tests/solc/FileLevelStructGaps.sol` checks both reviewed narrow-field cases:
an invalid nested `Sub` and a hidden library-local struct cannot become
full-word table fields. Both compiled-source regression tests pass.
Finder and skeptic accepted the final repairs without further material
findings. The isolated lane passes 319 default and 154 TestSuite build jobs,
the frozen 345/131 sort gate, 333 reachable modules with no orphans, TestSuite
parity and `git diff --check`. The regenerated 723-row corpus passes with
506 derived, 70 concretely proved, one pending, 43 unsupported, 100 unported,
one excluded and two skipped. Logs are `/tmp/migration-file-struct-run-lean.log`,
`/tmp/migration-file-struct-corpus.log` and
`/tmp/migration-file-struct-parity.log`.

The source suite passed 28 of 29 tests; its only failure was the expected
ready-row count, which increases from 506 to 507. The updated assertion passes
its targeted retry (`/tmp/migration-file-struct-js-retry.log`); all four
migration-tooling tests also pass (`/tmp/migration-file-struct-tooling-tests.log`).
The full source log is `/tmp/migration-file-struct-js-tests.log`. All 33 cases
are therefore validated across the complete run and the corrected-pin retry.

The merged tree passes the same 319/154 build jobs and frozen sort gate,
TestSuite parity, orphan and whitespace checks
(`/tmp/migration-file-struct-main-run-lean.log`,
`/tmp/migration-file-struct-main-parity.log`). The documentation path check
retains the six existing missing vendored LeanTeX paths. All 510 modified or
untracked migration files match the reviewed lane; the checkpoint is
`/tmp/migration-file-struct-reviewed.tar.gz`. No commit or push was made.

## Compatible fixed-array storage copies

The intrinsic source now admits fixed-to-dynamic and shorter-to-longer fixed
copies with an identical mapping-free element type. A checked `FixedCopy`
witness rules out truncation and incompatible elements. `Src.fixedCopy`
evaluates one source snapshot before the destination; its typed term has a
lazy reader proved against execution by `FixedCopy.observe_apply`,
`Src.lower_valueT` and `Op1.elim_rep`. A missing source still fails under
the original guard. The ordinary destination overlay clears the live tail
and preserves destination histories; source histories are stripped.

The explicit `storageFixedCopySave` and `pushFixedCopySave` adapters are
Lean-only: KeY's `Struct` sort erases the outer types that Lean must convert.
They are excluded from the native fragment and EVM compiler. Existing
same-type upstream copy rules retain their definitions. No element-write
parser lowering or heartbeat increase was introduced.

Five original frozen obligations now have kernel-checked derivations in
`TestSuite/Derived18.lean`: `storageStaticToDynamicCopyKeepsLength`,
`storageShorterStaticCopyClearsTail`, `testFixedCopyThenEmptyPushReadsZero`,
`testShorterCopyThenEmptyPushClearsTail` and
`testShapeCopyFixedTailAndSourceIndependence`. The TestSuite pin is 511 derived
public functions, one pending and one unsupported, with 512 scoped obligations.
`Examples/Tactics/ArrayShapeCopy.lean` also proves an arbitrary-state cleared
tail, concrete nested-history cases and source-printer roundtrips.
The compiled `tests/solc/ArrayShapes.sol` regression passes field targets,
source/target index effects, shape-compatible pushes, false tail/alias claims
and invalid-source reverts.

Read-only finder and skeptic review found a generic printer defect: erasing
fixed2-to-fixed4-to-dynamic conversions changed the reconstructed length
from four to two. The printer now keeps the exact typed conversion in a
Lean escape, and diagnostic printing names the target shape. A composed
conversion re-elaboration regression checks definitional equality.
Both reviewers accepted the repair without further confirmed defects.
The isolated lane passes 320 default build jobs, 154 TestSuite jobs and the
frozen 345-taclet / 131-read sort check. The regenerated 723-row corpus has
511 derived, 70 concretely proved, one pending, 38 unsupported, 100 unported,
one excluded and two skipped rows. Trust/parity, 334 reachable modules with
no orphans and whitespace checks pass. The axiom audit for the conversion,
lowering, lazy reader, global statement soundness, arbitrary-state tail
theorem and all five upstream proofs uses only `propext`, `Classical.choice`
and `Quot.sound`. Logs are `/tmp/migration-array-shape-run-lean3.log`,
`/tmp/migration-array-shape-corpus.log`,
`/tmp/migration-array-shape-parity.log` and
`/tmp/migration-array-shape-axioms-reviewed.log`.


All 34 JavaScript source and migration-tooling tests pass in one complete run
(`/tmp/migration-array-shape-js-tests.log`). The merged tree passes the same
320/154 build jobs and frozen sort gate, TestSuite trust/parity, 334 reachable
modules with no orphans and `git diff --check`
(`/tmp/migration-array-shape-main-run-lean.log`,
`/tmp/migration-array-shape-main-parity.log`). The six existing vendored
LeanTeX documentation-path misses remain. All 512 modified or untracked
migration files match the reviewed lane. The checkpoint is
`/tmp/migration-array-shape-reviewed.tar.gz`; no commit or push was made.

## Specification and type import containment

Quantifiers can now begin an implication's right operand. Their bodies keep
the same wide scope, matching the upstream `SolSpec.g4`. Function and
constructor clauses are validated alone when their bodies are admitted;
refused bodies supply no declaration or clause, so an unsupported renamed
parameter such as `from` no longer poisons unrelated declarations.
Parser-invalid modifiers are omitted from the modifier environment. Their
users fail the existing named lookup, and omission propagates through
callers and constructors instead of silently removing modifier execution.

Unsupported elementary state types and narrow array/mapping component types
are refused before they enter the literal contract. Existing declaration-ID
tracking refuses their body reads; a conservative token check refuses function
specifications mentioning an omitted state field. Shadowed names can also
be refused by this check. Contract invariants retain whole-contract validation,
and an invalid clause on an otherwise admitted body remains an import failure.
No unsupported type gains execution semantics.

The full TestSuite caught an initially overbroad elementary-type guard that
also rejected `string`/`bytes` catch labels. The elementary `tyText` branch
was restored; unknown-elementary rejection now walks only state declarations.
Both read-only reviewers rechecked this correction and accepted the final
containment boundaries.

`tests/solc/SpecImport.sol` checks quantified true and false claims, renamed
clauses, omitted bodies and modifiers, transitive callers, a rejected
constructor, omitted state types, specification-only field dependencies and
unrelated false assertions. Its focused regression and the existing clause
injection test pass. The frozen arithmetic-open source imports 21 functions
without a contract-level error; real-world ERC20 imports three ready and three
unsupported rows without a contract-level error. The frozen type suite imports
42 rows without a contract-level error. The isolated lane passes 320 default
and 154 TestSuite jobs, the frozen 345/131 sort gate, unchanged TestSuite
trust/parity (511 derived, one pending, one unsupported), the unchanged
723-row corpus, 334 reachable modules with no orphans and whitespace checks.
Logs are `/tmp/migration-spec-import-run-lean2.log`,
`/tmp/migration-spec-import-corpus.log`,
`/tmp/migration-spec-import-parity.log` and
`/tmp/migration-spec-import-source2.log`.


All 35 JavaScript source/tooling cases pass in one complete run
(`/tmp/migration-spec-import-js-tests.log`). The merged working tree passes
320/154 build jobs and the frozen sort gate
(`/tmp/migration-spec-import-main-run-lean.log`), trust/parity, orphan and
whitespace checks. All 514 modified or untracked migration files match the
reviewed lane. The checkpoint is `/tmp/migration-spec-import-reviewed.tar.gz`.
No commit or push was made.

## Inherited declarations and dispatch

The single-source importer retains Solc's C3 metadata, recomputes the complete
linearization, and requires exact agreement. Ancestors initialize once in
reverse C3 order. State, struct declarations, functions and modifiers retain
declaration identities. Virtual function/modifier dispatch follows transitive
override metadata; explicit `Base.f` and qualified modifiers keep their named
implementation. Named arguments are ordered against the original declaration
before dispatch. Private helpers stay bound to their declaration, and external
`this`/object calls keep the existing external-call semantics.

Only the selected contract's own functions and constructor receive independent
test rows. Inherited functions are helpers. Specification enum names resolve
in the defining declaration's lexical ancestry. The importer refuses missing,
cyclic, inconsistent or incomplete metadata instead of taking a partial closure.
Base constructors, `super` and inherited contract NatSpec are imported
(`docs/solc-alignment.md`, "Constructors"); duplicate storage-root names
remain an explicit gap. Imports/remappings remain outside
the compiler helper's single-source scope.

This extends the frozen upstream parser for explicit static base calls, which
its higher-level open suite describes as unsupported. The behavior follows
[Solidity's inheritance rules](https://docs.soliditylang.org/en/latest/contracts.html#inheritance).
Virtual dispatch in a base initializer was also checked against the pinned
compiler's emitted IR. No calculus representation or taclet changed.

`tests/solc/Inheritance.sol` checks virtual and static dispatch, renamed named
arguments, private helpers, virtual and qualified modifiers, inherited structs,
positive/false enum specifications, modifier invariants and external-call
opacity. Its diamond deployment has a kernel-checked execution theorem covering
all five constructor assertions; automatic symbolic closure of that constructor
remains pending. `InheritanceGaps.sol` pins conservative refusal boundaries.
Kernel examples reject a swapped C3 sibling order, missing/unknown ancestors
and an inconsistent merge. Both read-only reviewers accepted the C3 and lexical
scope repairs; the tests keep false claims pending.

The isolated lane passes 321 default and 154 TestSuite build jobs, frozen
345/131 sort annotations, TestSuite trust/parity (511 derived, one pending,
one unsupported), the unchanged 723-row corpus, 335 reachable modules with
no orphans and whitespace checks. The constructor execution theorem uses only
`propext`, `Classical.choice` and `Quot.sound`. The six existing vendored
LeanTeX documentation-path misses remain. Evidence logs are
`/tmp/migration-inheritance-run-lean.log`,
`/tmp/migration-inheritance-corpus.log`,
`/tmp/migration-inheritance-parity.log` and
`/tmp/migration-inheritance-axioms.log`.

All 37 JavaScript source/tooling tests pass in one complete run
(`/tmp/migration-inheritance-js-tests.log`). The merged tree passes the same
321/154 build and frozen sort gates, trust/parity, orphan and whitespace
checks (`/tmp/migration-inheritance-main-run-lean.log`,
`/tmp/migration-inheritance-main-parity.log`). All 518 modified or untracked
migration files match the reviewed lane. The checkpoint is
`/tmp/migration-inheritance-reviewed.tar.gz`; no commit or push was made.

## Contract address in specifications

Bare `this`, including the already-erased `address(this)` cast, now resolves
to the existing typed `selfAddress` environment symbol. Local parameters and
named returns retain priority; state and reference shadows keep their prior
resolution. `\old(this)` reads the same environment address, while
`\old(net(this))` continues to read `oldNet`. No snapshot, booking premise or
calculus rule changed. Both read-only reviewers accepted these boundaries.

`tests/solc/SpecSelf.sol` proves address identity, unchanged address/ledger
snapshots, a parameter premise and a returned source address. False address
and ledger-delta claims remain pending. `Examples/Tactics/Specs.lean` pins
intrinsic local, return, state and reference shadow resolution. The focused
source regression passes. Frozen `benchmark/SendContract.sol` now proves both
obligations without import errors. `benchmark/SendingEther.sol` imports without
errors with three pending and two unsupported obligations; its payment proofs
are not established by this adapter. Logs are
`/tmp/migration-spec-self-source-tests.log`,
`/tmp/migration-spec-self-sendcontract.json` and
`/tmp/migration-spec-self-sending.json`.

All 38 JavaScript source/tooling tests pass in one complete run
(`/tmp/migration-spec-self-js-tests.log`). The final isolated and merged
trees pass 321 default and 154 TestSuite jobs and the frozen 345/131 sort
gate (`/tmp/migration-spec-self-run-lean2.log`,
`/tmp/migration-spec-self-main-run-lean.log`). TestSuite trust/parity and
the 723-row corpus are unchanged; 335 modules are reachable with no orphans,
and whitespace checks pass. The first build captured incomplete regression
annotations; those were fixed before the final run. All 520 modified or
untracked migration files match the reviewed lane. The checkpoint is
`/tmp/migration-spec-self-reviewed.tar.gz`; no commit or push was made.

## Typed constants in specifications

The specification AST now distinguishes a fixed unsigned literal from a
context-polymorphic numeral. `uint(n)` quotes `SpecExpr.uintLit`; its compiler
range-checks `n` and constructs the existing typed literal term. It is not
eligible for a numeral's contextual coercions. The printer and counterexample
seed collector retain the new form. Macro equality, formatting, mixed signed/
Boolean rejection and an out-of-range case are pinned. This extends the
specification AST without changing the calculus's signature or proof rules;
the history check found no earlier speed optimization being undone.

The importer substitutes only lexical elementary `uint`/`uint256` constants
with literal-only, exact integral expressions in `[0, 2^256)`. It uses the
existing rational constant evaluator, including Solidity units, and writes
`uint(n)` before checking references to omitted fields. Function and modifier
clauses use their defining contract's ancestry; contract invariants use the
requested contract. Private ancestor constants are hidden, other contracts
and libraries cannot leak declarations, and local/return shadows and ambiguous
names remain unresolved. Other types, casts, calls and dependent constant
initializers are outside this fragment. Quantified/escaped clauses and renamed
shadows retain the conservative refusal boundaries.

`tests/solc/SpecConstants.sol` checks units, invariants, true and false claims,
own and inherited visibility, private ownership, other-contract/library
isolation, shadowing and unsigned/signed type rejection. The focused regression
passes. Typed constant casts in loop invariants still require a statement and
are explicitly refused; this milestone does not claim loop-annotation support.
Both read-only reviewers accepted the typing and visibility boundaries.

Frozen EtherGame now imports without errors with one proved and one pending
obligation. Frozen OZReentrancyGuard has four proved, two internal and one
unsupported row without import errors. Fixed constants follow Lean's existing
body inlining; the upstream guard's comments describe an older unconstrained
constant-slot model. Evidence is `/tmp/migration-spec-constants-source-tests2.log`,
`/tmp/migration-spec-constants-ethergame.json` and
`/tmp/migration-spec-constants-oz.json`.

The isolated lane passes 321 default and 154 TestSuite build jobs and the
frozen 345/131 sort gate (`/tmp/migration-spec-constants-run-lean.log`).
TestSuite trust/parity is unchanged at 511 derived, one pending, one excluded
and one unsupported obligation; 335 modules remain reachable with no orphans.
Whitespace checks pass.

All 39 JavaScript source/tooling tests pass in one complete run
(`/tmp/migration-spec-constants-js-tests.log`). The unchanged 723-row corpus
passes (`/tmp/migration-spec-constants-corpus.log`). The merged tree passes
the same 321/154 build and frozen sort gates
(`/tmp/migration-spec-constants-main-run-lean.log`), TestSuite trust/parity,
orphan and whitespace checks. The six existing vendored LeanTeX path misses
remain. All 523 modified or untracked migration files match the reviewed lane.
The checkpoint is `/tmp/migration-spec-constants-reviewed.tar.gz`; no commit
or push was made.

## Ledger-clause containment and builtin names

At the frozen SolKey pin, `KeyNatspec.java` documents `assignable` as accepted
and ignored; `SolidityProblemSynthesizer` adds invariants and ensures without
frames. Lean's existing storage assignable frame is therefore a stronger
extension. This milestone adds no ledger frame semantics. Source functions
with `assignable net(...)` are explicitly unsupported before their clauses
are interpolated, and their callers retain the gap. A bare state field named
`net` still uses the existing storage frame. Whitespace-separated call heads
are recognized; comment-separated variants can still fail parsing.

Review caught a collision with constants named `net`. The classifier now
checks raw clauses, and a shared token classification distinguishes builtin
call heads from variable reads in both constant replacement and omitted-field
checks. Escaped specification keywords also remain intact: constants named
`old` and `result` coexist with `\old` and `\result`, whose operands retain
the usual dependency checks. Token traversal is structural and linear in the
input rather than repeatedly dropping prefixes.

`tests/solc/NetAssignable.sol` pins ledger/mixed-frame refusal, transitive
caller refusal, unrelated positive and false assertions, the bare state
name, constant/builtin collisions, escaped keywords and a false ledger
claim. The focused source regression passes
(`/tmp/migration-net-assignable-source-tests3.log`). Frozen MultiAuction now
reports three unsupported functions and two skipped functions without a
contract-level error (`/tmp/migration-net-assignable-multiauction.json`).
This is containment, not a proof of MultiAuction or ledger-frame support.
Both read-only reviewers accepted the corrected classification and scanner.

The pinned synthesizer also assumes `msg.sender != this` for specified
obligations. Lean currently does not add that premise; its obligations cover
those entry states as well. No premise was added to make these tests pass.

The isolated lane passes 321 default and 154 TestSuite jobs, the frozen
345/131 sort gate, unchanged TestSuite trust/parity and the unchanged
723-row corpus. All 335 modules remain reachable with no orphans, and
whitespace checks pass. The six existing vendored LeanTeX path misses remain.
Logs are `/tmp/migration-net-assignable-run-lean.log`,
`/tmp/migration-net-assignable-parity.log` and
`/tmp/migration-net-assignable-corpus.log`.

The complete listing visits all 112 sources without contract-level import
errors: 1,299 ready, 232 unsupported, 234 internal, 27 skipped, three excluded
and 13 intentional compiler-rejection rows
(`/tmp/migration-net-assignable-listing-current.json`). These are listing
classifications, not proof results.

All 40 JavaScript source/tooling regressions pass in one complete run
(`/tmp/migration-net-assignable-js-tests.log`). The merged working tree
passes 321/154 build jobs and the frozen sort gate
(`/tmp/migration-net-assignable-main-run-lean.log`), TestSuite trust/parity,
orphan and whitespace checks. All 524 modified or untracked migration files
match the reviewed lane. The checkpoint is
`/tmp/migration-net-assignable-reviewed.tar.gz`; no commit or push was made.

## Full audit before specification integer negation

The dated [listing](../tests/migration/listing-2026-10-16.json) records all
112 pinned sources and 1,808 rows, with no contract-level import errors:
1,299 ready, 232 unsupported, 234 internal, 27 skipped, three excluded and
13 intentional compiler rejections. The dated
[expectations](../tests/migration/expectations-2026-10-16.json) retain the
strict policy: unsupported positive-suite rows remain required proofs.

The [uniform proof audit](../tests/migration/proof-2026-10-16.json) completed
all 112 sources and retained all 1,808 result rows. Its
[summary](../tests/migration/proof-2026-10-16.summary.json) records 1,032
proved rows. Its 32-function TestSuite batch timed out after 500 proofs,
leaving 13 rows unattempted. The separate
[focused retry](../tests/migration/proof-testsuite-retry-2026-10-16.json)
tests those exact signatures individually: 11 proved, one pending and one
unsupported, without process errors. Combining the disjoint results confirms
511 TestSuite proofs, 37 internal helpers, one pending, one unsupported,
one excluded and two skipped rows. This does not erase the uniform audit's
timeout or make its strict comparison pass.

The [supplementary retry report](../tests/migration/proof-unattempted-retry-2026-10-16.json)
attempts every one of the uniform audit's 87 `notRun` rows individually,
including those 13 TestSuite rows. It recovers 47 proofs and retains all
remaining outcomes. The [combined summary](../tests/migration/proof-retry-combined-2026-10-16.summary.json)
substitutes only those disjoint retry results; it preserves four unattempted
rows and does not erase errors from either run.

| Outcome | Uniform audit | With individual retries |
|---|---:|---:|
| proved | 1,032 | 1,079 |
| pending | 162 | 176 |
| unsupported | 229 | 243 |
| error | 24 | 29 |
| notRun | 87 | 4 |
| internal | 231 | 234 |
| excluded | 3 | 3 |
| skipped | 27 | 27 |
| compileRejected | 13 | 13 |

The [strict comparison](../tests/migration/comparison-2026-10-16.json)
fails with 513 outcome mismatches and 17 process/command error records.
The supplementary run retains five additional process/command error records.
These records are separate from the per-function `error` rows in the table.
Full source parity is not established. Some mismatches reflect deliberate
semantic differences: seven upstream `unprovable/Unprovable.sol` box
fixtures prove because Lean's checked, bounded arithmetic reverts before
`assert(false)`; upstream's unbounded arithmetic reaches the assertion.
The strict policy has not been weakened to accept these observed results.

The [implementation sidecar](../tests/migration/proof-2026-10-16.implementation.json)
records the frozen upstream/compiler inputs, 526 source hashes, observed
launch session and file identity, immutable completed-source checkpoint,
prepared listing/expectation hashes and final report hashes. Source hashes
were captured during the observed run and rechecked at finalization in both
the main tree and the isolated lane; all remained unchanged. Documentation
and report artifacts are outside the source digest. This is an observed-run
provenance record, not a pre-launch signed attestation.

The final read-only finder and skeptic reviews independently reproduced
the counts, unique identities, strict findings, source hashes and retry
composition. Review clarified that the result rows include 13 source-level
compiler-rejection placeholders. Both accepted the corrected evidence and
its limits. The final orphan check reports 335 reachable modules and no
orphans; whitespace and all ten migration-artifact links pass. The six
existing vendored LeanTeX documentation-path misses remain.

The complete
[inheritance checkpoint audit](../tests/migration/proof-inheritance-2026-10-16.json)
is historical evidence from before the later address, constant and clause
repairs; its sidecar records that boundary. It does not validate the final
working tree.

## Specification integer negation

The specification AST retains unary negation. Its compiler now supports
negating a ledger integer and widens an unsigned negand when the other
operand supplies a ledger integer context, in either operand order and
under `\old`. Negative literals also take the ledger integer sort there.
SolKey's `SpecCompiler.visitUnary` uses `neg`; Lean expresses the operation
through its existing typed integer subtraction from zero and `toInt`.
No statement evaluator, signature symbol or program taclet changed.
Primitive subexpressions retain their checked arithmetic, and unsigned
negation outside the ledger context and signed/ledger mixtures stay refused.

Review found exponential recompilation of nested invalid expressions in an
initial retry-based implementation, including a case crossing a ledger
address's context reset. Operand result shapes now select the context
before compilation, and each operand is compiled once by the pairing helper.
The actual types and ledger addresses are still checked. Six twenty-level
failure regressions cover ordinary and ledger entry contexts, invalid
ledger addresses and negated ledger reads. Both read-only reviewers accepted
the repair and typing boundaries. Shape scans can revisit subtrees; this is
not a claim that the complete compiler runs in linear time.

`tests/solc/SpecNegation.sol` proves eight source obligations, including
snapshots, typed constants, negative literals and maximum unsigned values.
The false-claim and overflowing-inner-arithmetic regressions remain pending.
Three native theorems in `Examples/Tactics/Specs.lean` pass the kernel and
use only `propext`, `Classical.choice` and `Quot.sound`. Per-file diagnostics
are clear. The fresh axiom check is `/tmp/migration-spec-neg-axioms.log`.

The [focused upstream rerun](../tests/migration/proof-spec-negation-2026-10-16.json)
and its [source sidecar](../tests/migration/proof-spec-negation-2026-10-16.implementation.json)
cover only the two Purchase sources and Escrow, with 527 unchanged captured
source hashes. Negation type errors are gone. The 14 rows remain one proved,
eight errors, four unsupported and one skipped, plus one process/command
error record. Purchase still hits heartbeat limits; Escrow still fails
proof preparation, and its nonstandard-axiom checks reject the resulting
proof candidates. This is not a proof of those contracts. The earlier
112-source audit above predates this change and has not been replaced by a
new whole-corpus run. Evidence is `/tmp/migration-spec-neg-upstream.log`.

The isolated lane passes 321 default and 154 TestSuite jobs, the frozen
345/131 sort gate, all 41 JavaScript regressions and the unchanged 723-row
corpus. TestSuite trust/parity remains 511 derived, one pending, one excluded,
one unsupported and two skipped. The orphan check reports 335 reachable
modules and no orphans; whitespace passes. The six existing vendored LeanTeX
documentation-path misses remain. Logs are `/tmp/migration-spec-neg-run-lean.log`,
`/tmp/migration-spec-neg-js-tests.log`, `/tmp/migration-spec-neg-corpus.log`
and `/tmp/migration-spec-neg-parity.log`.

The merged workspace passes the same 321/154 build and frozen sort gates,
TestSuite trust/parity and whitespace checks. All 527 source hashes and
the focused evidence artifacts match the reviewed lane. Merged logs are
`/tmp/migration-spec-neg-main-run-lean.log` and
`/tmp/migration-spec-neg-main-parity.log`. No commit or push was made.

### Proof-preparation performance investigation

Fresh scratch profiles of the pinned benchmark Purchase's `abort` obligation
isolate the current 200000-heartbeat failure in `sol_spec_prep`'s initial
`sol_close_eval`. Symbolic execution takes about 0.04 seconds; the failing
simplification takes about 8 seconds (`/tmp/migration-purchase-profile.log`).
Disabling definitional simplification lets that first pass finish, but later
contextual simplification still exhausts the same budget. Early formula and
evaluator rewrites, a landed-state congruence lemma, explicit rewrite proofs
and keeping the contract constant opaque did not repair the full pipeline.

A scratch Option-native weakest precondition has kernel-checked bridge,
bind, map, success and failure lemmas. Its evaluation-only elaboration takes
about 7 seconds, plus a separately reported 2.4-second kernel check; the full
preparation still times out
(`/tmp/migration-purchase-profile-option.log` and
`/tmp/migration-purchase-profile-option-full.log`). Staged single-pass
prototypes also leave goals and exceed the enclosing declaration's budget.
An intermediate progress message is therefore not evidence of a completed
preparation or proof. Scratch obligations deliberately use `sorry` to inspect
unfinished goals; none is imported, reported as proved or included in the
package. No performance prototype was integrated, no heartbeat limit was
raised, and the reviewed 527-source implementation remains unchanged.
Both read-only reviewers accepted this evidence boundary; the finder's
timing clarification above separates elaboration from kernel checking.

## Specification and loop binding renaming

The testing importer no longer rejects an otherwise supported specification
because its parameters or named returns require fresh Lean names. It escapes
keywords for parsing, rewrites free identifier heads in the parsed clause,
and validates the complete standalone member again. Member labels and storage
location roots stay as declared; assignable index expressions follow parameter
renaming. Parameters retain their pre/post-state scope. Named returns are
rewritten only in `ensures`, outside `\old`; quantifiers shadow both maps.
The pure `readContract` reader remains conservative without the importer's
parser callbacks.

Fresh names are allocated cumulatively against declarations, prior generated
names, function clauses and all loop annotation tokens. Review found that
independent allocation could collapse distinct parameters and make a false
claim vacuous; it also found return references being renamed in the wrong
state. Both are repaired and have permanent negative regressions.

Loop annotation names now follow lexical declaration scopes. The reader tracks
parameters, returns and local declarations, restores block and `for` scopes,
and isolates try success parameters and each catch's parameters. Modifier
parameters use the same table. An annotation is parsed as a `sol_expr` before
identifier-head renaming. Originally unbound annotation names stay unbound.
The existing quantified-loop boundary remains; this does not add a formula
invariant language or change loop taclets.

`tests/solc/SpecBindings.sol` covers keyword and state-field shadows, `\old`,
named returns, quantified shadows and siblings, deep capture, member labels,
assignable frames, constructors, inherited helpers, comments, malformed
clauses and loop scopes through modifiers, returns and catches. Its
[focused report](../tests/migration/proof-spec-bindings-2026-10-16.json) has 37
rows: 25 proved, nine pending negative checks, two unsupported malformed or
unbound-name checks and one internal helper, with zero process errors.
The [source sidecar](../tests/migration/proof-spec-bindings-2026-10-16.implementation.json)
captures 528 source hashes. This report covers the local regression fixture
only. The earlier 112-source audit has not been rerun on this implementation.

Both read-only reviewers accepted the repaired binding and lexical-scope
implementation. The two targeted JavaScript regression groups pass, including
the existing `SpecImport.sol` cases that now prove the renamed specification
and constructor while keeping the false caller open. The isolated build passes
321 default and 154 TestSuite jobs. Its automatic sibling-checkout sort step
was skipped, so the explicit frozen `--key` run was performed separately:
345 taclets, 131 read-bearing annotations, zero disagreements. The unchanged
723-row corpus and TestSuite trust/parity pass: 511 derived, one pending, one
excluded, one unsupported and two skipped. The orphan check reports 335
reachable modules and zero orphans. Logs are `/tmp/migration-spec-renames-run-lean.log`,
`/tmp/migration-spec-renames-sort.log`, `/tmp/migration-spec-renames-regression.log`,
`/tmp/migration-spec-renames-corpus.log` and `/tmp/migration-spec-renames-parity.log`.

The complete JavaScript run passed 41 of 42 groups. The remaining group's old
expectation still required a shadowed constant parameter to be unsupported;
the new importer correctly leaves its false claim pending. After correcting
that assertion, the entire constant-specification group passed on a targeted
rerun. No implementation or fixture changed between these runs. Thus all 42
groups are covered across the full run and rerun; this is not a claim of a
second all-green full run. The logs are `/tmp/migration-spec-renames-js-tests.log`
and `/tmp/migration-spec-renames-constant-regression.log`. Whitespace passes;
the documentation-path checker retains only its six existing vendored
LeanTeX misses. The complete working tree is preserved in
`/tmp/migration-spec-bindings-reviewed.tar.gz` before the temporary lane is removed.
The merged main workspace passes the same cached 321/154 build and explicit
frozen sort gates (`/tmp/migration-spec-renames-main-run-lean.log`). Its 528
captured source hashes and focused artifacts match the reviewed lane.
