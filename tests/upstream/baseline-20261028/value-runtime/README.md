# Value-entry runtime supplement (2026-10-28)

Starting checkpoint `29b73d0ec4534d8fd6ca4e74f11e8008803bfc24`, same saved VM
and `baseline/current-master-20261028` branch. The authorized Lifetime **root-only**
refresh succeeded. `valueEntryDiagnosticComplete = true` applies only to the
controls below. Historical `nativeValidationComplete = false` fields remain
unchanged as historical evidence. No corpus/feature/proof completeness promotion
is inferred; all 9,660 fixture verdicts and original observations are intact.

## Root compilation and actual provenance

Direct configured Lean4.24.0 (`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`),
Lake5.0.0-src+797c613. The unmodified `Solidity/Semantics/Lifetime.lean` was
compiled **once**, directly with `lean -j1 --tstack=131072 -o ... -i ... -c ...`,
using current local import identities. Root compilation exit0 took3.553542524s;
no Lake build, dependency compilation, Testing/ProveChunked build, project or
managed configuration edit occurred. Root timeout900s and diagnostic120s were
existing bounds. All stages used12GiB aggregate cgroup/no swap/one CPU, with
`LEAN_NUM_THREADS=1`; every Lean invocation supplied `-j1`. Peak aggregate memory
across recorded compilation/native stages was828518400 bytes. See `resources.json`
for actual per-command logs, elapsed times and aggregate cgroup peaks.

The private overlay contains the new Lifetime `.olean`/`.ilean`/generated C and
76 links to the already-verified native `.olean` artifacts. No linked native
root object was needed: actual `#eval` execution of `System.run` worked with the
private root artifact. Root source, all27 current dependency identities, all304
native cache snapshots, the old Lifetime source/artifact/setup/trace and root
lakefile are preserved in309 shared hash snapshots. All are unchanged afterward.
All77 overlay olean hashes independently match recorded identities. The stale
shared Lifetime root was never overwritten. Paths, source/olean/setup hashes and
Lake's own source/output hash verification are in the archive.

Retained failures are diagnostic failures, never passing evidence:

- Initial root preflight exit1: Lean selected the overlay as the `Solidity`
  package root, so it could not find the already-cached Upstream module there.
  Added verified symlinks and reran only the import preflight; exit0. No second
  root compilation or dependency build.
- Initial value wrapper exit1: reserved identifier, record layout and source
  contract alias errors in the new diagnostic. Corrected per-file checks pass;
  the original wrapper/log are archived.
- Initial expected-result verifier exit1: it attempted `git show` for an ignored
  raw input whose authoritative bytes are in the historical evidence archive.
  The corrected verifier checks that archive and its per-file hashes. The
  original lookup failure has no elapsed measurement; none is invented.

The corrected seven-transaction run is retained. The final eight-transaction
run adds a stronger unchanged-source rejection control at counter13, where
executing the rejected body would instead set9. Earlier runs/inputs are intact.

## Actual model-entry observations, both legacy and viaIR

Pinned solc0.8.38 SHA256
`6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390` analysed
`inputs/ValueEntry.sol` separately in each required pipeline. Full ASTs, pipeline
settings, source SHA256 and compiler records are archived. Production
`solc_import ... testing entrypoints` creates7 admitted typed report rows per
mode. Each selected action is resolved by unchanged `Upstream.resolveEntry`;
canonical signature, source declaration ID, external-entry role and report/
declaration payability must agree. The adapter only accepts zero-argument void
entries, closes the actual imported program with existing `Stmt.block`, and
calls **existing `Lifetime.System.run`** with explicit `TTx`. It contains no
replacement nonpayable guard. All source functions are loop/recursion-free;
this API uses `Prog.run`, not Upstream's fuel-bounded run.

Actual imported constructor deployment succeeds with counter3, balance0,
ledger sender7:0. Sender7 differs from self9; time increases from1 through8.
Explicit assumed spendable caller funds100 suffice for every selected call.
`World.accepts` premises are checked; `allowCall` is the defaultTrue. Lifetime
itself does not model spendable environment balances.

| Transaction | Actual result in each pipeline |
| --- | --- |
| nonpayableEntry, value0 | Success; counter9, balance0/ledger0 |
| nonpayableEntry, value1 | Empty-data rejection; prior persistent state/payment retained |
| payableEntry, value5 | Success; counter11, seenValue5, seenSender7, seenBalance5; balance/ledger5 |
| writeFail, value2 | Exact36-byte Panic(0x01); counter11/balance5/ledger5 retained |
| internalCall, value3 | Success; ordinary public nonpayable function plus internal helper execute; counter13, seenValue3/sender7/balance8; balance/ledger8 |
| nonpayableEntry, value1 at counter13 | Empty-data rejection; counter stays13, whereas source body would set9 |
| ordinary, value1 | Empty-data external rejection; counter13, whereas its body would increment14 |
| ordinary, value0 | Success; counter14; balance/ledger8 |

`helper()` is separately refused by the actual canonical ABI resolver in both
modes. The unchanged scalar negative control from native-cache expects8 for
`identifiers()` and actually returns7: unchanged Upstream reports `broken` with
the exact runtime expectation mismatch, both modes. This is a scalar negative
control, not a payment-specific comparator. No original expectation was changed.

On failure, `System.run` returns **no world**. The adapter retains immutable
prior `World.atTime`, following the existing `Step.rollback` relation. Its
reported persistent fields, ledger and funds remain unchanged; time advances.
This is explicit rollback policy plus observed errors, not a claim that
`System.run` returned restored state or that a concrete trace was kernel-proved.
`System.run_ok` prints only propext/Classical.choice/Quot.sound;
`World.enter_zero` prints propext. Root compilation kernel-checks the unchanged
Lifetime proofs. The observed transactions are native interpreter evidence,
not new kernel proofs, generated-EVM execution or compiler correspondence.

## Independent result checks and remaining limits

`solidity-baseline-value-verify.py` independently compares every source ID,
payability, transaction, before/after field, exact bytes, ledger/payment total,
remaining assumed funds, helper refusal and false-output control to explicit
expectations. Both mode results agree. Five corrupted-evidence controls are
rejected: leaked body effect, double credit, retained failed payment, changed
panic code and internal ABI admission. Those five are static verifier controls,
not additional runtime results.

Only this bounded value-entry diagnostic is complete. Universal source lowering,
external ABI dispatcher correspondence, nonzero-argument ABI decoding, arbitrary
world/funding semantics and feature proof interfaces are not established here.
Testing proof/search remains stale and unrun. Original named source refusals,
model policies and documentary proof limits remain separate and unchanged. No
new original-corpus variant association is asserted. Manifest and generated
inventory sources are unchanged, so no regeneration was needed. The original
cold exit124 at90minutes/546of685/8195923968 bytes, prior900s narrow timeout and
unrun warm measurement remain untouched.

## Reproduction and evidence

Do not rerun the successful root refresh merely to repeat timing. The final
launcher combines the individually observed steps, integrates overlay linking
before preflight, acquires the writer lock and enforces the hard cap. The
combined launcher was syntax/static reviewed; it was not rerun end-to-end to
avoid a second root compilation. On an authorized fresh private output:

```sh
scripts/run-solidity-baseline-value.sh .lake/upstream/FRESH_VALUE_OUTPUT
```

To check the retained current VM results without compiling or executing again:

```sh
python3 scripts/solidity-baseline-value-verify.py .lake/upstream/value-entry-runtime-20261028
```

`archive.json` hashes every regular file in `evidence.tar.gz` (including exact
executed Lean wrappers, successful/failed logs, private root artifacts and
snapshots). Existing shared-artifact links are represented by target/hash ledgers.
`verification.json`, `resources.json`, `validation.json`, `reviews.json` and
`handoff.json` separate runtime observations, static integrity, kernel checking
and limitations. Independent finder/skeptic reviews use no Lean server.
