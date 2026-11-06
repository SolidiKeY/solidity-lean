# Verifying the portable audit evidence

The committed evidence-manifest.json pins repository-relative checker sources
and archive-relative data files. Bulk census and kernel records stay outside
Git. The checker and all frozen mapped source pins can be checked directly
from the repository, without any VM artifacts:

```sh
python3 scripts/h62/item2/audit-evm-compiler/verify_evidence.py --sources-only
```

This mode explicitly verifies zero artifacts. To verify data, download the
evidence archive reported in CLOUDVM-RESULT and run from this checkout:

```sh
python3 scripts/h62/item2/audit-evm-compiler/verify_evidence.py --archive /path/to/audit-evidence.tar.gz
```

For an unpacked archive, use `--artifact-root /path/to/continuation-2` instead.
The verifier checks source fingerprints and artifact bytes without extracting
tar members or requiring any original VM path. A mismatch fails the command.
It does not re-run Lean or establish proof validity from a checksum.

The data records 555 checked candidates, of which 235 are literal equality
propositions with no inputs after definition-aware telescope expansion. Their
unchanged original kernel-checked proofs are retained. No replacement True
lemmas are generated. Other candidates remain pending. The combined ledger
uses the committed 65 manual links plus closed-coverage.json; exact-once and
frozen-signature checks are mandatory when reconciling them.

The producer commands are in closed_census.py, manifest_evidence.py and
reconcile.py under the same scripts directory. Run the first under the writer
lock with serial Lake configurations after building the frozen mapped modules.
Its `--census` seed is the manifested seed-census.json, the preceding
65-link full statement census. The kernel and ownership inputs are also
manifested; no coordinator-local input path is required. Compile the unregistered
JointImpossible and JointWitness audit helpers into the chosen serial config
lib/lean/tests/h62/item2/audit-evm-compiler directory before running the classifier,
using explicit -j1 and --tstack=131072. `--evidence` selects
an external output directory; the core and Bridge config/package arguments
select local paths prepared with prepare.py and prepare_bridge.py. No VM path
is compiled into the checker. Reconcile the result using the original source
census, kernel capture and manifested ownership snapshot, adding
`--additional-coverage` for closed-coverage.json. Generate the committed manifest
only after successful gates and reviews. Timing/resource receipts record actual
runs and are not expected to reproduce identical timing bytes on another VM.

Closed-input accounting proves no semantic nonvacuity, supported-program
totality, compiler equivalence or execution-gas theorem. The remaining ordinary
statements still require simultaneous witnesses; H69 intentional impossibility
results retain their separate classification.
