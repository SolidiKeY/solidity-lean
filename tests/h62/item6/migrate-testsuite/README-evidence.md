# Portable evidence verification

Run from the repository root. All paths in `evidence-manifest.json` are
relative to either the checkout or a supplied external evidence root. The
`recorded_evidence_root` is historical receipt provenance, not a required VM
location. Bulk outputs remain external under H44.

```sh
python3 scripts/h62/item6/migrate-testsuite/verify-evidence.py
```

Without external evidence this checks the checkout, prints `pending_artifacts`
and exits 2. A source mismatch fails. Explicitly supplied missing external files or an absent
archive also produce pending; present files with wrong hashes fail. It never reports full evidence acceptance
from a checkout alone.

Download the artifact named `evidence.tar.gz` whose bytes and SHA256 are in the
committed manifest, then pass its local path:

```sh
python3 scripts/h62/item6/migrate-testsuite/verify-evidence.py --archive /path/to/evidence.tar.gz
```

The verifier hashes the compressed archive and every required member, streams
it without extraction, and rejects missing/duplicate required members. The
archive can contain additional historical diagnostics. Alternatively supply
an already-unpacked evidence directory; its absolute location may differ from
the capture VM:

```sh
python3 scripts/h62/item6/migrate-testsuite/verify-evidence.py --evidence-root /path/to/evidence
```

This verifies the 333 pinned closure sources plus the manifested Python/shell lane tools
and fixtures, and separately the selected old-build/interface/API evidence.
It establishes byte integrity/source provenance, not proof validity, a fresh
build, export accessibility, H78 parity or RUNTIME_GATE_PASS. New compilation,
104 compiler-only signatures, export visibility, shims and full comparison
remain pending.

`public-api-report.py` can replay the old inventory after relocation. Pass
`--artifact-root` for the supplied evidence directory and `--recorded-root`
for the manifest's historical `recorded_evidence_root`; the other input files
are the relative paths listed in `evidence_files`. The compiler summary's
captured log/fixture paths are mapped explicitly into that directory, checked
against the actual files and pinned versions, and never executed. Output
provenance paths are relative to `--artifact-root`. No Lean job is started.

To regenerate the manifest from the preserved evidence and archive:

```sh
python3 scripts/h62/item6/migrate-testsuite/make-evidence-manifest.py --evidence-root /path/to/evidence --archive /path/to/evidence.tar.gz
```

The generator checks closure hashes against the accepted census and emits
stable JSON to stdout. The checked-in manifest authenticates the existing
historical archive; it does not promise that nondeterministic measurements
will regenerate identical bytes.
