# Portable evidence verification

Run from any working directory using the verifier in this checkout:

```
python3 scripts/h62/item6/migrate-solkey/verify-portable-evidence.py
python3 scripts/h62/item6/migrate-solkey/verify-portable-evidence.py --artifact-dir <retrieved-artifact-directory> --require-bulk
```

The first command checks committed repository-relative compact summaries and
producer scripts. Bulk absent means unavailable, not verified. The second
requires original-evidence.tar.gz and static-backfill.tar.gz with the exact
catalog hashes, then streams checks of selected archive-relative members without
extracting files. No VM-local absolute path, coordinator filesystem or network
fetch is assumed. Both output compatibility_accepted=false and lean_run=false.

The legacy evidence-SHA256SUMS and resume-d96f2406/SHA256SUMS are historical
artifact-root manifests, not repository-only CI gates. Their hashes are retained.
The new catalog distinguishes committed files from external H44 bulk. The full
old signatures remain inside manifested bulk; only small summaries are committed.
Visibility and new signatures remain unknown; no shim or public-API completeness
claim. Static SDK source-DAG sizes are not memory profiling or STOP clearance.

Checks: repo-only verification passes with bulk unavailable; --require-bulk
rejects missing bulk; a corrupted archive is rejected; supplied original and
static archives and every required member verify. Independent finder and skeptic
reviewed read-only without Lean/server/writes and found no new defect. Existing
Raw/RSS/H81/H78 waits remain; no statement/proof/budget/axiom change or Lean rerun.
