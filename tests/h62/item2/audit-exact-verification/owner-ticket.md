# B-MIGRATION-RAW — pinned compiler import prerequisite

Recipient for coordinator relay: `solidity-h62-6-20261106/migrate-syntax`
(`H62-6-MIGRATE-SYNTAX` in the SHA256-verified ownership snapshot).
Requester: `solidity-h62-2-20261106/audit-exact-verification`.
Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.

Unchanged `Solidity/Syntax/Raw.lean` fails official pinned Lean 4.35.0 at
597:44, 650:23, 665:27, 682:46 and 684:34: String/Slice type mismatches,
missing Slice.toList and String.dropRight, and endsWith partial-application
mismatch. This source import dependency reaches 296/305 mapped audit modules
according to the source import sweep. The other nine are independent backfill
candidates; only VisitedSet has been audited so far.

Reproduce from the task branch after installing the exact coordinator archive:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item2/audit-exact-verification/import-plan.py > /workspace/h62-audit-evidence/import-plan.txt
bash scripts/h62/item2/audit-exact-verification/bounded-check.sh imports
```

Observed exit 1; evidence `/workspace/h62-audit-evidence/bounded-imports.log`.
KeySort and the independent VisitedSet audit pass on the same official compiler.
This is a compilation dependency blocker, not evidence that any frozen theorem
is false or vacuous. No original interface changes are requested or authorized.

Requested owner action: supply an owner-reviewed v4.35-compatible syntax overlay
and its exact base/head/patch/hash for coordinator relay. Alternative: retain this
typed blocker until the syntax migration is published by its owner. This worker
will not touch that file, change the pin, or use the v4.24 cache as a substitute.
The relay.sh mentioned in the assignment is absent from this checkout; this saved
ticket is prepared for the coordinator that retrieves this VM's committed files.
