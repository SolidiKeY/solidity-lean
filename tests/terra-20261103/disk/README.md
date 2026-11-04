# TF-disk fixtures

Run `PYTHONDONTWRITEBYTECODE=1 python3 tests/terra-20261103/disk/accept.py` from the checkout root. The pinned script is exercised with real disposable Git repositories and bundles. Fake docker and podman record calls and return two exited IDs; no real container daemon is contacted. Cgroup files are simulated. Tests do not prove behavior of real container engines, host storage or Lean.

Case assertions:

- report_only: no cleanup or container calls; the full build and both seal trees remain byte-identical.
- missing_cgroup: absent memory files report unavailable.
- real_worktree_build: only an extra worktree's real build is deleted.
- symlink_lake_preserved: an external symlinked .lake remains untouched.
- symlink_build_preserved: a symlinked build and its target remain untouched.
- main_build_preserved: the main worktree's build remains.
- extra_seal_file_preserved: an unlisted file disqualifies a seal from removal.
- invalid_checksum_preserved: tampered checksum and checksum-valid missing, malformed and truncated bundles are preserved; a valid older control is deleted.
- git_directory_preserved: a seal containing an empty .git directory remains intact without an unlisted-file confound.
- newest_seal_preserved: the newest verified seal remains byte-for-byte intact.
- older_valid_seal_removed: an older verified bundle is removed.
- exited_containers_only: both mock engines are queried with the exited filter and only returned IDs are removed.
- invalid_usage: invalid arguments fail before cleanup and preserve seeded build and seal trees byte-for-byte.

Acceptance: `PYTHONDONTWRITEBYTECODE=1 python3 tests/terra-20261103/disk/accept.py` ran 13 tests in 0.940s, OK, PASS. Log: `/workspace/runtime-fixtures-evidence/disk-correction-accept.log`. Frozen acceptance SHA-256: `cdde8bca6fc9d9692d6c4e7f09c3e141ba21b177a278a02db4dc911fb87e20fb`.

The initial coordinator substance review failed: an unlisted .git/config masked the .git guard; negative seals did not test malformed or missing bundles; report-only and invalid-usage preservation checks lacked complete seeded artifact comparisons. The correction uses an empty .git directory, checksum-valid invalid bundle controls including a pack that verifies but cannot unbundle, a valid older deletion control, and complete before/after snapshots. Original review evidence is retained at `/workspace/runtime-fixtures-evidence/disk-original-review.txt`.

Fresh independent read-only gpt-6.1-sol finder and skeptic reviews each passed with no confirmed findings; their summarized evidence is in `/workspace/runtime-fixtures-evidence/disk-correction-reviews.txt`. No Lean server was used. Coordinator committed-item acceptance and review remain pending.

Coordinator review follow-up: protected extra-file seals are compared by complete byte snapshot; both symlink targets are compared before and after cleanup. Frozen acceptance, named cases and production script are unchanged.
