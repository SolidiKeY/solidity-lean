# H28 drift reports

## H151 status of historical and fresh evidence

The missing retired final delivery at
`faca44dc415dfbdab9b9ea6b0664f1e755abaa57` and its unavailable original captures
are **UNVERIFIABLE**. Original delivery, gate and review claims below are historical
reports, not newly authenticated results. Recovery is a documented gap rather
than a wait. Available H145 private archives are not classified as missing, and
no nearby source snapshot is substituted for that final head.

A fresh reconstruction uses the current owned Python tools and a disposable
checkout at the acceptance's pinned base
`6f3eedf0788ee1f8a3bcf230558c712ecdca04d5`, tree
`114f3a4e901fc282cec56d9e210fcffb2776e0cd`. The acceptance script is byte-identical
to the authenticated original assignment: SHA256
`01a6a0a842966fa758441e3e70af53799a8d657a181540341a7bcbe759071e64`.
Its selected corpus contains 5,369 paths, including all 4,184 Lean paths at that
base. The acceptance's suffix selection and lexical/file-evidence limitations
still apply. Embedded retained diagnostics exercise multiset and source-identity
classification; they are not a fresh execution of the historical sort checker.

Fresh output must remain bound to these actual inputs and the current tool hashes.
It cannot authenticate lost worker captures, establish integration of the missing
head, satisfy a coordinator rerun, or prove Lean declarations. Timing/RSS records
are execution observations, not a before/after performance claim. All new receipts
are private under H145; old code-tree evidence paths below describe historical
locations and must not be restored.

Fresh local frozen acceptance passed for items 1, 2 and 3: each reported 31 cases,
including the complete selected pinned corpus and its scope checks. The current
tools were copied from lane source `9dab41822dba79a548d0d9d8ea7d51c69f66086a`.
Wall-time and peak-child-RSS records are archived privately. They are execution
observations, not a performance comparison or evidence of the missing head's
acceptance.
Independent read-only finder and skeptic found no boundary blocker; finder also
verified corpus counts, pinned tree and copied tool/script hashes. Neither used
Lean or reran acceptance. Coordinator rerun and task-specific final validation
remain outstanding. No code or Lean source was changed by this reconstruction.

Item 1 reads JSON from stdin and emits a complete path-sorted Lean module census. Its library labels are path-prefix classifications; the module-map counts are exact lexical token occurrences across matching Markdown files, including duplicates. Shorthand, aliases, quotations and unmatched tokens require owner review and are not confirmed drift or a deletion list. Root files are classified as root-or-other. The pinned corpus census and selected-file, fixture and external ownership snapshot are retained under `tests/h28-terra/drift-reports/evidence/`. The ownership snapshot is routing context, not proof that an individual lexical candidate belongs to a particular owner.

The frozen acceptance checks the independent mechanical output against fixtures and the selected pinned corpus. It does not establish semantic module membership or completeness of ownership assignments. No source or shared module map is modified.

The census contains 4,184 Lean paths: 450 Bridge, 266 SolidityExamples, 3,390 Solidity and 78 root-or-other. The token occurrence histogram is 4,180 zero, one with one, two with two, and one with 21. Zeros are candidates only: the map commonly uses slash paths and relative names. The family label is not an actual Lake target: for example, Corpus and Solkey have separate targets, and vendor `srcDir` changes module names. Input completeness depends on the caller providing the entire corpus.

Read-only Sol finder review found no mechanical implementation defect and independently counted the census above. Read-only Sol skeptic checked all 30 frozen fixtures and six additional edge cases, finding no implementation defect; independent corpus comparison and the census and manifest review also passed. Neither review used a Lean server.

The coordinator acceptance command for item 1 passed 31 cases including the complete pinned corpus. This is a mechanical check, not substantive owner approval. Items 2 and 3 are recorded below; owner-routing and validation backfill is retained with the item evidence.

Additional routing matches exact frozen owner-ID tokens in each source path or text against the frozen owner snapshot. These are lexical hints, including comments and quotations, not authoritative ownership; files without a match remain unassigned for owner review. See `item1-routing.json` and its positive/negative probe.

The skeptic found and verified correction of omitted dotted owner IDs and overly permissive prefix matches. Final independent replay matched all 4,184 routing rows, with hints on 351 files; the reproducible probe includes dotted IDs and prefix rejection. No substantive findings remain in the independent item 1 reviews. Coordinator rerun remains pending.

## Feature file evidence

Item 2 reports every feature whose current status is partial, missing or unsupported, preserving the original order, status, scope and missing-path occurrences. The selected pinned corpus yields 162 rows (160 partial, two missing, no unsupported). A path in `missingEvidence` is absent from the supplied file list; it does not by itself mean the path is missing from the repository. The acceptance corpus selects certain suffixes and excludes `.sol`. All 13 missing-path occurrences in its output refer to five `.sol` files that are tracked at the pinned base; `item2-tracked-crosscheck.json` records the separate complete tracked-path check. Neither path presence nor absence proves declaration semantics or feature support. Every row requires owner review and no status rewrite is made. Feature-to-evidence routing preserves each occurrence and carries lexical owner hints where available; unhinted paths require owner assignment.

Frozen Item 2 acceptance passed 31 cases, including the selected pinned corpus. Independent Sol finder and skeptic each confirmed all 30 fixture cases and full-corpus output and identified the suffix-filter caveat above. They used no Lean server. The skeptic independently verified all final feature, manifest, routing and tracked-path artifacts; no substantive findings remain. Coordinator rerun remains pending.

## Retained sort diagnostics

Item 3 compares the supplied source identity string exactly with the frozen identity and compares the diagnostic multiset with the frozen 39 lines: 37 occurrences (8 READ DRIFT, 20 UNKNOWN TOKEN, 9 UNANNOTATED READS), plus two summary lines. Duplicate occurrences matter. Both exact identity and exact multiset are required for `complete37`. The retained source identity is a supplied assertion; this report does not independently hash its sources or audit the full historical receipts. The snapshot-derived diagnostic occurrence list and conservative review routing are retained in the evidence directory. No parser or annotation is repaired.

Frozen Item 3 acceptance passed 31 cases, including the selected pinned corpus. Independent Sol finder and skeptic reviews passed all fixture and additional identity/multiset controls. The skeptic identified and verified correction of source routing to the parser, annotation table, upstream rule file and checker entry point. Coordinator rerun remains pending. Neither review used a Lean server.

## Final gate and handoff status

The bounded KeySort gate passed with Lean 4.24.0 and Lake 5.0.0; its first attempt failed due to a container cache permission and is retained. The full `run-lean.sh` gate did not finish: after 158 of 3,342 tasks, the VM headroom guard stopped its container at memory.current 12,887,789,568 bytes (4 GiB required headroom in a 16 GiB cgroup), exit 137. Two earlier setup failures (missing Git/Python and a faulty wrapper) are also retained. No full-gate pass is claimed. Coordinator acceptance reruns remain pending, as does a bounded full final gate. The retained external diagnostic snapshot is a subset, not a full historical receipt audit. All three item implementations and independent Sol finder/skeptic reviews are committed; no Lean source, generated roots, producer registry, annotation or production document was edited.

A resumed final gate using the same serial settings and a smaller 6 GiB, no-swap container also hit the VM headroom guard at 12,905,586,688 bytes after 120 seconds; it exited 137 after replaying through target 157. The retry log is `tests/h28-terra/drift-reports/evidence/full-gate-6g-retry.log`. No OOM event was observed. The full final gate remains incomplete; a runtime that can maintain the required headroom while completing the build is still needed.

After the published-master update, the pinned branch and acceptance hash were verified unchanged. A further serial full-gate retry in a 4 GiB no-swap container stopped at the VM headroom guard after 90 seconds, at memory.current 12,885,897,216 bytes; exit 137, no parent-cgroup OOM recorded. See `tests/h28-terra/drift-reports/evidence/full-gate-4g-retry.log`. This is not a final-gate pass. The published master receipt covers a different tree and does not replace this gate or the coordinator reruns.
