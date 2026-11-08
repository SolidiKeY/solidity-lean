# Drift report checks

The frozen `accept.py` and `item2.py` retain their exact original contract.
That contract tests evidence membership in a suffix-filtered input list; it omits
`.sol` files. A passing frozen command does not establish full-inventory evidence
completeness. Do not re-pin the contract or rewrite feature status to hide that gap.

Use the separate full-inventory check:

```sh
python3 -B scripts/h28-terra/drift-reports/item2_completeness.py
python3 -B -m unittest discover -s tests/h28-terra/drift-reports -p 'test_item2_completeness.py' -v
```

The default commit is the original frozen base. `--base` accepts only an explicit
full commit SHA; `--repo` selects its local Git repository. All pinned objects must
already be available: the check does not fetch. Git replacement objects and inherited
Git redirection variables are disabled. Output binds the complete recursive Git
inventory, tree and feature-manifest blob, with no suffix filter on existence.
Only the manifest content is read; evidence content and symlink targets are not.

Exit 0 means every declared reference in every partial/missing/unsupported feature
names a tracked regular file at that commit. Exit 1 reports missing or nonregular
references while retaining all qualifying rows and duplicate reference occurrences.
Exit 2 rejects malformed inputs or unavailable objects. Every result still requires
owner review: presence establishes neither declaration semantics nor feature support.
Features with no declared references stay explicit; their support is not inferred.

`frozenOmittedExistingEvidence` distinguishes existing paths omitted by the frozen
suffix selection from genuinely missing paths. The complete check supplements the
old report; it does not silently replace that report's meaning. Coordinator full
item-2 acceptance remains separate. Routing is not checked by these commands;
item 3 checks retained diagnostics and a supplied identity, not fresh provenance.
Raw outputs, measurements, receipts and handoffs belong in the private H145 archive.


## Routing versions and migration

Version 1 (`scripts/h28-terra/drift-reports/route.py`) is frozen. Its duplicate-ID
behavior keeps the last record. Existing callers continue to invoke it unchanged.
The user approved `Q-H152-ROUTE-CONFLICT` option A: the separate opt-in version 2
(`scripts/h28-terra/drift-reports/route_v2.py`) retains every matching ownership
record, including identical duplicates. Records are grouped by sorted ID and keep
input order within each ID; sorted file occurrences, suffix selection and lexical
boundaries retain version 1's meaning. Input remains the same JSON object with
`ownership` records and `files` containing `path` and `text`. IDs, paths and
text must be JSON strings; numeric metadata is not treated as a routing token.

Different complete JSON records for a matched ID constitute a conflict, including
metadata differences even when the owner names agree. JSON numeric tokens are
preserved exactly, so `1`, `1.0`, rounding-prone decimals and large exponents stay
distinct; key ordering alone is not a conflict. Non-JSON NaN/Infinity constants
are rejected. The CLI performs no floating-point conversion of metadata. Only affected file rows get
`conflictingIds` (sorted IDs) and `lexical-conflict-owner-review-required`.
Identical duplicate records are retained without a conflict. Unmatched conflicts
do not label unrelated files. All hints remain non-authoritative: paths, comments
and strings can match; conflicts require owner review, never automatic selection.

Run both versioned controls:

```sh
python3 -B -m unittest discover -s tests/h28-terra/drift-reports -p 'test_route*.py' -v
```

The v1 controls cover all 4,184 Lean paths at the original pinned base against a
literal-position oracle. The v2 controls reuse that full-corpus input and check
both unique and duplicate/conflicting ownership inventories. Fixture owners are
test data, not live registry or Bridge assignments.

To migrate, explicitly select `route_v2.py` in the consuming command and retain
all `ownerHints` entries; do not rebuild a dictionary keyed by ID. Handle the
conflict verdict and `conflictingIds` as mandatory review work, then compare the
versioned output on the same input. Unique-ID output retains v1 fields and lexical meaning. Ordinary values have
identical output; numeric tokens are intentionally preserved rather than v1's
normalization/rounding, even for unique IDs (for example `1e2` and large decimals).
Duplicate-ID output intentionally preserves earlier rows. Do not overwrite v1,
re-pin its tests, or silently switch an existing caller. These tests do not
establish live-owner correctness, producer completion or runtime acceptance.
