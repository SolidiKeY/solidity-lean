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
