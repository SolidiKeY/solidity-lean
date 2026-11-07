# Bounded handoff byte receipts

Guarded regression: a truncated handoff display must not be reported as a complete artifact pull or proof validation. The bounded index prints four artifact bindings and a manifest hash after checking every listed local artifact.

Run `python3 scripts/h62/item2/audit-calculus/handoff_index.py /absolute/handoff/directory`. The read-only helper streams SHA256 verification for every flat SHA256SUMS entry, requires HANDOFF.md/gates.json/evidence.tar.gz/original.patch, rejects missing files, symlinked artifacts/manifests, duplicate/self-referential or non-flat names, oversized manifests and more than64 entries. Output is bounded by four selected entries, not handoff or log length. It does not parse semantic claims or trust a handoff's reported gates; filenames/bytes/hashes are the only verification boundary.

The selected paths identify local bytes only. Coordinator retrieval, census completeness, semantic acceptance, Lean/axiom/kernel/runtime validation and any gate interpretation remain separate obligations. Use an immutable saved packet without concurrent writers. Synthetic positive/negative tool controls do not prove Solidity/Lean statements. Existing artifact bytes/manifests are read unchanged; no historical missing bytes are reconstructed or called identical.

No census credit:1001 reviewed/4282 pending of5283,1537 unresolved owners and zero fresh joint witnesses remain. Original queues remain unfinished. No source, statement, dependent definition, budget, axiom, exclusion or toolchain change; H28 dependent proof/replay pause and Raw/Context waits retained. Bulk evidence remains off Git with path/size/SHA manifest, coordinator-pending. No STOP release.

Accounting and115controls PASS; documentation path gate PASS exit0. Complete acceptance remains FAIL exit1:4282 classifications pending. No proof/runtime acceptance.
