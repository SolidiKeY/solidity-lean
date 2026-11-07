# H70 typed helper compatibility interface

Standalone H55 backfill at frozen base `4d3790eadb8a5212233bc7d5e345817476b2f590`, on top of checkpoint `dc93ed60f5b2ed4cbf361bc20e9db69c9620e904`. This transfers no original-file ownership and implements no helper extraction or inferencer unification.

`tests/h55/source-relations/HelperCompatibility.lean` compares both helper copies with each original inline Typed premise; retains both delete guards, elementary-conversion eligibility, the input derivation, arbitrary exact result type and explicit conversion test; constructs all six typed applications; and targets the existing delete_res/payable_mem/convElem_mem membership statements without editing them. Controls distinguish non-mapping from deletability using calldata bytes and retain conversion refusal.

Status: standalone source check PASS; independent read-only finder and skeptic source reviews found no contract issues. Current H55 toolchain: Lean 4.24.0/Lake 5.0.0-src+797c613. H62 uses a different base and reports Lean 4.35; this interface is not evidence for that candidate/toolchain. No Lean MCP diagnostic tool is exposed here. No 4.35 artifact will be loaded into this build.

H62 candidate and scanner files have not been retrieved or reviewed. Its handoff supplies no extraction module or exact original-file patch. InferComplete remains outside the original H55 existing-file list; producer file transfers still require coordinator notice, accepted handoff and exact transferred paths.

## Exact interface and boundaries

| Original relation / consumer | Checked interface |
|---|---|
| Typed.delete / delete_res | sourceDelete and staticDelete retain the identical LVal witness, non-mapping test, deleteRefused=false and tuple[] result. delete_constructor_exact gives equality of the constructed derivations. delete_consumer gives the original exact Res.expr membership in prefixOne; it is not a new theorem about complete expression inference. |
| Typed.payable / payable_mem | Both applications retain the Typed witness and address-or-contract=true guard, producing address true. The exact constructed Res.expr remains a member of infer when the input derivation has the original Res.expr membership. |
| Typed.convElem / convElem_mem | Both applications retain el!=addressPayable, Typed input, arbitrary result type, result-location equality and explicit-conversion=true. The constructed derivations are equal, and the exact constructed Res.expr remains a member of infer under the unchanged input membership premise. |

Six equivalences compare the helper tests/locations with the original inline relation expressions. Two guard-pair equivalences preserve delete refusal and conversion checks. The guards alone assert neither LVal nor Typed nor constructor eligibility; the six typed adapters carry those separately. No premise is added to a production theorem or dropped from its original statement.

The negative controls concern these rule guards, not refusal of every possible checker path. Calldata bytes are a concrete non-mapping type with deleteRefused=true, so passing the mapping test alone is insufficient. An array containing a mapping passes only the top-level mapping test; no deletability claim is made. Address flags, contract type, bool payable refusal, every bytes/string location and default location are also covered.

## Validation

Evidence: `/workspace/source-relations-evidence/helper-compatibility/`, plus sibling runtime directories `helper-compat-keysort-01` and `helper-compat-proof-01`. Exact argv, logs, source snapshots, runtime limits and samples are retained.

- Authenticated all 94 earlier dependency source/object hashes and both Lean/Lake executable hashes against the sealed cache manifest before checking. No H62 or 4.35 object was reused.
- Actual Lean 4.24.0 (797c613), Lake 5.0.0-src+797c613, bounded KeySort PASS in 4.589 seconds.
- Bounded source command: `timeout 300 lean -j1 --tstack=131072 -o /workspace/source-relations-evidence/helper-compatibility/HelperCompatibility.olean tests/h55/source-relations/HelperCompatibility.lean`, with LEAN_PATH pointing to the authenticated local objects. PASS, HELPER_COMPATIBILITY_PASS, 2.746 seconds, before/after source snapshots equal.
- All 25 manually listed theorem reports are clean: 19 use no axioms; six use only propext, Classical.choice and Quot.sound. No sorry, new axiom, maxHeartbeats change, or trust shortcut. Six #check reports expose the full typed adapter signatures. This is direct reporting, not the H58-held generated audit.
- Existing bounded runner enforces 12 GiB memory, equal memory+swap limit, one CPU, no network, LEAN_NUM_THREADS=1 and a 4 GiB reserve. Each proof invocation has explicit -j1 and timeout300; wrapper maximum wall is 600 seconds. Both runs retained more than 15 GiB available. No LSP/server or Lake setup-file child ran.
- Initial setup stopped before source edits or Lean because the temporary lock parent disappeared across VM startup. Recreated the missing directory and acquired the standard writer lock; no existing reservation was reset. The setup failure is retained.

Independent finder and skeptic reviewers read the source and original contracts without Lean/server/builds, edits or network. Both found no contract issue. They confirmed the delete consumer's deliberately local prefixOne conclusion and the complete conversion/result-type premises. Final evidence/handoff verification follows in their saved reports.

No production checking-speed change exists: this unregistered standalone file changes no production build/import graph. No before/after migration timing, required MCP diagnostic, run-lean.sh/full affected-module gate, H62 candidate elaboration, 4.35 compatibility or Terra full-scope acceptance is claimed. Those obligations remain open for the original complete assignment.

## Coordination result

H55's existing helper copies are compatible with these frozen inline rule guards and the three named Static consumer interfaces, at the authenticated H55 source blobs/toolchain. This is not approval of an unprovided H62 extraction module or migration patch and transfers no original-file write authority. No hash/language owner overlay was applied. Inferencer unification and complete Source/model relation work remain with H55's original scope and are still blocked on exact transfers.

The coordinator should retrieve this exact standalone source and result, and the still-unavailable H62 scanner/candidate sources plus their immutable manifest before requesting an independent H62 source review. The reported H62 receipt SHA b49dc86b22dc30e75af9b89f75427d454aed2254451221d67b5262c8a83302b7 is routing evidence, not a locally verified file.

Existing `/workspace/source-relations-artifacts/` exports remain immutable historical artifacts at dc93ed60f5b2ed4cbf361bc20e9db69c9620e904. This addendum is exported separately under `/workspace/source-relations-artifacts/helper-compatibility-20261106/` with the new committed head, full patch/bundle, raw evidence and cache delta checksums. Bulk data stays off git; no ship-cache.sh, push or merge.
