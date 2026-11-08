# Immutable packet and transition reproduction

Guarded regression: a declared private receipt or synthetic fixture pass does not verify the actual published classification payload. Read immutable packet objects and compare complete prior records, scope and owner maps.

The private delivery immutable-packet-validation-v130 contains original Git objects for the published V127/V128/V129 input packets. Its proof pack includes the commit objects, the trees along the exact packet paths and the manifest/payload blobs. It is sufficient for those paths, not a full checkout or historical-evidence archive. No private HTTPS credentials are needed after obtaining the delivery.

Publication receipt: evidence: da3782f4f3a8d69f3c1a64ae59407a746c38a0cb evidence/solidity-h28-sol-20261104/automation-benchmark/

Prepare an external Git object repository with no remote, then reproduce the historical V127 input and its transition to V128:

```sh
git init --bare "$audit_packet_repo"
git -C "$audit_packet_repo" index-pack --stdin < "$audit_packet_delivery/immutable-packets.pack"
python3 scripts/h62/item2/audit-calculus/verify_packet_transition.py \
  --repo "$audit_packet_repo" \
  --before-commit 109856958e6df7a445c12b518c7da2d60a1d74af \
  --before-directory evidence/solidity-h28-sol-20261104/automation-benchmark/array-copy-inputs-v127 \
  --after-commit 4f8722f12dae4f516332d892b025def2ca09fec9 \
  --after-directory evidence/solidity-h28-sol-20261104/automation-benchmark/byte-capture-inputs-v128 \
  --out "$audit_packet_output"
```

Use absolute external directories; the output directory must not already exist. Exact historical V127 payloads are written under before, and V128 payloads under after. The immutable manifests retain the per-file sizes and SHA256 checks. Git reads retain replacement-ref, environment-routing and lazy-fetch protections. Missing objects fail locally.

For V128→V129 use the V128 commit/directory above as before, and commit2e12be5dd064c423ea37c77418d0efcd587d802a with directory evidence/solidity-h28-sol-20261104/automation-benchmark/byte-image-inputs-v129 as after. The published reports record1617→1628 (+11) and1628→1637 (+9), exact prior records/owners/scope/provenance equal. The delivery includes the exact manifests and payloads beside each report, so comparisons can be repeated independently.

This reproduction does not change the current default loader pin; tests/h62/item2/audit-calculus/BULK-INPUTS.md identifies that pin. It verifies packet bytes and transition preservation only, not the semantic correctness of classification, simultaneous witnesses, compiler totality or kernel replay. Historical unavailable evidence remains UNVERIFIABLE.
