# TF-seal fixture handoff

H151 status: the unavailable exact retired artifact-fixtures final delivery
`9cc85b14fa3f611e183379c257b10b19e1aa5325` and missing original captures are
**UNVERIFIABLE**. Their historical claims remain unproven; recovery is a documented
gap rather than a wait. Available source and available private archives remain
usable, without treating them as that missing final delivery.

Fresh local acceptance on source `dc9716659ba0442cdbe7cac4511f5fbef3e7cc46`
passed all 12 named seal cases without skips. The real production seal script
still matches the frozen contract's SHA256
`1fff7ac6e3082b2fd017e21c5c5d09107851de9c8ea08bb3386f6bd56da1a6d3`.
This is a new current-source fixture result, not authentication of lost captures,
final-head integration, coordinator acceptance, Lean proof or runtime qualification.
The command was `python3 -B tests/terra-20261103/seal/accept.py`.
Raw output, source hashes and resource records are private under H145; historical
VM log references below describe their earlier locations and must not be restored
to the code tree. No production source or frozen acceptance was changed.
Independent read-only finder and skeptic found no blocker in the 12-case contract.
The optional commit-argument path check was not invoked. The named tamper cases
do not establish authenticity against a fully rewritten manifest and bundle;
trusted external source/head identification remains necessary. Neither reviewer
reran tests or used Lean.


The pinned `scripts/coord-tools/seal.sh` is exercised with real Git in separate disposable repositories. The fixture checks the full generated inventory, manifest, checksums, bundle head and prerequisites, and rejection after tampering. No Lean, network, containers, host cleanup, or production downloads are involved.

Cases: `usage` checks invalid invocations; `clean_roundtrip` checks creation and verification; `base_merge_base` checks a diverged base; `manifest_tip` and `manifest_base` reject altered metadata with recomputed checksums; `bundle_prerequisites` checks the prerequisite and rejects an invalid base; `missing_file` removes each generated file; `extra_file` checks both unlisted and checksum-listed extra files; `corrupt_bundle` checks corruption before and after updating metadata and sums; `corrupt_checksum` checks a modified digest; `empty_range` checks refusal; `paths_with_spaces` checks repository and output paths with spaces.

Acceptance command: `PYTHONDONTWRITEBYTECODE=1 python3 tests/terra-20261103/seal/accept.py`. Actual result: 12 tests ran and passed (1.349 seconds); acceptance printed `TF-seal` with `count: 12` and `status: PASS`. The saved log is outside the checkout at `/workspace/terra-artifact-fixtures-evidence/seal-accept.log`.

Read-only finder review by the implementer: checked the case list, pinned hash, temporary repository isolation, generated file inventory, metadata, and tamper checks. Read-only skeptic review by the implementer: checked that the tool is real, Git is real, test mutations are verified rather than mocked, and no Lean or external service runs. These are self-reviews; the separate coordinator Sol finder and skeptic reviews remain pending. The prerequisite fixture covers a single base prerequisite; it does not exercise a bundle with multiple prerequisites.
