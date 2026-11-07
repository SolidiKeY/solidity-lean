# Dependency adoption, 2026-11-04

Repository: /workspace/solidity-lean
Branch: codex/solidity-sol-20261103/precompile-agreement
Assignment base: b6ba0696102a7a038afe2ed333c09dff397cc5b2
Published dependency: 6f3eedf0788ee1f8a3bcf230558c712ecdca04d5
Adoption merge: 46a0d1cbd77dd0a5fb7cece924b4c277c1f0ccc2
Parents: 465a25548d51b7485fdfd988cff717019d2a97bd and 6f3eedf0788ee1f8a3bcf230558c712ecdca04d5
The final CLOUDVM-RESULT identifies the containing documentation/seal commit.

Fetched origin/master and verified exact publication and ancestry. Existing
lane work is preserved, with no reset, push or merge into the default branch.
Read integration-20261104T042439Z-reviews.md. This increment includes no
precompile-agreement artifacts. Relevant core/vendor inputs, manifest/toolchain
and lane payload are unchanged. No new composition or logical changes made.

Post-adoption gates: source inventory PASS, 12 mutation controls PASS,
register.sh --check PASS, relevant-input git diff empty/PASS. Existing generated
roots are current, so no central registration edit was needed. Exact commands
and outputs: dependency-adoption-20261104-gates.log. No local full Lean/runtime
build was run or claimed for this adoption. Earlier KeySort evidence is historical.

Separate read-only finder and skeptic reviews both pass with no findings. They
independently verified exact parents, unchanged inputs, passing source/registration
controls and absent Mathlib Log.olean. Neither used Lean/server. Neither infers
actual-vendor proof readiness or whole-lane acceptance from integration.

The coordinator explicitly says cache delta/Mathlib delivery is separate and
pending its receipts. Required Mathlib/Data/Nat/Log.olean remains absent. No cache
retry, rebuild or pin change attempted. Original exact 898-key cache request is
preserved. No new decision requested. Existing proof goal remains blocked, not
complete, and is not recreated/reset. The prior goal-tool call lacked trusted
CCA source-turn context; get_goal is unavailable in the current catalog.

Remaining queue unchanged: arbitrary IDENTITY output/charged gas/boundaries;
all common algebraic gas, word/header proofs; inhabited/malformed/insufficient
gas EVM controls; theorem mapping, explicit axiom/trust/kernel gates, complete
acceptance, final full build/reviews and proof-complete handoff. No B16/G51,
G47 or RUNTIME_GATE_PASS claim. Original holds, statements, premises, exclusions
and proof budgets remain binding. Unsupported/fork/FFI rows stay open.

Original.patch remains the reviewed original source-inventory patch. Historical
handoffs remain evidence for their payload commits. SHA256SUMS binds current
lane documentation and adoption evidence alongside those historical artifacts.
Verify from repository root:
sha256sum --check Bridge/tests/precompile-agreement/evidence/SHA256SUMS
