# C3 gate-preserving re-cut (historical intermediate version)

CURRENT: the optional receipt adapter described below was subsequently removed.
See EVIDENCE-AUTHORITY-HANDOFF.md. The live checker is byte-identical to21043
and uses tracked evidence unconditionally; the earlier optional-adapter review
is not acceptance authorization.


Coordinator hold: c7c5685e4 at merge b7c3cc511. The previous successor upstream
pin change, mandatory direct-audit check and MCP acceptance alternative were
gate changes without owner approval. They are withdrawn, not grandfathered by
H82. No new gate/pin authorization is requested or claimed in this re-cut.

Original authenticated policy is restored from final member21043c5220a7c0390810ec7088c83a6bd9c8ff8c:
ADOPTED_UPSTREAM=e6849d3bdf516099d20c33d3581d523449764018; original BASE,
ALLOWED, TOOLING snapshot set, lake-build command, all resource/axiom/witness/
source/final requirements remain unchanged. No required direct-audit evidence
or MCP substitute remains. The runtime recorder uses the original snapshot
field set again. No Lean theorem, premise, budget, source or exclusion changed.

The only checker adapter chooses an optional hash-bound successor log/receipt
pair. If its manifest, pair entries or either artifact is absent, BOTH paths
fall back to the original tracked evidence. Available complete pairs must be
inside the C3 area and match committed digests. Changed available bytes fail;
missing artifacts do not introduce a clean-checkout exception. Fixture receipt
overlays retain their original behavior. SUCCESSOR-EVIDENCE now lists only the
four original-role log/receipt paths; MCP diagnostics are supplementary history.

Tests: six PASS, including a mechanical AST comparison against21043. After
normalizing only evidence-location calls and removing the added resolver, the
entire module AST equals the original: every original function, constant, pin
and gate condition is preserved. Other tests cover ordinary exit7, SIGTERM143,
complete-pair digest mutation, partial-pair fallback, path escape and all four
roles with no successor files present.

A disposable detached checkout at the pre-recut head was populated only with
tracked files plus the candidate scripts/selector. All successor artifact paths
were absent. The checker reached tracked evidence without FileNotFoundError,
Traceback or a required-direct-audit error. It correctly exited1 with the
original policy refusals: tracked/untracked write scope violation and audit
receipt source snapshot drift. Those failures are NOT relabeled passing gates.
The approved e684 pin is not silently advanced to make the consolidated branch
pass. New receipt generation cannot waive the original scope restriction.

Earlier successor checkpoint PASS results were produced under the withdrawn
gate/pin edits and are historical only, not approved acceptance. Independent
compiler/MCP observations remain preserved, but MCP does not replace the lake
run in the restored acceptance checker. All original final obligations remain
open. The earlier signed/intake metadata and final C3 head remain integrated;
no retirement acknowledgement or frozen prompt is missing now.

Ready remediation is complete. Remaining waits: owner-approved acceptance route
for the consolidated branch under the unchanged e684 pin; shared registry and
full-runtime/cache/final-gate readiness; original external C3 runtime/seal/cache
bytes. No known timing STOP was retried and no unrelated scope was taken.
Current recut outputs are in tests/sol-c3-exactness/.artifacts/gate-recut and
hashed by GATE-RECUT-SHA256SUMS. Bulk remains off Git under H44. Existing goal
identity is retained; no master push, retired-goal wake or completion claim.

Repository-wide check-doc-paths.sh currently exits1 on five references outside
this lane (H62 infer-helper/migration/generic-structuredflow docs and a census
script). The full decisive output is retained in gate-recut/doc-paths.log; no
missing C3 reference was reported. Those files were not edited and the failure
is not marked passing. This is an additional shared documentation-owner wait.
