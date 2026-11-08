# Continuous semantic validation (A05)

Operational extension of [trust and usability](trust-usability.md#principles).
All results are external executable observations. Fast mode is a verdict, never
a Lean theorem, and does not enter the core. No proof premise is discharged.

## Inventory at the assigned base

Inspected base `ee6ed004f703ff47f5d5399e1793306338e064af`.
Paths below resolve at that base; historical `Tools/` references now mean
`Solidity/Tools/`. The requested `docs/audits/prior-art-*.md` files are absent;
[architecture audit](../audits/architecture.md) documents existing runner/cache
constraints. No library interface or semantics definition is changed.

| Existing tool | Comparison | Modes | Programs / boundary |
|---|---|---|---|
| `scripts/evm-reference/replay.mjs` | Pinned solc bytecode on EthereumJS versus adapted upstream vector observations | legacy/viaIR, optimizer off for corpus replay | Admitted pinned semantic fixtures; unknown observations/host limits blocked |
| `scripts/evm-reference/generated.mjs` | `Prog.run` expected outcome, exact return/revert bytes, decoded roots and raw slots versus deployed solc bytecode | legacy/viaIR × optimizer off/on | 160 closed two-uint-root cases, ten families; same-kind boundary-pool shrinking |
| `scripts/roadmap-v17-differential.py` | Provenance-bound orchestration and revalidation of the published generated runner | all four | Original 160-case matrix, not new random programs; host-specific paths |
| `scripts/test-solidity.mjs` | Solidity source frontend/test obligations checked through Lean | source options supplied by caller | File discovery and proof/test API, no independent EVM oracle |
| `scripts/solidity-upstream.mjs` | Compiler diagnostics against pinned syntax fixtures; typed source replay against upstream semantic vectors | legacy/viaIR source scheduling; selected reference adapters | Complete archived upstream tree, partial runtime admission; refusals explicit |
| [solc validation](../solc-validation.md) A–O | A trust lint/axioms; B facts; C machine oracle; D generated harness; E inputs; F upstream; G rule oracle; H mutation; I translation validation; J rule map; K prediction; L adversaries; M symbolic completeness; N reflection; O automation | Individual components, not a unified claim | D already has bounded 160-case increment; B–O remain broader obligations |
| [alignment](../solc-alignment.md) | Explicit model boundaries and known evaluation-order/copy deviations | Legacy/viaIR distinctions | A matching finite trace never establishes universal compiler equivalence |

The existing engine uses Osaka, a 1,024-word stack, 100-million gas allowance,
disabled code-size caps and a separate five-million-instruction host cap.
Its adapter refuses nonempty logs. The admitted generated grammar emits no
logs; this lane claims no event/log feature coverage. Arithmetic panic bytes,
empty revert and transaction rollback are observed, including both storage roots.

## Reproduction and admission

Use the repository's writer lock and resource policy before Lean execution.
The standalone `scripts/differential/Driver.lean` imports the existing SolCases
adapter; it adds no library module or public theorem. Generated roots and module
maps therefore require no new rows. Restore fetched artifacts as documented in
[contributing](../contributing.md#build-cache-and-ci) before `lake env lean`.

```sh
lake build Solidity.Tools.SolCases
python3 scripts/ci/restore-lake-artifacts.py
npm ci --ignore-scripts --prefix scripts/evm-reference
node --test --test-concurrency=1 scripts/differential/run.test.mjs
node scripts/differential/bounded.mjs --compiler /path/to/pinned-soljson.js --out /external/new-corpus --count 20 --seed 1108 --budget-seconds 840
timeout --kill-after=10s 28800s node scripts/differential/run.mjs --compiler /path/to/pinned-soljson.js --out /external/new-nightly --count 10000 --seed 1108 --budget-seconds 28800
```

The first twenty cases exercise each existing family with zero/maximal starting
roots. Subsequent cases select families and 256-bit operands with a deterministic
64-bit LCG, with boundary bias. Family selection and each operand bias use
separate draws and high bits; per-family outcome and boundary counts are reported. This is random sampling within ten existing
well-typed templates, not arbitrary typed AST coverage or cryptographic randomness.
Admission and `Prog.run` observations are computed by Lean; JavaScript never
substitutes an arithmetic oracle. Refusals, mismatches and blocked modes all
prevent a passing exit. The report includes the complete per-mode denominators.
Shrinking re-runs Lean for each smaller operand and preserves family/mode;
one greedy pass is a local reduction, not a global or cause-preserving minimum.

The internal `--budget-seconds` is a soft execution-loop budget, excluding
generation and unable to interrupt a running EVM call or shrink. The bounded
entry point uses the existing process-group supervisor to enforce 840 seconds
across the entire child process; timeout is failure, never agreement. CI also
bounds the complete job to 15 minutes. Nightly must use its own outer timeout.
Reports separate end-to-end time from execution-loop time.

## Triage

Every mismatch requires independent reproduction with the emitted source and
shrunk operands. Classify as a harness bug, a semantics bug requiring a source
owner ticket, or an already documented solc/EVM-version deviation with a precise
alignment citation. Unknown causes remain open mismatches; never automatically
label them expected deviations. New alignment rows are proposals here, because
`docs/solc-alignment.md` is outside this lane's write scope.

Fixed external adapter controls (not Lean differential results) exercise all
four modes, deliberate mismatches and nonempty-log refusal. No executed Lean
agreement numbers or disagreement classifications are available yet.
The corpus and 10k runs are pending the Lean resource gate.

Input snapshots include the installed dependency tree and lock versions; any
changed execution input prevents a passing report. This records runtime trust,
not a kernel proof or V17 provenance certification.

## Waits and owner questions

`VA3-R1` [AGENTS.md; resource policy; launch H137]: required systemd user scope
cannot start on this VM (no user bus). Choose either provision the required
scope/reserve, or explicitly authorize an equivalent bounded no-swap runner
with a compatible reserve. Required Lean diagnostics, checkpoint/full gates,
corpus and random execution remain pending; lightweight work continues.
Question sent through `scripts/coord-tools/coord-ask`. H183 selected provisioning
the unchanged scope/reserve. Provisioning checks found PID 1 is `tail`, no systemd
manager or user runtime, no sudo, and an undelegated root-owned cgroup. Local
unprivileged setup cannot provision the required host reserve; provider or
coordinator action remains necessary. No alternative resource policy is used.

## Review log

Independent Codex finder and skeptic reviews used read-only sandboxes, without
the Lean server. Both identified the soft loop timer being insufficient for
end-to-end bounding: added the existing process-group supervisor entry point
and separate timing fields. Finder identified missing inbound documentation
navigation: exact owner diff below. Both reviews also found late/incomplete provenance: capture source/dependency,
compiler, Node, Lean/Lake and Git identities before execution, verify unchanged
afterward. Skeptic found correlated family/boundary choices: use separate draws
and high bits, and publish per-family outcome/boundary counts. Re-review confirmed these fixes. Finder requested explicit build/restore steps
for fresh checkouts; added them. Skeptic requested an outer nightly timeout and
persistence before shrinking; added both. Each observation is appended before
shrinking, and shrink errors preserve the original mismatch as incomplete triage.
No milestone is complete before its required gate and review.

## Handoff

Inventory and harness source prepared; required Lean checks and execution are
pending. Generator execution, triage and lane-end validation are not complete.
The CI owner proposal is prepared but not applied or execution-validated. No successful RUNTIME_GATE_PASS is claimed. Lightweight trust, path, generated
root/fragment and axiom-pin checks pass. Navigation correctly fails until the
CI/documentation owner applies the exact catalog diff below; this lane does not
modify the leased catalog. No new axioms, theorem declarations or `sorry` are
introduced.

## CI and documentation owner proposal

The following is an exact proposed diff, not applied outside this lane's scope.
The CI owner must provision the proposed `lean-bounded` self-hosted runner label
with the repository's systemd memory/no-swap limits and reserve, and enforce
those limits for the build and test command. This is a prerequisite, not a
claim that an ordinary hosted runner meets those constraints. The job's hard
15-minute timeout includes setup/build; incomplete runs fail. The bounded
entry point limits the test child to 14 minutes independently.

```diff
diff --git a/.github/workflows/differential.yml b/.github/workflows/differential.yml
new file mode 100644
--- /dev/null
+++ b/.github/workflows/differential.yml
@@ -0,0 +1,39 @@
+name: semantic-differential
+on:
+  pull_request:
+  workflow_dispatch:
+permissions:
+  contents: read
+jobs:
+  corpus:
+    runs-on: [self-hosted, linux, lean-bounded]
+    timeout-minutes: 15
+    env:
+      LEAN_NUM_THREADS: 1
+    steps:
+      - uses: actions/checkout@v5
+      - uses: actions/setup-node@v4
+        with:
+          node-version: '22'
+      - uses: leanprover/lean-action@v1
+        with:
+          build: "false"
+          use-github-cache: "false"
+          use-mathlib-cache: "false"
+          test: "false"
+          lint: "false"
+      - run: bash scripts/ci/fetch-lake-cache.sh
+      - run: lake build Solidity.Tools.SolCases
+      - run: python3 scripts/ci/restore-lake-artifacts.py
+      - run: npm ci --ignore-scripts --prefix scripts/evm-reference
+      - name: Fetch compiler (harness verifies exact SHA and version)
+        run: curl -fL --retry 2 https://raw.githubusercontent.com/ethereum/solc-bin/gh-pages/bin/soljson-v0.8.38+commit.1835d247.js -o "$RUNNER_TEMP/va3-soljson.js"
+      - run: node --test --test-concurrency=1 scripts/differential/run.test.mjs
+      - name: Compare corpus in all four modes
+        run: node scripts/differential/bounded.mjs --compiler "$RUNNER_TEMP/va3-soljson.js" --out "$RUNNER_TEMP/va3-corpus" --count 20 --seed 1108 --budget-seconds 800
+      - uses: actions/upload-artifact@v4
+        if: always()
+        with:
+          name: differential-observations
+          path: ${{ runner.temp }}/va3-corpus
+          if-no-files-found: error
```

The new guidance needs this exact inbound-link owner edit. Its additional
`docs/document-index.md` generated catalog change must be produced by the owner
with `python3 scripts/check-doc-navigation.py --write`, then checked.

```diff
diff --git a/docs/feature-work/trust-usability.md b/docs/feature-work/trust-usability.md
--- a/docs/feature-work/trust-usability.md
+++ b/docs/feature-work/trust-usability.md
@@ -33,1 +33,3 @@
+See [A05 differential commands and admission](va3-differential.md).
+
 ## Groups
```

Nightly owner configuration should run `--count 10000` with independently
recorded seeds, a larger explicit outer process-group timeout (for example
8 hours), and the same exact compiler lock and four-mode denominator. Preserve
all failures/refusals and shrink candidates; retain raw observations outside
the code branch. No nightly result is asserted until the VM run completes.

Exact generated catalog owner diff (computed without modifying the catalog):

```diff
--- a/docs/document-index.md
+++ b/docs/document-index.md
@@ -198,6 +198,7 @@
 - [docs/feature-work/transient-storage.md](feature-work/transient-storage.md)
 - [docs/feature-work/trust-usability.md](feature-work/trust-usability.md)
 - [docs/feature-work/v13-public-compiler-total.md](feature-work/v13-public-compiler-total.md)
+- [docs/feature-work/va3-differential.md](feature-work/va3-differential.md)
 - [docs/feature-work/vy5-composition.md](feature-work/vy5-composition.md)
 - [docs/feature-work/vy5-natural-account.md](feature-work/vy5-natural-account.md)
 - [docs/feature-work/vy5-source-release.md](feature-work/vy5-source-release.md)
```
