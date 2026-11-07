# Numeric-literal proof checkpoint handoff

Status: **blocked at coordinator registration / full runtime gate**. The scoped
implementation and backfill are complete; this is not assignment completion.

- Batch: solidity-sol2-20261104; slug: numeric-literals.
- Repository: /workspace/solidity-lean.
- Branch: codex/solidity-sol2-20261104/numeric-literals.
- Published base: 6f3eedf0788ee1f8a3bcf230558c712ecdca04d5.
- Validated implementation head: ebb4d3257694880f45b3591435cb270200d5ed2c.
- The sealed packet records its containing final commit, original patch, bundle,
  absolute artifact paths and SHA256 manifest. This committed file avoids a
  self-referential containing-commit hash.

## Implementation acceptance

All 42 modules, 652 authored declarations and 991 kernel declarations are
inventoried in acceptance.json / kernel-inventory.json. Full theorem signatures,
universe parameters, safety flags and actual transitive axiom sets are included.
The 991 actual axiom sets are: 803 empty, 93 propext, 89 Quot.sound+propext,
6 Classical.choice+Quot.sound+propext. No new axiom or unsafe declaration exists.
The one partial entry is Lean's generated safe underscoreOk._unsafe_rec helper,
not an authored partial/unsafe proof escape. Audit persists no declarations.

Independent byte-spelling relations and universal iff results cover digitsTail,
digits1, hexDigits, decNumber and hexNumber with exact suffixes and fields.
Whole-spelling underscore erasure, arbitrary decimal accumulator/concatenation
and raw-hex folds, scale/exponent Q interpretation, classification, arbitrary
refusal families, exact spans/slices/glue and denomination separation are proved.
No producer or Source/Syn/type representation changed. EIP-55 is the existing
deterministic flag, without a cryptographic equality claim.

There are 32 inhabited constructor witnesses, 68 scanner controls and 42 typed
Lean/compiler spelling fixtures. Kernel theorems check all typed fixture rows.
The fixed solc is 0.8.38+commit.1835d247.Emscripten.clang, SHA256
6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390.
All 18 accepted values match exactly; all five stage differences remain explicit.
External compiler/Python tests do not prove universal compiler parity. The
upstream baseline-20261028 and every shared trust/registration file are unchanged.

The final implementation command is:

    python3 scripts/check-sol-numeric-literals.py --implementation --self-test

The default command refuses completion while registration/runtime/final handoff
obligations remain open, and additionally requires committed inputs, stamped
reviews, actual root/map registration, a verified current-head seal and live
passing full gates. Pins are recorded only by the explicit make-manifest script.

## Actual gates and resources

Lean 4.24.0, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b;
Lake 5.0.0-src+797c613. See evidence/runtime-versions-actual.log. The earlier
non-strict wrapper version probe printed an error and is not a passing check.
KeySort per-file MCP diagnostics passed: zero errors, 2.059 seconds.
All proof modules passed per-file MCP; the full touched closure passed 49 jobs
in 218.660 seconds (peak child RSS 2105736 KiB). After the metadata-only Audit
raw-string correction, the same closure passed again in the full suite.

Every check uses the approved 12 GiB, swap=0, CPU=1 Docker envelope, activation
before LEAN_NUM_THREADS=1, explicit Lean -j1 and the global writer lock. The
owned shim serializes the shared corpus's concurrent probe launches. Docker
image: ubuntu@sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852.
The H1 reserve is min(VM MemAvailable, parent memory.max-current), sampled during
checks, required >=4 GiB. No address-space substitute or raised proof budget.

The unchanged gate.sh full run exited 1 after 2949.590 seconds. Maximum Linux
child RSS was 5656896 KiB; cumulative container peak 8661929984 bytes; minimum
parent headroom 7935414272 bytes; no resource stop. These are distinct metrics.
Per-file MCP process RSS was not separately measured; its aggregate cgroup peak
and timings are retained. No RUNTIME_GATE_PASS is claimed.

| Gate | Command | Result / seconds | Evidence |
| --- | --- | --- | --- |
| build-touched | `build_touched` | pass / 20 | /workspace/solidity-lean/tests/sol-numeric-literals/evidence/recovered-full-gates/1.log |
| run-lean | `bash run-lean.sh` | fail / 0 | /workspace/solidity-lean/tests/sol-numeric-literals/evidence/recovered-full-gates/2.log |
| trust | `bash scripts/check-trust.sh` | pass / 11 | /workspace/solidity-lean/tests/sol-numeric-literals/evidence/recovered-full-gates/3.log |
| orphans | `node scripts/check-orphans.mjs` | fail / 1 | /workspace/solidity-lean/tests/sol-numeric-literals/evidence/recovered-full-gates/4.log |
| layers | `node scripts/check-layers.mjs` | pass / 0 | /workspace/solidity-lean/tests/sol-numeric-literals/evidence/recovered-full-gates/5.log |
| roots | `bash scripts/coord-tools/register.sh --check` | fail / 0 | /workspace/solidity-lean/tests/sol-numeric-literals/evidence/recovered-full-gates/6.log |
| doc-paths | `bash scripts/check-doc-paths.sh` | pass / 10 | /workspace/solidity-lean/tests/sol-numeric-literals/evidence/recovered-full-gates/7.log |
| axiom-pins | `node scripts/check-axiom-pins.mjs` | pass / 13 | /workspace/solidity-lean/tests/sol-numeric-literals/evidence/recovered-full-gates/8.log |
| testsuite | `bash scripts/check-testsuite.sh` | pass / 0 | /workspace/solidity-lean/tests/sol-numeric-literals/evidence/recovered-full-gates/9.log |
| corpus | `bash scripts/check-corpus.sh` | pass / 2894 | /workspace/solidity-lean/tests/sol-numeric-literals/evidence/recovered-full-gates/10.log |
| automatic-strict | `node scripts/check-automatic.mjs --strict` | pass / 0 | /workspace/solidity-lean/tests/sol-numeric-literals/evidence/recovered-full-gates/11.log |

The read-only module-map check separately exits 1 and lists 42 missing rows.
All failures above are retained. run-lean stops before Lake/default targets;
the full library, examples, CLI and SolKey executable remain unvalidated. Corpus
and its existing TestSuite/network checks did pass under the same hard limits.
The automation gate checks classification, not cumulative timing.

The first full run also found an Audit literal-text lint finding and a missing
adjacent SolKey setup pin. The raw-string convention fixed the former without
changing metadata. The latter was recovered byte-for-byte from the published-base
pin after all 274 manifest entries were verified. The failed runs remain saved.
The failed MOCK harness first lacked its simulated lock fixture; its corrected
run passes. No real resource stop was induced by that test.

The runtime now captures its exact container ID before launch. The MOCK control
checks retaining exit 137, resource_stop=true, reserve evidence and unavailable
peak=null after simulated auto-removal; it performs no real Docker action. The
other added regression creates a unique real untracked input, requires that exact
path in the committed-input refusal, and cleans it in finally.

## Reviews, provenance and continuation

Independent finder and skeptic reviews were read-only and used no Lean server.
They accepted proof/fixture coverage and found F-ACCEPT-01 (ledger-only completion)
and F-ACCEPT-02 (checked dirty inputs versus sealed HEAD). Both are fixed with
live gates/registration and committed-input binding, and passing re-reviews are
source/checker stamped in evidence/final-reviews.json. The runtime auto-removal
reporting fix is independently reviewed and has an isolated regression control.

All 42 proof hashes match the successful kernel audit and touched/full-suite
source stamps. Later owned changes strengthen reporting/control checks and
record results; no Lean source changed after the validated implementation head.
The original 200000 heartbeat budget and 300-second MCP diagnostic timeout were
not increased. Earlier failed word-table attempts remain failures; 439 final
arbitrary-tail prefix proofs use 30 small structural modules and pass.

Coordinator integration must apply/register the concrete proposals:
registration.json, registration.patch, registration.module-map.patch. The worker
has not edited generated roots or module maps. Then rerun unchanged final gates
under the approved envelope and make a fresh current-head seal. The full-assignment
handoff obligation stays pending until those gates pass; this blocked checkpoint
has its own immutable packet. No push, merge, PR, scope change, new premise,
weakening or goal-state change occurred. No human scope question is pending.

Final runtime review also found F-RUNTIME-01: an exit-0 race after a reserve
breach. The wrapper now preserves the observed process exit separately and
forces effective exit 125 when a resource stop coincides with process exit 0.
The isolated MOCK tests cover both observed exits 137 and 0, with auto-removal;
no real pressure or stop is induced. This does not change any Lean source.


H35 follow-up: VM-owned build,627 exact #print axioms results and controls
pass. Cache shipping preflight fails on absent coordinator routing; the prepared
owned cache asset is not delivered. No new checkpoint is done. See
tests/sol-numeric-literals/h35/HANDOFF.md and evidence/h35-cache-receipt.json.


H41 supersedes the earlier H35 VM-shipping requirement. The verified pack
remains on this VM; its hash matches the coordinator-reported receipt. Delivery
is recorded as coordinator-pending. Never run ship-cache.sh on this VM. The
completion checker now validates the preserved pack and all 42 source mappings
instead of attempting VM delivery. Q-H35-SHIP1 is resolved; no transport choice
remains open. The coordinator receipt path is reported provenance, not a file
read on this VM. Original registration/full-runtime obligations remain open.
See evidence/h41-cache-handoff.json for the exact path, hash and receipt.


## Adoption of published master 8495f1de

The coordinator explicitly authorized adoption. Merge commit
221c2eaee71760bac888cb309645c2afaf90109b has parents the preserved owned head
7dc7de2d8581fd54766318fb20670511acd68ed6 and exact published master
8495f1deb0a95dd6b9301822d8649ab76b217681. A backup ref and byte-hashed copy
preserve the old head and both untracked evidence outputs. No reset occurred.
All 42 owned proofs and seven numeric input pins remain byte-identical. Original
base6f3eedf0 remains the proof/source baseline; adopted-master identity is separately
pinned. Inherited foreign work is accepted only when it exactly matches that
publication. Candidate paths union differences against both baselines, preventing
an upstream-added deletion or reversion to original-base bytes from disappearing.
Real Git object-tree controls exercise both failures without editing foreign files.
F-ADOPT-01 was found by both read-only reviewers and is fixed and re-reviewed.

The post-adoption owned build passes (matching-cache replay,49jobs). Per-file
MCP Audit passes and fresh actual #print axioms covers all808 theorem constants;
all991owned constants and axiom sets still match pins. No proof or budget changed.
The H41 verified pack remains valid, preserved and coordinator-pending; no VM
shipping was invoked and no cache freshness was inferred from the notice.

The unchanged full gate suite took72.553793seconds, maximum childRSS689316KiB,
with no resource stop. Build/trust/layers/docs/axiom pins/TestSuite/corpus/strict
automation pass. Root/orphan/run-lean fail because37owned imports remain pending.
Module-map check separately reports38missing rows, including Part00's row.
Published Part00–04 are reused; their source is not duplicated. Existing map rows
are preserved. Updated proposals are data only and pass temporary-index checks;
no shared root or map was edited after adoption. The protected published Source
and Core ExtCall areas remain exact adopted bytes.

The live assignment remains blocked on coordinator registration and final runtime
validation. The final packet records the containing commit separately, plus both
an original-base full patch and an owned delta against adopted master. Old sealed
packets and verified cache packs remain unchanged. Questions=[]; goal not reset.


Follow-on publication f77cf60d3cea8f7f1db8db29cc027532b0cd3fce adopted by merge d83602fb2b6fc9e94da52a3460b719a06f6e8648 preserving prehead7aabe84a and all 42 proof files/seven source pins. Both independent read-only reviews PASS. Fresh bounded owned build is matching-cache replay (49 jobs; 0.467876s, 59892 KiB max child RSS), controls PASS. Existing complete axiom/KeySort evidence is preserved; no theorem changed. Registration proposals remain 37 imports/38 rows; shared roots/maps untouched. Prior full gate failure remains outstanding; this follow-on does not claim a fresh full runtime pass or fresh cache pack. H41 archive/path/SHA and coordinator-pending handoff remain unchanged; no VM shipping. Original goal remains blocked, not reset.


Publication9584f9e7 adopted by merged9e1e7e preserving b225656c and every owned proof/source pin. Parts05/06 now identically integrated; remaining registration35 root imports/36 map rows. Finder/skeptic PASS. Fresh bounded owned matching-cache build PASS (0.519046s;61940KiB max child RSS), controls PASS; fresh register --check exit1 records missing imports. Complete prior axiom/KeySort evidence retained; no theorem changed. No fresh full-runtime pass/cache freshness claimed. H41 preserved pack/path/SHA unchanged, coordinator-pending, no VM shipping. Original goal unchanged and blocked on coordinator registration/final runtime.


Publishedb86ae456 adopted by merge3c9defec preservingd7cdfb47 and all42proof files/seven source pins. Parts07/08 identically integrated; proposals now33 root imports/34 map rows. Fresh bounded owned matching-cache build and controls PASS; register --check exit1 records missing roots. Finder/skeptic PASS. Prior complete axiom/KeySort evidence retained; no theorem changed. No fresh full-runtime pass/cache freshness claimed. H41 preserved pack/path/SHA unchanged, coordinator-pending; no VM shipping. Original goal unchanged and blocked on registration/final runtime.
