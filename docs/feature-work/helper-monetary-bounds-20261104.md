# H26 HELP-MONEY packet: exact monetary bounds

Status: coordinator-pending. Implementation, on-VM kernel acceptance and reviews are complete; the coordinator reports the cache received and SHA256 verified. Shared registration is now complete on the worker branch under the 2026-11-07 coordinator authorization. Full combined validation remains pending the merge pre-gate; no worker scope decision remains. This is not H16/H19/P15/G35.03 completion. No RUNTIME_GATE_PASS claim.

Repository: `/workspace/solidity-lean`. Branch: `codex/solidity-helpers-20261104/monetary-bounds`. Pinned helper base: `6f3eedf0788ee1f8a3bcf230558c712ecdca04d5`. Exact immutable owner input: `046292ee61fc6967311bbb1ddec44505ed698481`, checked in detached `/workspace/monetary-producer-input`. Owner input ancestry is separate from helper commits; no producer commit is included in the helper branch. Final helper head and artifact hashes are recorded in the delivery handoff after committing, avoiding a self-referential commit hash.

## Transport and producer inventory

Sealed input `/workspace/peer-inputs/h26/monetary-046292ee.bundle`: 341632 bytes; SHA256 `3e80a54e099845314bfd0b494132947eb312e1e683046eabf7dca0431099b64b`. Companion SHA256SUMS verification passed. `git bundle verify` passed; exact input ref and required pinned base verified. At initial setup, published origin/master was fetched and equaled the pinned base; subsequent publications did not include this monetary packet. Q1 (missing manifest during delivery) resolved when the companion arrived; no alternate model was created.

`Balance := Nat`; `Word := Fin (2^256)`; `Fits b := b < wordLimit`. `credit?` guards `b + v.val < wordLimit`; `debit?` guards affordability `v.val ≤ b` and returns exact subtraction; `checkedWord` constructs an intrinsic Word only with Fits. Producer modules remain byte-for-byte unchanged; their SHA256s and helper content hashes are in evidence/input-binding.json.

All producer theorems inventoried (no requested general helper theorem already exists):

| Module | Existing theorems |
|---|---|
| Monetary | ofWord_fits, wordView_exact, fromWords_fit, wide_exact, wide_not_fits, wide_checked_rejected, wide_word_projection, wide_debit, credit_overflow_refused |
| MonetaryLaws | credit_success_fits, debit_success_fits, wide_zero_debit, debit_success_without_range |

The limit and overflow controls deliberately recheck existing `wide_*`/overflow facts at the explicit boundary. They are acceptance controls, not claimed novel laws.

## Exact interface and backfill

All helper declarations use the producer namespace `Solidity.Source.Monetary`. Explicit signatures in Laws.lean:

```lean
credit_debit_roundtrip (b : Balance) (v : Word) (c : Balance)
  (h : credit? b v = some c) : debit? c v = some b
debit_credit_roundtrip (b : Balance) (v : Word) (d : Balance)
  (hb : Fits b) (h : debit? b v = some d) : credit? d v = some b
checkedWord_iff (b : Balance) (w : Word) :
  checkedWord b = some w ↔ Fits b ∧ w.val = b
```

These quantify over arbitrary exact Nat balances and all intrinsic Words, not just fixtures. Backfill completed: debit_eq_some_iff, credit_eq_some_iff and reverse_roundtrip_iff give exact algebraic characterizations, including necessity of Fits for the reverse round trip. No changed definitions, weakened premises or exclusions. No untyped entities, ledger change, authority/session implementation, reachability claim, Source edit, H22 change, or H21 tooling change. Gate G0 was read before using existing intrinsic Word; representation is unchanged.

## Kernel acceptance matrix

Command K: in the exact producer worktree, under the Docker envelope below, `lake -f /workspace/solidity-lean/tests/helpers-20261104/monetary-bounds/lakefile.toml build Solidity.Lowering.P8.HelperPackets.MonetaryBounds.AxiomPins`. This imports Controls, Laws and both producer monetary modules. K passes. Every row below is kernel checked and has an exact transitive axiom pin. Machine-readable rows: evidence/acceptance.json.

| Module | Theorem/control | Kernel command/result |
|---|---|---|
| Laws | credit_debit_roundtrip | K: pass |
| Laws | debit_credit_roundtrip | K: pass |
| Laws | checkedWord_iff | K: pass |
| Laws | debit_eq_some_iff | K: pass |
| Laws | credit_eq_some_iff | K: pass |
| Laws | reverse_roundtrip_iff | K: pass |
| Controls | boundary_zero_fits | K: pass |
| Controls | boundary_zero_checked | K: pass |
| Controls | boundary_zero_debit_zero | K: pass |
| Controls | boundary_zero_credit_zero | K: pass |
| Controls | boundary_zero_view | K: pass |
| Controls | boundary_max_fits | K: pass |
| Controls | boundary_max_checked | K: pass |
| Controls | boundary_max_debit_zero | K: pass |
| Controls | boundary_max_credit_zero | K: pass |
| Controls | boundary_max_view | K: pass |
| Controls | boundary_limit_fits | K: pass |
| Controls | boundary_limit_checked | K: pass |
| Controls | boundary_limit_debit_zero | K: pass |
| Controls | boundary_limit_credit_zero | K: pass |
| Controls | boundary_limit_view | K: pass |
| Controls | boundary_above_fits | K: pass |
| Controls | boundary_above_checked | K: pass |
| Controls | boundary_above_debit_zero | K: pass |
| Controls | boundary_above_credit_zero | K: pass |
| Controls | boundary_above_view | K: pass |
| Controls | zero_unaffordable | K: pass |
| Controls | max_affordable | K: pass |
| Controls | limit_affordable | K: pass |
| Controls | above_affordable | K: pass |
| Controls | zero_credit_max | K: pass |
| Controls | max_credit_refused | K: pass |
| Controls | limit_credit_refused | K: pass |
| Controls | above_credit_refused | K: pass |
| Controls | max_forward_roundtrip | K: pass |
| Controls | max_reverse_roundtrip | K: pass |
| Controls | reverse_without_fits_counterexample | K: pass |
| Controls | above_reverse_counterexample | K: pass |
| Controls | checked_rejects_wrong_word | K: pass |
| Controls | max_unaffordable | K: pass |

AxiomPins imports Controls and pins all 40 declarations with `#guard_msgs`. Five general laws and the two controls max_forward_roundtrip/max_reverse_roundtrip use only `propext`; checkedWord_iff and the other 32 controls have no axioms. Totals: 7 propext-only, 33 axiom-free. No new axioms, sorry/admit, unsafe/opaque proof escape or proof-budget overrides. No maxHeartbeats changes. Kernel controls cover Fits, checkedWord, debit?, credit? and wordView at 0, 2^256−1, 2^256, 2^256+1; affordability/refusal transitions; wrong result Word; both nonzero round trips; actual successful wide debit followed by refused reverse credit. Wide balances make unaffordability impossible for a Word amount; tests do not invent such a case. There are no Solidity compiler controls or EVM execution claims in this primitive proof packet.

## Historical runtime and gate evidence (before 2026-11-07 registration)

Lean 4.24.0 commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b; Lake 5.0.0-src+797c613. Docker ubuntu:24.04, coordinator-pinned digest sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852. Hard flags: `--memory=12g --memory-swap=12g --cpus=1 --user=1000:1000`; actual memory.max 12884901888 and memory.swap.max 0 asserted before each gate. `LEAN_NUM_THREADS=1` set after activate.sh; packet-local alternate Lake TOML adds explicit `-j1` to all library and executable arguments. Writer lock `/tmp/solidity-lean-feature-groups-20261025/writer.lock`; serial execution. run-gates.py checks the minimum of MemAvailable and outer cgroup memory.max minus memory.current every 250ms, stopping its own container below 4 GiB. No reserve stops occurred. Historical logs used host-visible MemAvailable; the corrected effective guard and final packet/KeySort reruns are in resource-final.json and serial-final.json. Initial executable-root compilation omitted explicit -j1; the corrected-config verbose run fetched the root artifact, so it does not prove a fresh root compilation. The additional explicit per-file KeySort root check in keysort-root-final.json records `lake env lean --tstack=131072 -j1 --setup .lake/build/ir/SolkeyCheck.setup.json SolkeyCheck.lean` and the executable result. No systemd attempts. No other workers were terminated.

Consolidated final commands, outcomes and output paths: evidence/final-gates.json. Historical commands, exit codes and memory measurements: evidence/gates.json plus runtime-final.json, resource-final.json, serial-final.json, keysort-root-final.json and mcp.json. Initial recoverable environment failures are retained: Lake does not accept `lake build -j1`; explicit `-j1` belongs to Lean arguments. Initial direct `lake env lean` missed an artifact-cache Keccak import; building the target resolved it. Initial Docker PATH lacked Node; the corrected runner uses the installed runtime under /opt. Initial wrapper version handling was corrected; final runtime evidence supersedes that failed attempt. These failures are not passing gates.

| Gate | Actual result |
|---|---|
| Exact packet K and all 40 pinned statements | Pass, evidence/packet.log and axioms-pinned.log |
| Per-file MCP diagnostics | Pass: Laws, Controls and AxiomPins each report `diag: 0 errors` |
| KeySort | Pass: parsed 377 taclets, 131 read-bearing, table covers 131; OK annotations match configured SolKey rules, evidence/keysort-final.log |
| Trust | Pass: 3697 sources, 285 inventoried implementation/recovery sites, 0 findings |
| Layers | Pass: 559 core modules, 0 reach elaborator or checked parser adapters |
| Documentation paths | Pass |
| run-lean.sh | Fails at stale generated roots before full Lean build |
| register.sh --check | Fails: three new helper imports missing from Solidity.lean |
| check-orphans.mjs | Fails: the same 3 helper modules are unregistered |
| Central axiom inventory | Fails: 0 axiom errors, 64 unrecorded changes (40 helper + 24 owner-input pins) |

No independent final-master gate claim: master does not contain the exact producer Source interface. Full library/default-target/importing-consumer final confirmation and remaining full gate suite remain pending behind shared registration. Packet-local importing consumers Controls and AxiomPins pass; no existing owner consumer is changed. Central registration and inventory remain immutable per scope.

## Separate reviews

Implementation milestone: separate read-only finder and skeptic agents inspected all 6 laws and 34 controls against the immutable producer, without Lean/server execution or writes. Both found no correctness, premise or scope defects; both requested that duplicated boundary facts be labeled acceptance controls (done above). Their verdicts are saved in evidence/finder-implementation.md and skeptic-implementation.md. Final separate finder and skeptic reviews are saved in evidence/finder-final.md and skeptic-final.md. They caught and confirmed correction of the axiom summary, historical log binding, executable serial flags, effective cgroup headroom guard, and cached-root wording. Both accept a blocked handoff; neither certifies the failed global gates. Delivery artifacts are mechanically sealed after committing.

## Queue and integration handoff

1. Producer transport, signatures, exhaustive existing-law inventory: done.
2. Three assigned arbitrary-input proofs: done.
3. Positive/negative kernel boundary controls and actual counterexamples: done.
4. Acceptance matrix and standard axiom pins: done; separate final reviews done with findings fixed; global gates pending coordinator merge, not complete.
Backfill: the three same-namespace algebraic laws and 34 boundary controls are complete; no other backfill or H25 work authorized.

VY5 integration: cherry-pick helper-only commits onto the owner's existing input ancestry (do not cherry-pick the producer bundle into master as part of this packet). Register Laws, Controls and AxiomPins in the generated root and the appropriate module-map area, and record the 40 helper pins in the central inventory; reconcile 24 owner-input inventory additions separately. Then run checkpoint/full gates, required consumers and ./run-lean.sh with serial Lean, hard resource bounds and the configured SolKey checkout. The packet-local config and wrapper exist only to validate this immutable input without changing shared build files.

Q2 initially resolved by coordinator: "Per H21(2)/H35: do not edit shared roots; record full validation as pending coordinator merge, and continue." This historical registration deferral was superseded on 2026-11-07 by explicit authorization to register on the worker branch using register.sh and fragments.sh. Full combined validation still belongs to the merge pre-gate. Historical failed outputs remain evidence of the earlier pre-integration state, not passing checks.

The final delivery directory (ignored to avoid recursive patch/bundle commits) contains original.patch, helper.bundle, handoff.md, result.json and SHA256SUMS, with exact final committed head/base and absolute paths. The committed changes contain only the three exclusive scopes. No push, merge or PR was performed. get_goal is unavailable in the exposed tool catalog; the existing goal was neither created nor reset.

## H35 on-VM revalidation and cache transport

Fresh H35 validation is in tests/helpers-20261104/monetary-bounds/evidence/h35/gates.json and h35-packet.log. The exact producer worktree built AxiomPins (importing all owned modules), then explicitly checked Laws, Controls and AxiomPins with Lean --tstack=131072 -j1 and Lake setup metadata. All pass under the established hard 12 GiB/no-swap Docker envelope and effective 4 GiB reserve guard. No proof or producer source changed. This checks all 6 laws, 34 controls and 40 standard axiom pins on this VM.

Historical pre-H41 transport evidence: H35 cache shipping was attempted with scripts/coord-tools/ship-cache.sh. Its default master guard rejects the immutable producer worktree. The supported SHIP_ALLOW_HEAD=1 dry run then prepared 48 artifacts (~0.19 GB) and 20 mappings with no unresolved traces, but failed at the missing coordinator poll-state.json. The worker also lacks ~/.local/share/cloudvm-coord/vmexec.py. No destination or credentials were invented; no transfer or successful remote receipt is claimed. The honest blocked receipt is evidence/h35/cache-receipt.json, with both actual command logs. A SHA256-bound local cache archive and artifact/input manifests are prepared under delivery/h35-cache for coordinator retrieval.

Q3 resolved by H41: the coordinator pulled the prepared pack and reports its SHA256 verified against the reported value. The coordinator receipt is `/home/guilherme/.local/state/cloudvm-coord/receipts/monetary-bounds-cache-received-20261105T020646Z.json`. This is a coordinator-side receipt path supplied in the conversation; the receipt file has not been read from this VM. The historical blocked worker shipping receipt is retained unchanged and superseded by evidence/h41/coordinator-receipt.json. No further worker shipping attempt will be made.

Separate H35 finder/skeptic read-only reviews both pass for blocked handoff (evidence/h35/finder-review.md and skeptic-review.md), without Lean/server use. All 48 archived artifact checksums and all three owned-module cache mappings were independently verified locally; this is not a remote delivery receipt.

## H41 current delivery state

H41 amends H35: "Leave verified packs on the VM and record the path and sha; the coordinator pulls them; never run ship-cache.sh on a VM. Mark delivery coordinator-pending and continue." The verified pack remains at `/workspace/solidity-lean/tests/helpers-20261104/monetary-bounds/delivery/h35-cache/artifacts.tar.zst`, SHA256 `135c2b69cd73f22d4acd3febe835aa65ed469863ccaa6159d0faa0a4e63ffcb1`. Its local hash was rechecked after the coordinator receipt. The coordinator reports receipt and matching SHA; no remote full validation is inferred from cache receipt.

Current status is coordinator-pending, with questions=[]: Q2 and Q3 are closed. Proofs, controls, axiom pins, backfill and separate reviews retain their passing on-VM evidence. The cache-retrieval obligation is satisfied by the coordinator-reported receipt. Shared registration and full combined validation remain pending coordinator merge. No full-assignment or whole-feature completion claim. This update changes documentation/evidence only, so Lean checks are not repeated; documentation paths and checksum-bound delivery artifacts are checked.

Separate H41 read-only finder/skeptic reviews pass without findings (evidence/h41/finder-review.md and skeptic-review.md); neither used Lean/server or wrote files.

## 2026-11-07: authorized shared registration on adopted master

Coordinator instruction: VY5 frozen under H118, monetary work published at e8247d927/a0cdc0bec; perform shared registration on this branch with register.sh and fragments.sh; merge pre-gate supplies combined validation. Adopted master `65e69b6426a9a4fc3fb5541f41726a4bfefda5d0` in merge `33a9ea1619101d11301cc3a840a27fcde2984304`, preserving original helper commits. Both frozen monetary Source modules are byte-identical to exact owner input046292ee; no Source or helper proof was edited.

Generated registration adds exactly three root imports, three rows through docs/module-map/v08-adapters.d/monetary-bounds.md, and the existing 40 exact axiom pins through scripts/g07-axiom-pins.d/Solidity/Lowering/P8/HelperPackets/MonetaryBounds/AxiomPins.json. Ran register.sh and fragments.sh; no hand edits to combined generated files. There are no changes to pre-existing pin entries.

Fresh targeted owned build and all three explicit per-file checks pass against adopted master in the existing serial Docker envelope (actual12GiB memory.max, swap0, effective4GiB reserve guard). Lean4.24.0/Lake5.0.0; unchanged proof budgets. Source/helper content binding, commands and outputs are under tests/helpers-20261104/monetary-bounds/registration-20261107/evidence. Root, fragments, module-map, trust, layers, orphan and doc-path checks pass. The first per-file attempt hit fetched Evm artifact lookup failure; preserved per-file-cache-failure.log is superseded by the passing --setup-aware per-file-final.json, without changing a proof.

Global inventory check still returns failure: 0 axiom errors and 492 unrecorded entries. axiom-delta.json verifies all40 helper pins match their fragment exactly, while all492 outstanding changes already occur in the adopted master outside this helper; no unrelated baseline or policy was changed. Combined validation and reconciliation remain with the coordinator merge pre-gate. No fresh full-core/Bridge pass or RUNTIME_GATE_PASS is claimed.

Separate finder/skeptic registration reviews verify exact imports/rows/pins, unchanged frozen producer/helper hashes and passing targeted/resource evidence. Their verdicts are saved with this checkpoint. H41 remains in force: original verified pack retained for coordinator pull; no VM shipping script invoked.

## Consolidated constructor member — 2026-11-07

The formerly missing constructor final publication is now fetched, authenticated and merged: retired0d92f861, manifest-only publication a0c09d3, merge3df80159. Exact original prompt/scope bytes and acknowledged paused status verified before member work. The bundle manifest entry matches expected58bdca13… exactly; raw historical bundle bytes remain unavailable and are not recreated or claimed verified.

Both packets are registered on this branch: seven public helper imports/map rows,40 monetary plus28 constructor pin entries, generated by register.sh/fragments.sh from lane fragments. Monetary proof code remains unchanged and its current-master checks pass. Constructor Source/Target compile after one proof-witness arity fix; all16 corresponding axiom sets match original guards. Constructor Producer/Controls and12 remaining proofs remain pending CTOR-NAT-1 because the original relation projects balance.val from the now-Nat source balance. Relation body unchanged pending the H82 definition decision. All independent compiler/static registration checks have run; full merge pre-gate and unrelated adopted-master492 inventory entries remain coordinator work. No whole-chain completion claim.

## CTOR-NAT-1 resolved by H57 — 2026-11-07

The coordinator-approved migration is implemented and reviewed. The original Word relation/statements are frozen verbatim as provenance; a live explicit Word-view V1 and exact Nat relation have bidirectional bridges with an exact-match or Fits premise. All five dependent statements explicitly use Nat without other premise/output changes. Actual fixture bounds and a wide+5 counterexample cover the overlap boundary. All41 constructor proofs/guards now pass alongside the retained40 monetary checks;81 exact pins and ten public helper modules are registered. Earlier pending-owner-decision paragraphs and consolidation snapshots are historical, superseded by constructor-transport/nat-migration-20261107/migration-status.json. Questions are closed. Full combined validation and unrelated adopted-master492 inventory changes remain coordinator merge pre-gate work. No frozen Source edit or whole-feature completion claim.
