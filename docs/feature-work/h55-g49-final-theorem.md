# H55 G49/G50 work record and blocked handoff

Batch: `solidity-h55-sol-20261106`; task: `g49-final-theorem`.
Repository: `/workspace/solidity-lean`.
Branch: `codex/solidity-h55-sol-20261106/g49-final-theorem`.
Frozen base: `4d3790eadb8a5212233bc7d5e345817476b2f590`.
Final committed identity is exported in `/workspace/h55-g49-evidence/identity.json`.

The full assignment is unfinished. Historical source preservation, a checked
conditional G01 certificate-chain backfill, and scoped premise tooling are
reviewable. The actual G49/G50 public theorem, full premise census, inherited
controls/acceptance and V08 producer composition remain pending. No partial
checkpoint or prerequisite pass is represented as full completion.

## Recovered setup and exact historical source port

The VM initially had clean `work` at
`8bf8321873befa3f35ca31e97e5339a1baee93e6`. The old branch was preserved.
A fetch recovered the exact base; remote `origin/master` equals that base and
its ancestry check passes. The assigned branch was created there under the
repository writer lock. Direct fetch of staging initially failed with
`upload-pack: not our ref`; the raw object remains unadvertised upstream.
This initial failure is retained in evidence, not treated as the current
staging-source blocker.

The coordinator resolved staging recovery with the exact historical eight-file
archive `/workspace/h55-staging-e59348224.tar`, SHA256
`1164b3de72c26e28c8b78843e151ff23e17ba8046a18de5e4682d472afcee60a`.
The archive/member set, regular-file paths and every supplied file hash were
verified before extraction into `/workspace/h55-staging-e59348224`, outside Git.
`tests/h55/g49-final-theorem/staging-manifest.json` commits the original hashes
and provenance; it is not the bulk payload.

Only the leased consumer, controls, audit script and additive documentation were
ported. Consumer and controls match the historical bytes exactly. The script's
only adaptation accepts the external payload as fourth positional argument and
checks its exact committed hash. All original revision, dependent statement,
producer-body, guard/observation, dependency/axiom, 24-control, 19-corruption and
2290-open-obligation checks remain unchanged. Newer master content is retained.
LoopControls and supplied shared registration changes are for central integration.

Bulk `parallel-premises.json` is OFF GIT. Regeneration command:

```sh
python3 -B scripts/h55/g49-final-theorem/premise-tools.py regenerate --archive /workspace/h55-staging-e59348224.tar --output /workspace/h55-g49-evidence/parallel-premises.json
```

It verifies the archive and all eight original files before emitting the exact
payload. Result SHA256:
`bbeb698364f92833b4b38f03299fe5286cefd32bf12a973aedf72f1282ee3b37`.
The tool refuses bulk output anywhere inside this repository or replacement of
different evidence. The audit is invoked with metadata, accounting report, result
path, then this payload path. No historical current-proof pass is claimed.

## Remaining staging and producer prerequisites

The recovered historical files depend on four absent master files:

- Solidity/Roadmap/V16/CompilerConsumer.lean
- tests/roadmap-v16/CoreConsumerControls.lean
- tests/roadmap-v16/MixedMemoryControls.lean
- scripts/roadmap-v16-heap-audit.py

Their prerequisite closure has not been supplied; no replacement fixture or
producer proof has been invented. The original strict audit also pins older
`Solidity/Evm/Compiler.lean` and `Solidity/Semantics/RunFrame.lean` hashes, both
different on current master. Those newer files have not been overwritten and
historical pins have not been relaxed. Exact missing imports and both old/new
hashes are in `staging-prerequisites.json` outside Git. Audit execution exits 1
on its missing heap-audit import before reading nonexistent metadata/report
inputs; the remaining historical gates are still pending.

ESCALATE — prerequisite publication and producer compatibility remain unresolved.
Recovery routes are (1) coordinator delivery of the original prerequisite source
closure with actual owners performing any needed current-master integration, or
(2) owner-reviewed additive adapters preserving every existing contract/control,
followed by a fresh complete compatibility audit. Neither route authorizes a
weaker premise, changed observation, altered historical pin or excluded feature.
These are coordinator artifact/interface dependencies, not a human scope request.

V08 agreement composition remains gated on the specifically requested published
migration. No verified delivery of it is identified. P1/P8a/P8b/P10 are not
fabricated. Inspected shape gaps: P8b's frozen producer type extends the full G01
Lowering but the declaration alone supplies no inhabitant; P10's local decoder,
charged-step and continuation API is not the full G01 Execution/assembler/load
certificate. This is a bounded interface inspection, not an exhaustive producer
fit audit. The complete fit report remains pending.

## Checked frozen-interface composition backfill

[PassChain](../../Solidity/Roadmap/G49Final/PassChain.lean) proves `pass_chain`
from the unchanged full G01 Lowering, Compilation and Execution packages and an
exact equation identifying the assembled artifact with the table read by source
meaning. It composes both directions at the actual lowered world, using each
certificate's need/back fields; all admissibility, Forward/Guard and environment
maps remain. It adds no closure restriction on source admission or producer
pass domains. The theorem has only `propext` in its observed axiom set.

This is conditional refinement for supplied complete certificates, not a
concrete Source/P8a/P8b/P1/P10/V08 producer, PublicCorrectness, deployment or
reachable adversarial-session proof. In particular coverage, approved readings,
non-vacuity, source-determined hashes, creation table consistency, reached-world
decoding and resumed-session commutation have not been proved by this helper.
All five G49.01–.03/G50.01–.02 obligations remain unfinished.

The source-only bounded helper rebuilds all five affected modules in an isolated
external cache, then checks a test-only Lean inventory of the actual kernel
declaration. No old `.lake` olean is consumed. Lean tooling is imported only by
the external inventory test, not the core.

```sh
python3 -B scripts/h55/g49-final-theorem/check-pass-chain.py --lean /workspace/.setup/tools/lean-4.24.0-linux/bin/lean --evidence /workspace/h55-g49-evidence/pass-chain-reviewed
```

That evidence directory already exists and is immutable; a rerun must use a NEW
directory. Recorded outcome: `PASS_CHAIN_SOURCE_AND_INVENTORY_CHECK_PASS`.
Full per-module commands, source hashes, results and logs are in that directory.
This direct affected-module check does not replace repository final acceptance.

## Mechanical count and current owners

The coordinator's post-transfer ownership file supersedes the frozen prompt's
pre-transfer snapshot. Its SHA256 is
`f4baf22b3eac583398a90c021d91600c2c7074f7ff8e3b6ee328a373fefe5b73`.
The raw 263 KiB file remains outside Git at `/workspace/h55-ownership-after.json`;
its identity is committed in the staging manifest.

The checked backfill has 14 top-level binders: four open producer premises,
three caller proof conditions and seven quantified parameters. Every one is
inventoried from Lean with its full dependent type. Types, readable types,
constants, complete statement, dependency list, source and axiom set are pinned.
No Type-valued certificate is hidden by counting only propositions.

| Binding | Role | Ownership obligation | Current owner |
| --- | --- | --- | --- |
| lowering | supplied full producer | P8b | V16 |
| backend | supplied full producer | G49.01 | this H55 lane |
| execution | supplied full producer | G49.02 | this H55 lane |
| artifact | exact artifact agreement | G49.02 | this H55 lane |
| w | caller well-formedness proof | P8a | CR |
| p | caller profile proof | P8a | CR |
| allowed | caller allowed-environment proof | G50.02 | this H55 lane |

Caller-condition owners denote integration responsibility, not a claim of a
missing producer for every particular environment/proof. Parameters are S, I,
Asm, V, r, art and e. Supplied package fields are NOT recursively atomized or
discharged. Thus four is the scoped top-level producer count, not the final
pipeline's open-obligation total. The final public-theorem count is UNKNOWN.
No premise has been certified closed by metadata.

```sh
python3 -B scripts/h55/g49-final-theorem/premise-tools.py count --inventory-log /workspace/h55-g49-evidence/pass-chain-reviewed/premise-inventory.log --ownership /workspace/h55-ownership-after.json --output /workspace/h55-g49-evidence/pass-chain-reviewed-owners.json
python3 -B tests/h55/g49-final-theorem/test_premise_tools.py
```

Both pass. Seven test methods include 19 accounting corruptions plus archive,
output/no-clobber, ambiguous inventory and immutable-evidence controls. These
are metadata tests, not compiler/runtime proof or the historical 19-corruption
suite. The test harness currently consumes explicitly named retained VM inputs;
it is not a standalone producer/full-scope acceptance test.

## Gates, resources, reviews and registration

Lean: 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`.
Lake: 5.0.0-src+797c613 (Lean 4.24.0). Versions are recorded in `versions.txt`.
The bounded KeySort prerequisite passed with exit 0 and `KEYSORT_PASS`:

```sh
LEAN_NUM_THREADS=1 /workspace/.setup/tools/lean-4.24.0-linux/bin/lean -j1 --tstack=131072 Solidity/KeySort.lean
```

All Lean checks were serial, explicit `-j1`, one heavy job at a time, under the
writer lock, with an 8 GiB address-space cap, no swap, and a monitored 4 GiB free
reserve. KeySort had a 60-second bound; each backfill module/inventory had a
300-second bound. No proof heartbeat, resource cap or swap limit was increased;
no systemd-run was used. Minimum available memory in the reviewed run was
17,771,978,752 bytes. Matched five-module source checks took 11.553 then
11.561 seconds (+0.069%); the theorem itself took 0.403 seconds in both.
Sources/toolchain/bounds matched. No core representation refactor occurred.
Speed history was inspected before work; no speed-motivated change was undone.

Per-file Lean MCP tools and get_goal are not exposed in this session; the
source-only Lean fallback and launcher goal context were used. No second goal
was created or original goal reset. One initial creation of the new Python gate
helper was inadvertently not wrapped in the writer lock; no concurrent writer
was observed. Subsequent repository edits and every Lean check used the lock.
This procedural lapse is retained rather than claiming perfect lock compliance.

| Gate | Outcome | Evidence |
| --- | --- | --- |
| Exact base/remote ancestry | pass | recovery.json |
| Archive and all eight original file hashes | pass | staging-verified.json |
| Versions and bounded KeySort | pass | versions.txt, keysort-result.json |
| Backfill source closure and actual typed inventory | pass | pass-chain-reviewed/results.json and run-status.json |
| Payload regeneration, owner count and seven corruption-test methods | pass | parallel-premises.json, pass-chain-reviewed-owners.json, premise-tool-tests-reviewed.log |
| `./run-lean.sh` | fail 1 | run-lean.log: layers pass (859 modules); stale shared root registration stops before Lean |
| Historical strict parallel audit | fail 1 | staging-audit.log: missing heap-audit module |
| Documentation paths | initial fail 1, corrected staged rerun pass | doc-paths-corrected.log: every reference resolves; 115 ambiguities retained |
| Full affected consumer/control/import closure and full-scope Terra acceptance | pending | missing prerequisites and unfinished full theorem |

No `RUNTIME_GATE_PASS`, full build pass, historical audit pass, full-scope Terra
acceptance or completed goal is claimed. No two failed acceptance attempts were
made; acceptance is pending rather than relabeled from a narrower review.

Independent finder and skeptic source-preservation reviews found no port defect.
The theorem review found no semantic defect. The skeptic identified unpinned
readable binder types and stale evidence-directory reuse; both were fixed and
independently reinspected. The finder identified the obsolete initial blocked
handoff; it was replaced by this record. Reviewers used no Lean/server/builds,
tests or writes. Detailed review outcomes are in `reviews.json`; final full
public-theorem reviews remain pending.

Shared roots/maps/pins were not edited. Central registration fragments:

```lean
import Solidity.Roadmap.G49Final.PassChain
import Solidity.Roadmap.V16.CalculusConsumer
```

Suggested roadmap map rows for central integration:

| Module under Solidity | Description |
| --- | --- |
| Roadmap/G49Final/PassChain.lean | Conditional complete G01 certificate-chain refinement; concrete producers/public theorem pending. |
| Roadmap/V16/CalculusConsumer.lean | Historical six calculus/compiler consumers, original explicit premises and payment/callback/exhaustion boundaries. |

Core stays intrinsically typed and dependency-free. No H16 Source/Core ExtCall,
shared registration/pins, theorem/premise/exclusion/refusal/observation weakening,
axiom/sorry shortcut or H58 HOLD item was introduced. No push, merge, PR,
ship-cache.sh or cache transfer occurred.

## Export and remaining full scope

Evidence directory: `/workspace/h55-g49-evidence`.
Original committed patch: `/workspace/h55-g49-evidence/original.patch`.
Bundle: `/workspace/h55-g49-evidence/source.bundle`.
Handoff copy: `/workspace/h55-g49-evidence/handoff.md`.
Checksum manifest: `/workspace/h55-g49-evidence/SHA256SUMS`.
Identity/base/full head/source hashes: `/workspace/h55-g49-evidence/identity.json`.
These final exports are generated after the reviewed commits.

Validated scoped cache pack: `/workspace/h55-g49-evidence/pass-chain-cache.tar.gz`.
SHA256: `8019ff5e1815dbc1178b4fbc97eba5f2684e34634a363692c2e7ecd112809260`.
It contains only the five checked backfill modules and their source-build/version
records; it is NOT a full combined-project or final public-theorem cache pack.

Resume the original whole queue after prerequisite/owner publication. Complete
the actual staged consumer/control closure, unchanged historical gates and
current-producer compatibility; wait for published V08 migration before those
premises are composed; implement the real full G49/G50 public theorem with every
unproved component named and typed; census every final premise with current
owners and producer-fit gaps; run all frozen scope/observation/resource/progress,
deployment/adversarial transaction, controls, affected-module and acceptance
gates; finish independent full-scope reviews and export the final validated cache.
The existing goal remains unfinished, with the above dependencies recorded.
