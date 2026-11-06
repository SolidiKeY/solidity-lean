# H55 historical source-port checkpoint

Batch: solidity-h55-sol-20261106; task: g49-final-theorem.
Repository: /workspace/solidity-lean.
Branch: codex/solidity-h55-sol-20261106/g49-final-theorem.
Base: 4d3790eadb8a5212233bc7d5e345817476b2f590.

The full assignment remains unfinished. This commit preserves the historical
source port; separate backfill commits follow on the same assigned branch.
No full theorem, affected consumer proof pass or acceptance is claimed.

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


## Checkpoint validation and handoff

Archive/member hashes and exact historical consumer/control bytes pass.
The external payload regenerates to its committed SHA256. Independent read-only
finder and skeptic source-preservation reviews found no defect; neither ran
Lean/server/builds/tests or wrote files. The historical audit fails on the absent
heap-audit prerequisite; the full repository gate stops at central-only root
registration. Newer master producers and all historical strict checks are kept.
Detailed evidence: /workspace/h55-g49-evidence.
The entire original queue and V08/public-theorem/acceptance obligations remain
unfinished. Source-only review is not a proof pass. No push or merge.

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


The fresh serial isolated five-module closure and actual Lean inventory pass.
The theorem uses only propext; independent finder/skeptic semantic reviews found
no defect. This remains a generic conditional backfill with supplied full
certificates, not delivery of the original full public theorem. Current gate
commands, hashes and logs: /workspace/h55-g49-evidence/pass-chain-reviewed.
Scoped cache pack: /workspace/h55-g49-evidence/pass-chain-cache.tar.gz, SHA256
8019ff5e1815dbc1178b4fbc97eba5f2684e34634a363692c2e7ecd112809260.
Full public and acceptance gates remain pending as above.
