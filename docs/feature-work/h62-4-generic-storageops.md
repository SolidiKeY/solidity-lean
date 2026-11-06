# H62 item 4: generic StorageOps controls

Status: **blocked, full assignment unfinished**. This checkpoint delivers a
reviewed textual census and deterministic reproduction backfill. It does not
claim a generic StorageOps proof, semantic correspondence, migration, runtime
gate, or acceptable before/after checking-cost delta.

Branch: `codex/solidity-h62-4-20261106/generic-storageops`.
Exact frozen base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Repository: `/workspace/solidity-lean`. The initial clean `work` branch pointed
to `6cf853aea`; fetching origin/master supplied the missing base. Its ancestry
was verified with `git merge-base --is-ancestor BASE origin/master` before
creating the assigned branch. No old checkout changes were discarded.

## Scope and census

The only repository additions are in the two assigned test/script directories
and this document. All 230 original Backend/StorageOps modules remain byte-for-byte
identical to the base. There are 6,036 explicit declarations across those files.
The 84 `*Controls` files contain 1,623 theorem declarations: 1,007 public and
616 private. These are **candidate cases including proof helpers**, not 1,623
independent semantic cases. No declaration has been silently excluded.

The full original declaration inventory includes each source path, line,
qualified source name, visibility, kind, exact source header, ambient binders,
contextual statement SHA256 and declaration SHA256. These are source pins,
not kernel-elaborated type hashes. File SHA256 pins also preserve definitions,
imports, options, observations, proofs and comments. A conservative namespace,
section and mutual-block scanner masks nested comments and strings. Six scanner
regressions include binder changes, mutual scope, proof-only drift and malformed
input. Current-corpus independent sweeps found no missed declaration starts.

Full inventory (about 4.73 MiB) stays off git under H44:
`/workspace/h62-generic-storageops/evidence/inventory.json`.
SHA256: `fd5361469fe3e59603d8e1612e5abb306c586ad1a2f97a2576ab7c178179f336`.
The compact [manifest](../../tests/h62/item4/generic-storageops/inventory-manifest.json)
pins all 230 files, totals and full inventory digest. Regenerate with:

```sh
python3 -B scripts/h62/item4/generic-storageops/census.py \
  --output /workspace/h62-generic-storageops/evidence/inventory.json
python3 -B scripts/h62/item4/generic-storageops/accept.py
```

Acceptance independently compares the current file set and each file's bytes to
`git ls-tree` and `git show` at the frozen base. It fails on source or inventory
drift; `--write` only regenerates the manifest and never authorizes changing the
base or passing changed original statements.

## Audit 9/11/16 disposition

The coordinator's verified audit has SHA256
`31ab16906906a9b22fd28700aacc72d2ee0ffe81cea723ae209eb28e5299286a`.

| Item | StorageOps application and remaining obligation |
| --- | --- |
| 9, parameterize twin controls | Applicable method: preserve intrinsic element/path/operation types and all observations while sharing a law. The named Passes/PrimitivePackets/InternalFlow/MemoryCopies examples are other families. No ownership is claimed over them. This census retains every StorageOps control; semantic grouping and exact-instance migration remain pending. |
| 11, shared lemmas and fixtures | Applicable method: e.g. repeated private names `graph` (48), `hash` (48), `locations` (46), `ix` (43), `one` (40), `zero` (39), `run` (36). Name repetition is a search lead, not proof of equivalent definitions. No helper extraction or shared HeapRepr/AllocatorRepr replacement is claimed. |
| 16, table plus one semantic lemma | Applicable method to per-case StorageOps controls. Tables must retain negative/refusal and retained-versus-live observations and accompany an intrinsic parameterized semantic law. No `decide` table substitutes for that law. Yul Raw/vector generation remains H55; no generator is duplicated here. |

This is family-level applicability, **not a completed per-semantic-case audit**.
The full inventory supports the remaining per-case disposition work without
padding the case count. A proposed small starting point was the actual
`modifyMany` scheduler behind OperationControls failure/success cases; its
upstream dependencies fail before a new proof can be checked.

## Validation and resource evidence

The coordinator supplied five input files under `/workspace/h62-coordinator-inputs`;
all five SHA256 values match `sha256.json`. The later coordinator instruction
requires the exact official `lean-4.35.0-linux.tar.zst` archive with SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
It was downloaded and verified before extraction outside git. The preinstalled
4.24.0 toolchain was not invoked for migration checks. The definitive final
reproduction explicitly disables local artifact-cache reads and writes; earlier
probes used separate build directories but did not explicitly disable all local
cache reads, so those earlier probes alone do not establish cache isolation.
No tracked toolchain file or module registration was edited.

Actual versions:

```text
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
```

The VM has a 16 GiB cgroup memory cap and zero host swap. Checks hold
`/tmp/solidity-lean-feature-groups-20261025/writer.lock`, set
`LEAN_NUM_THREADS=1`, pass explicit Lean `-j1 -M12288 --tstack=131072`,
and use the supplied guard with a sampled 12 GiB process-group RSS stop and 4 GiB
available-memory reserve. The hard cgroup cap remains the preprovisioned 16 GiB; the 12 GiB group stop
is sampled, not a new kernel memory limit. No systemd scope is created. The build configuration
and products live outside git in separate v4.35 directories. `enableArtifactCache = false` and explicit Lake cache environment settings
disable the local artifact cache in the definitive reproduction; `--no-cache`
also disables package cache downloads. `XDG_CACHE_HOME` is isolated. Earlier
probe configurations did not disable the local cache explicitly. No Lean MCP tool was
exposed; serial CLI checks used the official toolchain. No runtime-pass label
is inferred from provisioning or from the prerequisite.

| Check | Result / evidence |
| --- | --- |
| Six census scanner tests | Pass, exit 0. |
| Frozen-source deterministic census acceptance | Pass, exit 0; all 230/230 original file hashes match the exact base. |
| Pinned v4.35 KeySort | Pass, exit 0; 1.517 s, sampled peak group RSS 519,495,680 bytes. `evidence/keysort-v435.log{,.json}`. |
| v4.35 `lake ... --no-cache build Solidity.Backend.StorageOps.OperationFamilies` | **Fail**, exit 1; 20.011 s, sampled peak group RSS 1,657,294,848 bytes. `evidence/dependencies-v435.log{,.json}`. |
| Reproduction driver, isolated fresh output | KeySort passes (1.513 s); dependency build **fails**, driver exit 1 (18.970 s, 1,667,461,120 bytes). `evidence/reproduction-driver.log`, `reproduction/dependencies.log{,.json}`. |
| Corrected driver, freshly extracted verified archive | KeySort passes (1.514 s, 519,446,528 bytes); dependency build **fails**, driver exit 1 (19.211 s, 1,666,662,400 bytes). `evidence/final-keysort.log{,.json}`, `evidence/final-dependencies.log{,.json}`. |
| Definitive corrected driver, local artifacts disabled | KeySort passes (1.717 s, 518,828,032 bytes); dependency build **fails**, exit 1 (20.295 s, 1,657,606,144 bytes); no guard stop. `evidence/isolated-keysort.log{,.json}`, `evidence/isolated-dependencies.log{,.json}`, `evidence/isolated-lakefile-v435.toml`. |
| Full affected validation / normal run-lean.sh / sort-conformance | Pending: dependency migration failure; no RUNTIME_GATE_PASS. |
| Before/after same-condition comparison | Pending: no migration implemented, so no delta or >10% acceptance claim. The fresh dependency failures are reproduction checks, not before/after measurements. |

An initial timing invocation found `/usr/bin/time` absent; no Lean check ran
in that invocation and it was not counted as passing. The Python guard then
provided the actual measurements above. Peaks are 100 ms sampled RSS, not exact
maximum allocations.

Reproduce after obtaining the pinned archive/toolchain and inputs:

```sh
flock -n /tmp/solidity-lean-feature-groups-20261025/writer.lock \
  python3 -B scripts/h62/item4/generic-storageops/reproduce-dependency.py \
  --toolchain /workspace/h62-generic-storageops/lean-4.35.0-linux \
  --output /workspace/h62-generic-storageops/reproduction-isolated
```

## Independent read-only reviews

Finder and skeptic used neither Lean server nor heavy builds. Both independently
confirmed all 230 original file pins and found a real mutual/end scope bug that
misnamed 139 declarations (117 theorems); the finder additionally found missing
ambient variable context in statement hashes. Both were fixed and covered by
regressions. Both rechecks pass for the frozen textual corpus, agree on all
6,036 qualified declarations and the inventory digest, and explicitly reject
interpreting this as semantic proof or full assignment completion.

Final tooling review also found that a guard stop could return success for
a SIGTERM handler exiting zero, extracted tool binaries were not linked to the
archive pin, and inherited Lean paths could defeat build isolation. The guard
now forces nonzero on every stop and kills surviving group descendants; two
process regressions cover timeout/normal failure. Reproduction freshly extracts
the verified archive, clears inherited Lean paths and explicitly disables the
local artifact cache (the finder caught that `--no-cache` alone is insufficient). Acceptance checks use
explicit failures rather than optimization-sensitive Python assertions.
Read-only rechecks and their evidence are retained in the external handoff. Nothing in these source checks proves a StorageOps semantic
statement; no theorem, helper lemma, new axiom, `sorry`, `native_decide`, raised
heartbeat budget or frozen-interface change was introduced.

## Blockers and next checkpoint

`B-TOOLCHAIN-RAW` is an external migration dependency: pinned Lean4.35 rejects
String/Slice APIs at `Solidity/Syntax/Raw.lean` lines 597, 650, 665, 682 and 684.
The file is outside this lane's exclusive write scope. Do not patch it here;
coordinator must supply the migration owner's compatible dependency and arrange
an authorized integration overlay. The exact errors and failing command are in
the saved dependency logs.

`B-V10-RELAY` is the required future owner agreement, not permission inferred
from silence. No relay script is present in the checkout, no request was
delivered and no existing family file was edited. Obtain V10 exact-file approval
before changing `Solidity/Backend/StorageOps/OperationControls.lean` or another
original selected after the census; owner applies migration patches. New helpers
stay additive in the assigned test directory, registration fragments await the
coordinator, and generated roots/module maps/axiom pins stay untouched.

All four queue checkpoints remain open: (1) textual census done, semantic-case
classification unfinished; (2) parameterized intrinsic lemma and typed fixture
table pending; (3) correspondence, refusal coverage and semantic acceptance
pending; (4) same-condition before/after timings and full final validation
pending. No H55 work was duplicated. The goal must remain blocked/unfinished,
not complete. Resume on this VM/branch after the dependency is supplied; do not
create a replacement goal or push, merge, publish or pre-gate.

Final static checks: Python syntax and this document's relative link pass;
`git diff --check` passes. Guard regression output is saved in
`evidence/guard-tests.log`; optimization-enabled census acceptance output is
saved in `evidence/acceptance-optimized.log`.
