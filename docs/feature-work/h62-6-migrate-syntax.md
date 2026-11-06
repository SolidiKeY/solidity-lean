# H62 migrate-syntax: validated directory overlay, blocked final integration

The assigned Syntax directory builds on the exact official pinned Lean 4.35.0.
All21 assigned modules and their eight local prerequisites pass a clean serial
build. The complete assignment remains **blocked**, not done: actual annotation
and whole-repository gates fail in other migration owners, and root-gate API,
axiom and resource disposition plus handoff receipt remain outstanding.
No RUNTIME_GATE_PASS, merge, push, PR, pre-gate, deployment or freeze announcement.

## Exact checkout and producer artifacts

- Batch/owner: solidity-h62-6-20261106/migrate-syntax.
- Repository: `/workspace/solidity-lean-migrate-syntax`.
- Branch: `codex/solidity-h62-6-20261106/migrate-syntax`.
- Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
- Original checkout `/workspace/solidity-lean` remains on `work`; no reset/discard.
- The base was fetched and verified an ancestor of published origin/master;
  the assigned isolated worktree was created exactly at that base.
- Persistent thread: `01a1b0ed-1b3e-74dc-8ef5-83cceedb6056`.
- VM: `ccarenv_b64_Y2NhcmVudl85MzRiZmM3N2MzZDQ4MTkxODU0MjllMWJjMjI5NmIyOQ`.
- Frozen original prompt SHA256:
  `7611a05a47de7c243a9b39e66c7e3af6edfe382bb638822da45f79917ce663eb`.

The consolidated H70 Raw prerequisite is already committed at
`074e62c1840dd2d7ab19c95ca5d437ebfe57dbb8`. Exact-file patch:
`/workspace/migrate-syntax-evidence/continuation-2/raw-prerequisite.patch`,
SHA256 `34fc66ea93a8a2c956ebb51f225b03593109239c5b46631aaa28bfb24efb2a9a`.
Raw source SHA256:
`a463aa0f978da5d5bae6ba5cffdfa95861a495a8d69942502b706b7b157ec506`;
base source SHA256:
`7c137f7e8e4c70f4868dc41a437687ab42e2d63e887cdde3ba3ccd1ea764b76f`.
`raw-overlay.json` records the exact receipt and historical 65-named-type hash.
The coordinator retrieves/relays artifacts; no direct delivery is claimed.
This is an isolated migration overlay, not a transfer of live producer ownership.

## Coordinator clarifications applied

The coordinator explicitly confirmed that relay.sh is host-only and the
registered isolated migration lane may apply its own statement-preserving
source patches. Existing-file coordination is therefore resolved for this
scope; the earlier pending relay installation request is superseded.
Every live-owner change is recorded in `live-owner-changes.json` for cut-over.
H64 explicitly permits `decide +kernel`; no native proof shortcut is used.

A per-module time/memory increase does not stop a migration lane. Earlier
per-module holds were removed; every module's metrics were retained and the
matched complete directory comparison was finished. The conservative full
comparison tool marks the 90.73% peak-RSS growth STOP/escalated for root
cut-over disposition. No local resource waiver or acceptance is claimed.
The old blocked handoff at 1bdaa3b0 is historical, not the current state.

## Toolchain and fixed-resource measurements

All five `/workspace/h62-coordinator-inputs` inputs match sha256.json.
Official new archive:
`/workspace/migrate-syntax-evidence/toolchains/lean-4.35.0-linux.tar.zst`;
SHA256 `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Lean 4.35.0 reports commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
Lake 5.0.0-src+eb6cafb. Old Lean 4.24.0 reports commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; Lake 5.0.0-src+797c613.
Both official Linux x86_64 releases. No tracked lean-toolchain/lakefile change.

Measurements use explicit `-j1 -M11000 --tstack=131072`, LEAN_NUM_THREADS=1,
CPU affinity {0}, empty private output directories, no Lake artifact cache,
no swap and a monitored 4 GiB host/cgroup available-memory reserve. The VM cap
is 16 GiB; host swap is absent although cgroup swap.max is unrestricted.
One heavy Lean process at a time, no Lean server, no systemd-run.
OS wait4 maximum RSS is a process/descendant maximum, **not simultaneous
aggregate tree RSS**. Filesystem page cache was not purged; clean means no
reused project build outputs/artifact cache. Explicit proof budgets are unchanged.

The final matched driver SHA256 is identical in both result files:
`f807a3828db6424da0a532ade2be8ca5676718d18944f127e9dfa80781e529ea`.
Both have timeout_seconds0 (per-module performance no longer stops the lane),
the same 29-module order and all 29 statuses pass.

| Complete assigned closure | Wall seconds | Peak process RSS KiB |
|---|---:|---:|
| Exact pinned source, old4.24.0 |207.377|885420|
| Owned migration overlay, new4.35.0 |102.747|1688748|
| Change |-50.454%|+90.728%|

Commands, each exit0:

```
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item6/migrate-syntax/measure.py --source-root /workspace/migrate-syntax-evidence/continuation-2/base-source --toolchain /workspace/.setup/tools/lean-4.24.0-linux --output /workspace/migrate-syntax-evidence/continuation-2/old-clean-identical-driver
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item6/migrate-syntax/measure.py --toolchain /workspace/migrate-syntax-evidence/toolchains/lean-4.35.0-linux --output /workspace/migrate-syntax-evidence/continuation-2/new-clean-pass
```

This is the full **assigned-directory import closure**, not a successful clean
whole-repository comparison. Whole-repository acceptance remains blocked.
Initial pre-review and failed diagnostic runs are preserved off git, not passes.
The legacy old-clean-2 measurement 218.691 s is superseded by the identical-driver
repeat; its raw evidence was not silently upgraded. Initial missing GNU time
was handled with wait4, not a package/system change.

## Migration and frozen-interface evidence

Twelve production files changed, all within the assigned scope:

| File under Solidity/Syntax | Change |
|---|---|
| Raw, Grammar | Character-based slice copies/dropEnd/ofList, explicit String suffix predicate |
| Elab/Context, Elab/Values, Elab/Lower | Preserve String results of dropped/suffixed components |
| Elab/Values | Explicit original target-index equalities/transports; eliminate two impossible Boolean cases |
| Elab/Arms | Explicit existing element-index transports in push; unused local name cleanup |
| Elab/Stmt | Match the existing result-context index together with receiver statement |
| LoopWarnings | trimAscii.copy, same space/tab/CR/LF predicate |
| Scoped, Quote | Equivalent String constructor; unused pattern name cleanup |
| CheckedExact | Equivalent ite_true/ite_false proof lemma names |
| Splice | Three exact original printing equalities: rfl to authorized decide +kernel |

No original declaration signature, constructor, import, premise, exclusion,
observation, default tactic or proof budget changed. No production helper,
new axiom declaration, sorry, native_decide or representation layer was added.
GateG0 indexed hot-path representations/sharing remain unchanged. Added
transports are in elaboration-time code. History of Splice/Scoped was inspected;
no earlier sharing/speed change was undone. Checking-cost warning preceded
kernel-proof replacement, and measurements above include those proofs.

The deterministic source census covers all 21 files and29-module closure.
Eight read-only local prerequisites are KeySort, AST, SpecSyntax, the Syntax
umbrella, Scope, Keccak, RevertBytes and ERC7201. Builtin imports are Lean/Std
only. No outside production dependency was edited. No generated root, central
module map, axiom pin or toolchain was edited; no new production registration.

Elaborated environments contain 5711 old and 6232 new owned-module constants.
The fail-closed comparison maps **877 original source declarations**, including
public opaque RecThunk.get and all eight explicitly mapped anonymous instances.
All877 normalized types match with zero missing/changed source declarations.
Frozen type SHA256:
`b51f71e1d1b871d39dce848e51d94cbd9cc956eb3356e4fa88de271b780a0f2a`.
The 20 modules owning declarations are covered; the 21st is import-only Elab.

Normalization erases binder labels/metadata and unfolds autoParam
**definitionally**. The sole rigid source-type difference was private
Scoped.lit's compiler-generated default-tactic helper name. Its original
`by rfl` default source is unchanged. Normalized type identity alone does
not prove default-tactic behavior; raw dumps and unchanged source are retained.
An independent byte comparison covers all **898 declaration headers/defaults**,
including all 21 anonymous example statements, with zero changes.

Complete compiler-generated/other drift remains explicit: 365 old constants
removed, 886 added, with all shared metadata/type differences retained.
The root must audit generated noConfusion/derived implementation names and
compatibility. This is not a whole-generated-API equivalence claim.

Actual transitive axiom collection reports 637 source-declaration growth
entries involving only propext, Classical.choice and Quot.sound. The global
axiom-name union adds **no new axiom name** beyond the old union. The per-entry
changes still require root-gate pin/allowlist audit; no pins were rewritten.
No failed proof artifact or diagnostic sorryAx is accepted as a proof.
See `api-summary.json`, `frozen-complete-interfaces-final.json`, and both raw
unnormalized/normalized old/new environment dumps.

## Proof and external-test boundaries

`controls.py` deterministically generates 22 finite cases of hashing members,
function-type parsing/nesting/refusal, Unicode, top-level comma splitting,
shape/row extraction and hex bytes. All22 new cases use kernel-checked
`decide +kernel`; two arbitrary-string drop/dropEnd list laws also check.
Old String primitives blocked reduction in exploratory old kernel controls;
the identical 22 baseline predicates pass as explicitly labeled runtime
assertions. Twelve separately captured executable observations match old/new,
including nested ABI spellings, reference refusals and whitespace/Unicode.
Those runtime checks supplement proofs; they do not prove general parser
semantic equivalence, compiler totality, solc/EVM/gas or fork correctness.
Original proofs/examples in all 21 files are checked by the clean builds.
Generated fixtures stay off git; generators and acceptance are committed.
No production module registration fragment is needed for these scratch tests.

## Required gates and exact outcomes

- `python3 tests/h62/item6/migrate-syntax/accept.py`: exit0. Reconstructs exact
  pinned 29 sources, verifies 877/8/opaque accounting and 898 original headers;
  scanner comment/string/attribute/cycle/missing-import controls, timing boundary
  controls, real type mutation/missing-row/missing-entire-module controls,
  axiom-growth reporting and empty-subset refusal pass. Empty API input fails;
  partial Raw checks require explicit --modules, not implicit module skipping.
- `gate.py --phase keysort` under bounded.py: exit0. Actual Lake output
  `Built Solidity.KeySort`, `Build completed successfully (2 jobs)`, with
  official Lean/Lake versions printed. See lake-keysort-3/command.log.
- `gate.py --phase sort`: exit1. Actual compilation fails in unchanged
  Solidity/SortCheck/Parser.lean:76 onward (removed trim API); actual taclet
  comparison was not executed. Owner migrate-sortcheck; decisive output in
  lake-sort-diagnostics/command.log. Frozen rules snapshot exists explicitly.
- `gate.py --phase full`: runs actual `bash ./run-lean.sh`, exit1. First genuine
  failure is unchanged Hash/CollisionBound at407,660,680 and dependent guard
  messages. Owner migrate-hash. Later bad imports/cancellations are fallout,
  not independent diagnosed source failures. See lake-full/command.log.
- Static layer, generated-root and fragment checks pass. Final gates use a
  temporary private TOML/sysroot view of the same official compiler, serialized
  workers, no cache and fail-fast; temporary TOML removed after each phase.
  Initial private-wrapper setup errors were fixed before the passing KeySort
  run; they are archived as setup failures, not source/compiler gate passes.
- Matched full-directory comparison records STOP/escalation for the measured
  full RSS growth. Root cut-over disposition remains outstanding; no local waiver.

## Independent read-only reviews and continuation

Separate finder and skeptic reviewed each source/tooling milestone; neither
ran Lean/server or edited files. All confirmed findings were fixed: premature
live pass, comment-as-import, attributed/opaque/local/anonymous declarations,
floating threshold at exactly 10%, equation-body/header confusion, empty API
module skipping, and described-but-unexecuted negative controls. Final reviews
verify source preservation and actual negative controls and endorse the
**blocked** outcome. Evidence: reviews-final.json and accept-final.log.

Remaining: reviewed external SortCheck/Hash overlays, complete affected
examples/TestSuite/whole-repository validation and whole-repository timing,
generated API/per-entry axiom/resource disposition, and migrate-root-gate
receipt/live-owner cut-over relay. Other failures may appear after those first
external prerequisites pass. Do not weaken statements or edit other owners.

Preserve the original goal unfinished/blocked and exact VM/branch. get_goal
is not exposed; coordinator confirms its absence is not a blocker. No goal
was created/reset. This is the fresh-thread handoff after the completed census,
Raw prerequisite, directory migration, interface/control and measurement work;
coordinator owns continuation, not a self-launched replacement thread.
Final export paths/full head/checksums are in the off-git HANDOFF and result JSON.

Historical Raw/Grammar fixtures remain reproducible from the final branch with `python3 scripts/h62/item6/migrate-syntax/fixture.py --from-base --output <fresh off-git directory>`; already migrated inputs are handled idempotently. The fixture retains its UNAPPROVED-FIXTURE-ONLY label and does not replace the committed production overlay.
