# H62 item 4: generic memory copies

Status: **blocked; full four-checkpoint assignment is unfinished**.
Batch `solidity-h62-4-20261106`; lane `generic-memorycopies`.
Repository `/workspace/solidity-lean`; branch
`codex/solidity-h62-4-20261106/generic-memorycopies`; exact base
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
The base was fetched from origin and verified an ancestor of published master.
No push, merge, PR, cut-over, generated-root change, axiom-pin change, or owner
file edit was performed. No second goal was created. Goal inspection is not
exposed; the coordinator explicitly says this is not a blocker.

## Delivered source census and backfill

The deterministic scanner inventories **300 files / 3,905 declarations /
2,075 theorems**, including **97 Controls files / 2,828 declarations /
1,519 theorems**. It records each complete file hash and each declaration's
name, kind, line, exact header bytes, UTF-8 byte offsets, header hash and source
region hash. The full named inventory is off Git at
`/workspace/h62-generic-memorycopies-evidence/frozen-inventory.json`:

`9edeca091a08071f42b17f698c4a184a7debc4cf6367d58bac81162eba845de5`.

These are lexical headers, not elaborated signatures. Structure and inductive
headers exclude fields/constructors; complete file hashes preserve those, proof
budgets, imports, section variables and all original bodies. The scanner is a
source tool for this frozen family, not a complete Lean parser.

Audit matching is deliberately conservative and retains every inventory row:

| Audit item | Candidate mapping | Count |
|---|---|---:|
| 9 | Declarations in path-labelled family files | 787 |
| 11 | Named repeated intrinsic heap/allocator/representation fixtures | 371 |
| 16 | Every theorem in Controls-labelled files | 1,519 |

There are 402 negative/refusal name signals across all family files, including
controls outside Controls filenames. These signals are navigation aids, not an
exhaustive semantic classification. Every case is protected by full-file pins.
`audit-candidates.json` retains all 3,905 rows and has SHA256
`492b0870104bf630491306b1d1d3a694fc78ad8b7eb78c7d2082c556110f6242`.
No H55 Yul Raw/vector generator was copied or replaced. Audit 16's H55 part
remains outside this lane.

## Checkpoint state

1. **Partial:** complete source inventory and candidate audit 9/11/16 matching;
   semantic per-case grouping and owner-approved migration remain pending.
2. **Blocked:** no new intrinsic generic copy lemma or typed semantic fixture
   table is claimed. Existing declarations have not been replaced.
3. **Partial:** deterministic external reproduction acceptance passes and all
   original negative/refusal source is unchanged; kernel correspondence and
   affected semantic validation remain blocked.
4. **Blocked:** full inventory is delivered, but family baseline/candidate
   measurements under equal cache/resource conditions have not been obtained.
   No speed delta, >10% acceptance, or final runtime gate is claimed.

There are **zero new Lean declarations, zero new axioms, zero new sorrys and
zero frozen statements touched**. This backfill is not semantic completion.

## Toolchain, resources and gates

All five coordinator input files passed their SHA256 manifest. The official
archive `/workspace/h62-toolchain/lean-4.35.0-linux.tar.zst` matches the pin:
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Actual versions: Lean **4.35.0**, release commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake **5.0.0-src+eb6cafb**.
The tracked toolchain pin was not edited, and the old v4.24 cache was not used.
An off-Git alternate configuration selects a private `build-v4.35.0` directory.

The VM has a 16 GiB cgroup memory cap and no host swap. Checks used the writer
lock, `LEAN_NUM_THREADS=1`, `-j1`, `-M8192`, `--tstack=131072`; no systemd-run.
The dependency-order runner checks one module at a time, samples process-tree
RSS every 0.25 s, enforces a 4 GiB available reserve and stops at 300 s/module.
Sampled peaks are not exact maxima or a separate hard cgroup cap.

| Command/check | Outcome and decisive evidence |
|---|---|
| Official `lean --version`, `lake --version` | Pass; `toolchain.json` records versions and archive hash |
| Bounded direct `lean -j1 -M8192 --tstack=131072 Solidity/KeySort.lean` | Pass, exit 0, fresh 2.0507 s, child maxrss 507,276 KiB; `keysort.json`, `keysort.log` |
| Private Lake `build Solidity.AST` | Pass, exit 0, 10.8105 s including KeySort; AST deprecation warnings retained; `ast-prerequisite.json` and log |
| Serial CopyPaths prerequisite chain | KeySort, AST cached checks pass; SpecSyntax passes; **Syntax.Raw fails**, exit 1, 4.5214 s, sampled peak 1,612,214,272 bytes; `module-checks.json` and per-module logs |
| `python3 -B tests/h62/item4/generic-memorycopies/test_census.py` | Nine parser/regression tests pass |
| `accept.py --frozen … --audit … --output …` | `EXTERNAL_ACCEPT_PASS`; exact 300 published-base blobs, repeat census bytes and audit reproduction, tests exit 0; `acceptance.json` |
| Layers, registration, fragments, diff whitespace | Read-only checks pass; saved command/exit logs in evidence |
| Full affected Lean checks, `./run-lean.sh`, axiom replay, same-condition before/after | Pending, blocked by unowned Syntax.Raw prerequisite and missing candidate migration |

The first timing wrapper could not run because `/usr/bin/time` is absent
(exit 127); it was replaced with Python timing before counting KeySort as
passed. One read-only sandbox parser-test attempt could not create a temporary
directory; the authorized writable-temp retry passed all nine tests, with both
outcomes retained in evidence. Cached ~0.25 s prerequisite checks are not fresh-build measurements.
No `RUNTIME_GATE_PASS` is asserted.

## Typed blockers and relay handoff

**B-RAW-435 / prerequisite-owner:** `Solidity/Syntax/Raw.lean` at lines
597, 650, 665, 682 and 684 does not typecheck with v4.35 String APIs. Examples:
`HashKind.ofName? (f.drop 1)` now supplies `String.Slice` instead of `String`;
`String.Slice.toList` and `String.dropRight` are absent. This is a real compiler
failure, not a resource stop. Its registered migration owner is
`solidity-h62-6-20261106/migrate-syntax` (ownership snapshot). No repair was
attempted outside scope. Resume after the coordinator supplies an approved
migration overlay, then rerun the same serial prerequisite command.

**B-OWNER-RELAY / owner-agreement:** family originals remain read-only.
The saved exact-file relay request for CR/V11 is:
`Solidity/Backend/MemoryCopies/CopyPathControls.lean`,
`Solidity/Backend/MemoryCopies/MemoryPathCopyControls.lean`, and
`Solidity/Backend/MemoryCopies/FixedPathCopyControls.lean` for a first
path-copy fixture migration review. This is a request for owner coordination,
not permission inferred from silence. No agreement or owner-applied migration
patch is present. A `relay.sh` tool is absent from this checkout; the local
coordinator can relay this saved request. Owners retain live producer ownership.
Other family controls remain inventoried and in scope for later groups.

**B-SEMANTIC-GATES / dependent:** generic proofs, typed data tables, exact
instance proofs, negative/refusal correspondence, all affected checks and
same-condition timing with the >10% stop rule remain pending. No exclusions,
weakened statements, increased proof budgets or trust shortcuts are proposed.

Resume commands (repository cwd; one heavy check at a time):

```sh
python3 -B scripts/h62/item4/generic-memorycopies/check_modules.py \
  --toolchain /workspace/h62-toolchain/lean-4.35.0-linux \
  --evidence /workspace/h62-generic-memorycopies-evidence \
  Solidity.Backend.MemoryCopies.CopyPaths
python3 -B scripts/h62/item4/generic-memorycopies/accept.py \
  --frozen /workspace/h62-generic-memorycopies-evidence/frozen-inventory.json \
  --audit /workspace/h62-generic-memorycopies-evidence/audit-candidates.json \
  --output /workspace/h62-generic-memorycopies-evidence/acceptance.json
```

After an approved original-file migration, preserve the original frozen
inventory and build a separate correspondence acceptance mode; do not overwrite
the baseline merely to make byte-preservation acceptance pass. New canonical
module registrations must be supplied as coordinator fragments, not root edits.

## Independent read-only reviews

Finder and skeptic used no Lean server and made no edits. The finder discovered
truncation at type-level lets, a top-level match, and control statements outside
Controls filenames. Fixes cover all family declarations and add chained-let,
match, equation, where and nested-file regressions. The skeptic requested
precise header terminology and recursive discovery; both were fixed. Both
independently reproduced all 300 file hashes and 3,905 header slices/hashes.
Final hardening fixes resolve all driver path arguments, verify the official
archive and actual Lean/Lake versions, and describe resource peaks as sampled.
Review records are saved in `reviews.md` in evidence. All accepted findings
were fixed; semantic checkpoints remain explicitly unfinished.

This is the handoff after three independent backfill items (census, audit
mapping, deterministic acceptance) and the prerequisite diagnosis. Continue the
same original VM, branch and goal; do not create a replacement goal/thread.
The coordinator must arrange the next thread after resolving the blockers.
Artifact metadata records the full committed head, patch, evidence archive and
SHA256 manifest under `/workspace/h62-generic-memorycopies-artifacts/`.
