# H62 item 4: generic-p10

The full four-checkpoint assignment remains **unfinished**. This checkpoint
delivers reviewed source-accounting backfill only. No generic semantic lemma,
typed execution fixture table, correspondence proof, Lean gate, or proof timing
comparison has passed. No original declaration or frozen interface changed.

The assigned branch is `codex/solidity-h62-4-20261106/generic-p10`, based exactly
on `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. The VM checkout is
`/workspace/solidity-h62-4-generic-p10`. The initial clean checkout at
`/workspace/solidity-lean` on `work`, head
`6cf853aea0417155aca29ddb91f1767d3f3a3cc4`, was preserved. Fetching the exact
published base and `origin/master` succeeded; `git merge-base --is-ancestor`
confirmed the assigned base belongs to the remote history. No push, merge, PR,
deployment, generated-root write, or H55/Yul generator work occurred.

## Census and audit matching

The deterministic scanner visits every `.lean` file in the RoadmapV15 family,
including controls outside filenames ending in `Controls`. It records exact
UTF-8 source hashes, named and anonymous declarations, statement hashes, source
locations, complete structure fields, declaration hashes, and diagnostic/trust
commands. Anonymous examples and the local anonymous instance receive ordinal
IDs within their files. Whole-file hashes also freeze namespaces, imports,
options, attributes, comments, and proof bodies.

| Inventory | Count |
|---|---:|
| Original family files | 198 |
| Files ending in Controls | 76 |
| All theorems / anonymous examples | 1,525 / 33 |
| All definitions / abbreviations | 501 / 1 |
| All structures / local instances | 7 / 1 |
| Total original declarations | 2,068 |
| Controls theorems / anonymous examples / fixture definitions | 787 / 33 / 307 |
| Guarded diagnostic commands / axiom print commands | 190 / 1,270 |
| Repeated private-name candidate groups within Controls | 32 |

The complete original inventory, with every captured statement and source
hash, is the off-git `census.json`; its SHA256 is committed in
`tests/h62/item4/generic-p10/census-receipt.json`. This is the full declaration
inventory, not a claim that a conjunction contains only one semantic case or
that every candidate is equivalent. Every original conjunction remains verbatim.

| Audit item | Application and boundary |
|---|---|
| 9: parameterize twin packets/controls | Inventory makes the P10 per-case declarations available for comparison. The audit's specific Backend/Evm paths belong to other families and were not changed. Similar names are candidates, not proof of semantic equivalence. |
| 11: shared helpers and fixtures | 32 repeated private-name groups identify candidates such as `seed` (19), `u` (17), `execute` (16), `site` (15), `spill` (15), `expected` (13), and `shape` (8). Their signatures and bodies remain independently hashed. A name match does not authorize replacing its semantics. |
| 16: per-case packets to typed table plus lemma | The approved P10 assignment uses this transformation pattern. ByteObservation's nine positive execution controls are a concrete candidate. H28/NumericLiteral/Yul Raw work and the H55 vector generator remain excluded. |

The scanner is a bounded lexical source tool, not a Lean parser or elaborator.
It refuses unsupported indented/inline-attributed declaration forms and missing
or empty family directories. In this pinned corpus, independent reviewers
confirmed the declaration counts and source hashes. Candidate flags for errors,
negative conclusions, binders, and kernel decisions require semantic review.
They must not determine proof acceptance or justify dropping cases.

## Acceptance and independent reviews

Reproduce from the assigned checkout:

```sh
python3 -B scripts/h62/item4/generic-p10/census.py \
  --output /workspace/generic-p10-artifacts/evidence/census.json
python3 -B scripts/h62/item4/generic-p10/accept.py \
  --inventory /workspace/generic-p10-artifacts/evidence/census.json
python3 -B tests/h62/item4/generic-p10/negative_acceptance.py \
  --inventory /workspace/generic-p10-artifacts/evidence/census.json
```

Acceptance checks the committed inventory receipt, exact base file set, each
source against `git show` at the published base, byte-identical reproduction,
branch ancestry, and staged/unstaged/untracked write scope. Generating a new
inventory does not update the committed receipt. H44 forbids bulk output inside
the repository. All commands, exits, durations, and log hashes are recorded in
`/workspace/generic-p10-artifacts/evidence/gates.json`.

| Gate | Outcome |
|---|---|
| Scanner adversarial unit tests | PASS: 18 tests, including defaults, nested lets/comments, strings/chars, anonymous cases, malformed input, field weakening, and guard-output mutation |
| Source reproduction acceptance | PASS: all 198 pinned files, exact inventory, base ancestry, sole write scope |
| Negative acceptance | PASS: checksum tamper, missing source, forged base hash, empty inventory, and changed theorem statement all refused |
| `node scripts/check-layers.mjs` | PASS: 857 core modules, zero reaches to elaborators or checked parser adapters |
| Frozen-family diff / `git diff --check` | PASS: no family diff, no whitespace errors |
| Generic lemma / typed fixture proofs / correspondence | PENDING |
| KeySort prerequisite / affected Lean checks / full gate | PENDING; no `RUNTIME_GATE_PASS` |
| Same-condition original versus migrated proof timings | PENDING; no slowdown percentage asserted |

Independent read-only finder `/root/census_finder` and skeptic
`/root/census_skeptic` used source/Python inspection, no Lean server or heavy
jobs. They found the omitted local anonymous instance, incomplete structure-field
statement hashes, empty-family false pass, and an index-only write-scope gap.
All were fixed and regression coverage added. Trust commands were also added
to the inventory. Both final rechecks report no remaining concrete finding
within the source-accounting scope. Their read-only sandboxes could not create
the temporary test directory; the parent ran all 18 tests and five forgery
challenges successfully. These reviews do not accept any semantic proof.

## Runtime and ownership state

The VM has a 16 GiB cgroup memory cap and no host swap. No heavy Lean job ran.
Future checks remain serial, with explicit `LEAN_NUM_THREADS=1`, Lean `-j1`,
bounded memory and a 4 GiB available reserve. No `systemd-run` is allowed.
The writer-lock path is
`/tmp/solidity-lean-feature-groups-20261025/writer.lock`. The initial scanner
addition preceded acquisition of a sustained writer lock; subsequent edits,
checks and commit preparation held that lock. No other writer was observed.

All five coordinator-input SHA256 values were checked against the supplied
manifest; the hashes are retained in the receipt. The coordinator's
`toolchain-pin.json` names the official v4.35.0 Linux archive, SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
The downloaded archive matches. Its binary reports:

```text
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
```

The assigned base's tracked pins remain v4.24.0. Installing elan succeeded, but
attempting to provision that toolchain through its release service failed with
proxy CONNECT HTTP 403. No v4.24 cache was used, no tracked pin was changed,
and the v4.35 binary was used only to report its version. Goal inspection is
not exposed by the worker tools; the coordinator explicitly resolved that
optional absence as nonblocking. No replacement goal was created.

| Typed state | Required next action |
|---|---|
| `SCOPE_TOOLCHAIN_APPLICABILITY` | Resolve Q-TOOLCHAIN-01 below before toolchain-dependent proof validation. |
| `OWNER_RELAY_REQUIRED` | V15 owns original family files. No `relay.sh` or exact-file owner agreement is available locally. Additive work is permitted; original-file migration remains prohibited. The saved exact-file request identifies the proposed ByteObservation control file. This is coordination, not a request to the human to waive ownership. |
| `PROOF_WORK_QUEUED` | Prove an intrinsic parameterized execution lemma using the existing native semantic theorem, then a typed fixture table. Do not replace fetched execution with a decision table or add a success premise equivalent to the conclusion. |
| `CORRESPONDENCE_QUEUED` | Connect each migrated original declaration as an exact instance where possible; retain all negative/refusal/guard observations and prove the correspondence. |
| `VALIDATION_QUEUED` | Run version/KeySort prerequisite, per-file diagnostics or authorized fallback, transitive axiom checks, affected/full gates, and same-cache/tree/resource timing comparison. Stop for slowdown above 10%. |

`ESCALATE: Q-TOOLCHAIN-01`, sources: coordinator toolchain update and base
`lean-toolchain`. Does “Migration ONLY” apply the pinned v4.35.0 requirement
to this generic-controls lane? The mutually exclusive options are:

1. Retain v4.24.0 for generic-p10; v4.35.0 applies only to migration lanes.
   Generic proof validation then needs the base toolchain provisioned.
2. Validate generic-p10 on pinned v4.35.0 using an isolated overlay; retain the
   assigned base and ownership boundaries. Dependency/source migration must be
   provided by its owners; this lane cannot edit their files.

No option is assumed approved. No exclusion, premise, theorem statement,
interface, resource budget, axiom allowance, or proof budget is weakened.
New Lean declarations/helpers: zero. Frozen statements touched: zero.
New axioms/sorry/native_decide: zero. The 10% proof-time gate remains unmeasured.

The original patch, committed-head receipt, handoff, complete inventory,
individual gate logs, review record, and checksum manifest are saved under
`/workspace/generic-p10-artifacts`. The off-git handoff records the full commit
head after committing; this document deliberately cannot contain its own commit
hash. No checkpoint or elapsed time is treated as completion of the full queue.
