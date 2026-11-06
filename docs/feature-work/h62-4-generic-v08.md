# H62 item 4: generic V08 controls

Owner: `solidity-h62-4-20261106/generic-v08`. Frozen base:
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. Checkout:
`/workspace/solidity-lean`; assigned isolated branch:
`codex/solidity-h62-4-20261106/generic-v08`.

Status: unfinished. Census implementation and independent static reviews pass.
The generic execution lemma, exact original theorem instances, correspondence,
family measurements and full final validation remain required. Existing family
files are read-only. No permission to migrate them has been received.

## Census checkpoint and handoff

The deterministic scanner includes all 220 V08 files, not only filenames ending
in Controls. It retains 4,428 declaration rows: 2,619 theorems, 1,616 definitions,
138 abbreviations, 20 instances, 18 inductives and 17 structures. Controls files
contain 2,951 declarations, including 1,589 theorems. No original is removed.
Each source file is hashed; each declaration has its exact lexical header and
SHA256, source path, line, kind, written name and ordinal. Anonymous declarations
retain ordinal identities. Consumers must key by `(path, ordinal)`, since nested
namespaces can repeat written names. Multiple conjuncts and cases within a
statement remain verbatim, rather than being silently split or dropped.

Header hashes are lexical fingerprints, not elaborated Lean statement hashes.
Full file hashes additionally protect section variables, namespaces, imports,
proof bodies and all negative/refusal controls. The scanner is not an evaluator,
compiler, theorem prover or H55 vector generator.

Full original inventory: `/workspace/generic-v08-evidence/inventory.json`.
SHA256: `be03b64ac04c24940e39e24a75b806abf042524233bc465b1ed5109aad406096`.
Bulk stays off git. The committed manifest retains every original file hash,
counts and the full inventory checksum; the committed generator reproduces the
complete inventory from the exact base. Acceptance refuses any source change.

Commands (from this checkout):

```sh
python3 -B tests/h62/item4/generic-v08/test_census.py
python3 -B scripts/h62/item4/generic-v08/accept.py
python3 -B scripts/h62/item4/generic-v08/census.py --revision c6f550e281a7e5affa9a99bc2cdaed556dec00e4 --write /workspace/generic-v08-evidence/inventory.json
python3 -B scripts/h62/item4/generic-v08/census.py --check /workspace/generic-v08-evidence/inventory.json
```

Eleven mutation/parser tests pass. They cover nested comments and strings,
proof-body versus statement mutations, default binder values, equation-style
definitions, complete match and let theorem conclusions, named instances,
anonymous cases, nested module discovery and malformed-source refusal.

## Audit applicability

Source: coordinator-supplied `refactor-audit-20261106.md`, SHA256
`31ab16906906a9b22fd28700aacc72d2ee0ffe81cea723ae209eb28e5299286a`.
All five supplied inputs match `/workspace/h62-coordinator-inputs/sha256.json`.

| Item | Exact audit target | Application to this lane |
|---|---|---|
| 9 | Backend/Evm twin controls and compiler families | Generic-proof strategy is relevant; those named families are outside V08 and are not edited. V08 inventory provides the exact candidate source set. |
| 11 | Backend/Evm shared lemmas and memory fixtures | Shared semantic lemmas inform the approach. No Evm/Backend helper or fixture migration is claimed. |
| 16 | StatementGrammarH28/NumericLiteralProofs packets; Yul Raw | Typed table plus generic proof is the method. Those packets and Yul Raw are outside this lane. H55 remains owner of Yul Raw/vector generation; no generator is duplicated. |

This applicability map does not assert that every V08 control has the same
statement shape. Runtime frames, admission, payloads, source and target state
relations and their existing exclusions must stay distinct where their exact
statements differ.

## Independent census reviews

Separate read-only finder and skeptic agents used no Lean processes or server.
Both found three truncated match-conclusion headers in `SourceCallPhase`.
The skeptic also found nonrecursive current-tree discovery and resource-reporting
issues. Named instance names were lost, and path/name pairs were ambiguous.
All confirmed defects were fixed. Regressions were added for match conclusions,
let binding, named instances and nested modules. Re-reviews pass for the current
220-file/4,428-declaration inventory. Reviewers ran ten tests read-only; the
remaining temporary-directory test passed in the authorized main-worker run.
The resource harness now labels requested threads, per-process address-space
limits and nonaggregate RSS accurately and refuses surviving process groups.

## Environment and validation boundary

Setup recovered an older clean checkout at `6cf853aea0417155aca29ddb91f1767d3f3a3cc4`.
Fetched the exact base and master without discarding work; verified the base is
an ancestor of fetched `origin/master`; no remote task branch existed. Assigned
branch was created at the exact base under the repository writer lock.
`get_goal` is not exposed; coordinator explicitly says its absence is optional
and not a blocker. No second goal was created.

The official coordinator-pinned archive is Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake 5.0.0-src+eb6cafb.
Archive SHA256:
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
It is extracted at `/workspace/generic-v08-tools/lean-4.35.0-linux`.
The original tracked toolchain and cache are untouched. New artifacts are under
`/workspace/generic-v08-evidence/v435/lib`, exclusively built with that release.
The initial 4.24 build is historical setup evidence only and is not an accepted
migration gate (its checker invocation also had an invalid extra `--`).

VM memory cap: 16 GiB, no configured host swap. Checks are serial with explicit
`-j1`, `LEAN_NUM_THREADS=1`, a 12 GiB per-process address-space limit, a sampled
4 GiB available-memory reserve and a 300-second per-file timeout. No systemd-run.
The reserve check is sampled, not a hard aggregate RSS cap. No Lean MCP tools
are exposed; pinned per-file CLI checks provide actual diagnostics. Final
repository build validation remains pending.

| Gate | Actual outcome / decisive evidence |
|---|---|
| Official archive and all coordinator input hashes | PASS, exact published checksums |
| KeySort under pinned release | PASS, exit 0, 1.758 s, `v435/KeySort.log` |
| AST under pinned release | PASS, exit 0, 7.773 s, `v435/AST.log` |
| SortCheck annotations | PASS, exit 0, 1.505 s, `v435/solkeycheck.log` |
| SortCheck parser prerequisite | FAIL, exit 1; `Parser.lean:76` uses removed `String.trim`, followed by dependent errors; `v435/solkeycheck.log` |
| ABI dependency closure | FAIL at unchanged `Hash/CollisionBound.lean:407`, `:660`, `:680` and guarded outputs; `v435/Solidity.Hash.CollisionBound.log` |
| Complete solkeycheck and `./run-lean.sh` | PENDING behind failed prerequisites; no RUNTIME_GATE_PASS |

The blocked prerequisite files are outside the sole write scope. Neither is
patched or bypassed. Runtime/provisioning checks are not semantic proofs.

## Outstanding queue and typed blockers

1. Census source integrity and audit map are available; full elaborated statement
   fingerprints and runtime milestone validation remain pending.
2. Required generic *execution* lemma, full typed case migration and exact original
   declaration instances: pending. Isolated width-admission backfill is separate.
3. Required source/target correspondence, all negative/refusal semantic checks and
   runtime reproduction acceptance: pending. Static reproduction acceptance passes.
4. Full family before/after measurements under matching tree/cache/resources:
   pending. Timing delta is **unavailable**, not zero. No speedup is claimed and
   no refactor has been deployed. Stop if a future measured migration exceeds 10%.

`DEPENDENCY_TOOLCHAIN`: owners must migrate the parser and collision-bound proof
prerequisites to the pinned release, or the coordinator must provide their
approved isolated overlay. No family semantic proof gate can be claimed now.
`OWNER_RELAY`: no exact-file owner agreement exists; existing V08 files remain
read-only. No relay tool or coordinator host relay script is installed here.
Registration fragments must be supplied for owner/coordinator application; no
central map, generated root, axiom pin or frozen interface is changed.

No merge, push, PR, publication, pre-gate or deployment was performed. Preserve
the existing goal as unfinished; do not create a replacement continuation.
