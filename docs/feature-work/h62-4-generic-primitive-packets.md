# H62 item 4: generic PrimitivePackets

Owner: `solidity-h62-4-20261106/generic-primitive-packets`. Branch:
`codex/solidity-h62-4-20261106/generic-primitive-packets`.
Repository: `/workspace/solidity-lean`.
Pinned base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. The clean older `work` checkout was preserved;
`git fetch origin master` obtained the base and `git merge-base --is-ancestor
c6f550e281a7e5affa9a99bc2cdaed556dec00e4 origin/master` exited 0. Published master at inspection:
`821e3e8f4c7a5ac3a51dc5cba8be813bb173e310`. The task branch was absent remotely,
so the assigned local branch was created directly at the verified base.
No push, merge, PR, deployment, generated-root, module-map, or axiom-pin writes.

## Checkpoint 1: source census complete

82 original family files, 826 declarations: 453 theorems, 297 definitions,
72 abbreviations, 3 anonymous examples, 1 inductive. The 18 control files have
476 declarations: 216 theorems, 204 definitions, 53 abbreviations, 3 examples.
All original source files remain byte-identical to the pinned base. Complete
signatures, declaration-region hashes, namespace identities and line numbers
are in `/workspace/h62-generic-primitive-packets-evidence/census.json` (off git under H44). The committed manifest pins
its SHA256 and all 82 original-file SHA256 values. Anonymous examples retain
file/line identities. Hashes describe source bytes, not elaborated Lean terms;
full-file hashes also freeze imports, ambient namespaces and proof options.
The scanner is deliberately bounded to this frozen corpus.

| Original control file | Theorems | Anonymous examples | All declarations |
|---|---:|---:|---:|
| `Solidity/Backend/PrimitivePackets/BitNot/Controls.lean` | 20 | 3 | 36 |
| `Solidity/Backend/PrimitivePackets/CheckedAdd/Controls.lean` | 16 | 0 | 31 |
| `Solidity/Backend/PrimitivePackets/CheckedMul/Controls.lean` | 18 | 0 | 36 |
| `Solidity/Backend/PrimitivePackets/CheckedSub/Controls.lean` | 20 | 0 | 35 |
| `Solidity/Backend/PrimitivePackets/Comparisons/Controls.lean` | 8 | 0 | 23 |
| `Solidity/Backend/PrimitivePackets/Constants/Controls.lean` | 16 | 0 | 22 |
| `Solidity/Backend/PrimitivePackets/Shifts/Controls.lean` | 14 | 0 | 19 |
| `Solidity/Backend/PrimitivePackets/SignedCast/CastControls.lean` | 13 | 0 | 29 |
| `Solidity/Backend/PrimitivePackets/SignedCheckedAdd/Controls.lean` | 4 | 0 | 11 |
| `Solidity/Backend/PrimitivePackets/SignedCheckedMul/Controls.lean` | 8 | 0 | 39 |
| `Solidity/Backend/PrimitivePackets/SignedCheckedSub/Controls.lean` | 5 | 0 | 21 |
| `Solidity/Backend/PrimitivePackets/SignedDiv/Controls.lean` | 10 | 0 | 21 |
| `Solidity/Backend/PrimitivePackets/SignedMod/Controls.lean` | 18 | 0 | 30 |
| `Solidity/Backend/PrimitivePackets/SignedSub/Controls.lean` | 20 | 0 | 40 |
| `Solidity/Backend/PrimitivePackets/UnsignedCast/Controls.lean` | 5 | 0 | 19 |
| `Solidity/Backend/PrimitivePackets/UnsignedMul/Controls.lean` | 15 | 0 | 36 |
| `Solidity/Backend/PrimitivePackets/UnsignedMul/WideControls.lean` | 4 | 0 | 23 |
| `Solidity/Backend/PrimitivePackets/UnsignedMul/WidthControls.lean` | 2 | 0 | 5 |

Audit 9 maps 219 declarations in Checked{Add,Sub,Mul} and
SignedChecked{Add,Sub,Mul}/{Agreement,Target,Controls}. Audit 16 maps all
219 control theorems/examples as table/refusal candidates, not automatic
refactor eligibility. Audit 11's concrete in-family candidates are the empty
HRef proofs in UnsignedCast/Controls:66, Comparisons/Controls:37 and
UnsignedDiv/Witness:34; CheckedMul/Populated:61 and :71 have populated-heap
semantics and need separate proofs. SourceReverted/cons-revert/allocation-cost
helpers cited in the broad audit do not occur here. This base has three copies
each of exact_panic_bytes and panic_not_truncated, rather than the older audit's
five. Yul Raw/vector generation remains H55-owned and is not duplicated.

Reproduction (from repository root; Python standard library only):

```sh
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item4/generic-primitive-packets/census.py --output /workspace/h62-generic-primitive-packets-evidence/census.json
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item4/generic-primitive-packets/accept.py /workspace/h62-generic-primitive-packets-evidence/census.json
```

Both exited 0. Decisive outputs: `FROZEN_SOURCE_INVENTORY_PASS` and
`CENSUS_ACCEPTANCE_PASS: complete inventory, six let signatures, nested lets,
comments, ordinary/optimized refusal`. The acceptance is external testing,
not a Lean semantic proof. It checks refusal with Python optimization enabled.

Finder and skeptic independently reviewed the corpus read-only, neither using
a Lean server or making fixes. They found six signatures truncated at type-level
let initializers and assert-based gates disabled by Python optimization.
Both were fixed; both re-reviews passed. Evidence: `/workspace/h62-generic-primitive-packets-evidence/reviews-census.txt`.

## Runtime and current blockers

Coordinator inputs in `/workspace/h62-coordinator-inputs` match all five hashes
in sha256.json. The official v4.35.0 linux archive matches
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Lean: `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release.
Lake: `5.0.0-src+eb6cafb`. No v4.24 artifacts are used for migration checks.
Version evidence: `/workspace/h62-generic-primitive-packets-evidence/keysort.log` (initial timing executable was absent).
The corrected check uses Bash `time -p`: `LEAN_NUM_THREADS=1 lean -j1
--tstack=131072 -o /workspace/h62-generic-primitive-packets-evidence/build/Solidity/KeySort.olean Solidity/KeySort.lean`.
Exit 0, wall 1.16 s; `/workspace/h62-generic-primitive-packets-evidence/keysort-check.log`. AST check also passed, 6.04 s,
with deprecation warnings. This is a prerequisite result, not a full runtime gate.
VM cgroup memory cap: 16 GiB; no active swap; jobs bounded to 12 GiB address
space with a 4 GiB available reserve; writer lock held; no systemd-run.

**B-MIGRATION-HASH**: The 231-module CheckedSub.Controls import closure fails
under pinned v4.35 at `Solidity/Hash/CollisionBound.lean`:407 (List.contains
function equality), :660 and :680 (omega), followed by axiom-message guard
failures caused by unsolved proofs. That source was not modified. This is not
a source sorry insertion. Owner per snapshot:
`solidity-h62-6-20261106/migrate-hash` (isolated migration overlay); proving-owner
ownership remains intact. Logs: `/workspace/h62-generic-primitive-packets-evidence/dependency-results.json` and
`/workspace/h62-generic-primitive-packets-evidence/dependency-logs/Solidity.Hash.CollisionBound.log`. Exit 1.
No dependency failure is accepted as proof or axiom evidence.

**B-OWNER-RELAY**: Existing family originals are read-only. No exact-file owner
agreement has arrived. relay.sh is absent at this base; no original was changed.
V09 coordinates family owners. Any migration patch remains owner-applied only.

## Remaining checkpoints and committed handoff

Checkpoint 2: pending PrimitivePackets semantic parameterized lemma and owner
migration; isolated typed arithmetic fixture backfill is being checked.
Checkpoint 3: census reproduction passes; EVM/Source correspondence and complete
semantic refusal validation await the failed prerequisite and owner relay.
Checkpoint 4: same-condition original-versus-migrated timing, full affected final
validation and full run-lean.sh remain pending. No valid speed delta exists;
stop migration if the measured slowdown exceeds 10 percent. The warning about
checking speed was given before edits; recent family history was inspected.
The full original case inventory is retained in the off-git census and manifest.
This milestone is not completion of the four-checkpoint assignment.
