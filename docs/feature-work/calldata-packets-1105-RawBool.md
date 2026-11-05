# G35-BOOL-RAW-1105: raw Boolean calldata packet

Assigned base: `b86ae4568cef6d6226f4d170360bbb089debe3fb`.
Parent/checkpoint start: `a77c1f6b2dfe5c4128315a96e0e52e2b8efdc543`.
Branch: `codex/solidity-fullscope-20261104/vt1-solc-validation`.
Repository: `/workspace/solidity-lean`; same original VM/goal.
Integrator: V11. This is the explicitly assigned H10/H12 rebalance item; original
VT1 T01/T02 queues, holds, failures and seals remain unchanged and incomplete.

## Implementation and proof boundary

Execution.lean follows the published RawUint packet structure and consumes the
existing SourceRawBoolEntry/SourceRawBoolCopy producers, decoder, allocator,
entry guard and intrinsic checked transfer. RawUint and all producer modules
are unchanged. No H16 Source or frozen Core ExtCall edit, new syntax/evaluator,
axiom, sorry, native_decide, exclusion, heartbeat or recursion-limit change.

`canonicalWord` computes whether a raw natural equals 0 or 1. `valid` checks all
actual zero-padded 32-byte frame words; `payload` derives their Boolean values.
The unconditional `copy_run` theorem proves the actual Source cdToMem result:
computed validation success allocates exactly that payload at heap.next; dirty
input returns `.revert []` with the complete initial state unchanged. There is
no assumed successful decoder, copy result, payload or postheap premise.
`decode_bool` proves both cases for arbitrary natural words; `dirty_at` derives
failure from any actually dirty element. `copy_observations` preserves old heap
addresses, locals and every non-heap state field in either branch.

`guarded_run` retains entry-before-validation order. `guarded_frame_run` exposes
all three cdTail checks and raw Boolean validation using explicit initial
`selectorBytes.length=4` and `F.cd=selectorBytes++data` premises. `eval_copy`
consumes an existing intrinsic local calldata reference, with its explicit
initial local binding and horizon n+2. No output equation is a premise.

The derived decoded table publishes an object only when the raw validator
succeeds. `table_bools` proves exact lookup or rejection; `transfer` proves the
existing intrinsic checked transfer from the same computed payload. Its only
extra premises are initial source-slice and destination-capacity bounds, as in
the template. No native EVM, physical byte-memory, gas or compiler adequacy is
claimed. Standalone copies intentionally pad missing bytes; dynamic entry
rejects a truncated span. This distinction is not a language exclusion.

All 55 public elaborated signatures are exported by Signatures.lean. The
resulting log supplies exact quantified types/premises; the two source modules
retain their complete statements. All 64 public/private proof axiom sets are
printed and checked by audit.py, allowing only existing propext,
Classical.choice and Quot.sound. Central pins/registration remain coordinator-owned.

## Inhabited controls

Controls.lean executes real Source operations with a nonempty old heap and
retained aliases. It covers 0/1 order, fresh allocation, old-object framing,
accepted false prefix then dirty2, maximum-word rejection, high-bit 2^255+1
with canonical low byte, full-state/alias preservation on rejection, guard pass
then dirty failure, absent length, truncated elements, oversized length, zero
entry/copy, empty-frame standalone padding, partial-word right padding, actual
local conversion and horizons0/1, validated target transfer and dirty refusal.
Missing table offset, invalid source slice and insufficient destination capacity
are rejected. The target starts [true,true,false] and ends [true,false,true],
so both selected cells must change and the untouched prefix remains observable.

## Reviews and corrections

Separate read-only finder and skeptic reviews used no Lean/server. They found no
semantic defect in the computed classification or explicit premises. The
skeptic identified a weak transfer fixture (second destination already true);
changed it so both cells must change, and added the high-bit dirty control.
Added the finder's suggested bad bounds/missing-offset controls. Both reviewers
confirmed the fixes and reported no unresolved concrete defect in this scope.

During implementation a redundant terminal tactic and an owned unused simp
argument were removed. Concrete entry controls initially used undecidable Halt
equality; replacing whole-expression reduction then hit default recursion depth.
They were split into actual raw head/length/span facts and ordinary guard
rewrites, retaining statements and default budgets. All failed logs are retained.

## VM verification and reproduction

Lean4.24.0 (797c613eb9b6d4ec95db23e3e00af9ac6657f24b), Lake5.0.0-src+797c613.
RUNTIME_GATE_PASS: fresh KeySort check passes with the verified runtime.
Docker hard memory.max=12884901888, memory.swap.max=0, one CPU; admission and
ongoing available-memory reserve4GiB. The runner samples aggregate RSS and aborts
if more than one Lean frontend is observed. Each module is checked separately,
with <=180s/module and <=300s/group; aggregate budget14400s is guarded.

Lake's CLI in this toolchain has no -j option. The scope-local copy of the
unchanged configuration adds `-j1` to weakLeanArgs; LEAN_NUM_THREADS=1 and the
measured process guard enforce serial execution. Trace logs show actual Lean
`--tstack=131072 -j1` arguments. No tracked root configuration is edited.

Cache restoration preceded minimal AST/Eqns rebuilding (5.6s/0.4s). A single
178-module topological prerequisite pass reuses artifacts and prepares one module
at a time. Preparation max module12.1s and peak sampled RSS1028763648 bytes;
no module above60s. Execution checks approximately1.5s; controls approximately3s.
The exact exit/wall/RSS/module-count records, initial failures, final MCP
zero-error diagnostics, signatures and axiom inventory live in the ignored
`tests/calldata-packets-1105/RawBool/evidence/` directory and are included in the
sealed handoff. Content-addressed import artifacts require Lake's setup-aware
`lake lean` for the standalone signature file; bare env lean failure is retained.

Reproduce individual checks with run.sh:

```
bash tests/calldata-packets-1105/RawBool/run.sh execution 180 lake build +Solidity.Backend.CalldataPackets.RawBool.Execution:olean
bash tests/calldata-packets-1105/RawBool/run.sh controls 180 lake build +Solidity.Backend.CalldataPackets.RawBool.Controls:olean
bash tests/calldata-packets-1105/RawBool/run.sh signatures 180 lake lean tests/calldata-packets-1105/RawBool/Signatures.lean -- -j1 --tstack=131072
python3 tests/calldata-packets-1105/RawBool/audit.py
```

Required gate.sh touched and checkpoint are executed after committing source,
with GATE_BASE set to the checkpoint parent above. Their actual gate HEAD,
commands, outcomes and logs are sealed without changing committed source.
Final gate outcomes are in that sealed HANDOFF.md and CLOUDVM-RESULT; passing
per-file proofs alone is not checkpoint readiness. No registration/map/pin
exception is silently counted as PASS. The pre-existing local IrImport root debt
belongs to the original queue and is not edited for this item.

## Coordinator registration

- Solidity.Backend.CalldataPackets.RawBool.Execution
- Solidity.Backend.CalldataPackets.RawBool.Controls

Register generated roots, area rows and exact standard-axiom inventories through
central serialized integration. No VM ship-cache.sh is run (H41); verified
source/toolchain/checksum-bound packs are left for coordinator pull. Full native,
physical/world/resource adequacy remains outside this packet, as in RawUint.


## Axiom-pin follow-up after scheduled publication

Adopted origin/master3ad22f66d8fc6431378c22e71823436c79dede7f, preserving
all owned commits and prior seals. Review request: pin the existing axiom prints.
All64 existing prints now have exact `#guard_msgs` expectations:15 Execution,
49 Controls, including all nine private theorems. Expectations were copied from
actual saved execution-6/controls-5 output; the initial proof checks already
verified those sets. No theorem, proof, definition, premise, observation or
budget changed. Coverage tooling strips only added comments/guards and checks
byte equality with published3ad source. Only existing standard axioms appear.

Both files kernel-check with all guards:Execution1.604s/RSS869511168 bytes;
Controls3.795s/RSS895467520 bytes. Per-file MCP diagnostics0 errors each; server
stopped before further builds. A paired `copy_run` pin control passes with the
actual three axioms; its otherwise identical negative fixture omits choice and
Quot.sound and is rejected for exactly the expected guard-message mismatch
(exit1, not a passing build). Fixtures use .lean.in and setup-aware stdin so
intentional bad expectations are not production-inventory entries. Root audit
now reads the checked source expectations because successful guards consume
printed messages. The repository pin parser generates a64-entry per-lane
pins-proposal.json; shared scripts/g07-axiom-pins.json remains coordinator-owned.

Separate read-only finder and skeptic reviews found no defect in64-pin coverage,
private names, actual-message agreement or unchanged proofs; neither used
Lean/server or writes. Positive/negative controls discriminate expected sets.
Source hashes, commands, exact output, wall/RSS and review conclusions are saved
under PinFollowup/evidence and sealed after the committed-HEAD gates. Existing
RawBool source controls remain unchanged; this task adds no semantic claim.

Fresh runtime:Lean4.24.0 (797c613), Lake5.0.0-src+797c613. KeySort exits0 in0.912s:
RUNTIME_GATE_PASS. Verified Docker memory.max12884901888, memory.swap.max0,
CPU1, >=4GiB reserve, one observed Lean frontend, LEAN_NUM_THREADS1 and actual
frontend-j1; no proof budget lift. Scope-local runner/config reuses existing
caches and retains the180s/file/300s/group guards. No focused module above60s.

Required touched/checkpoint gates run at the follow-up committed HEAD, with
actual results in sealed HANDOFF.md and final CLOUDVM-RESULT. New source pins
require central inventory recording, not a trust allowance; never count pending
inventory drift as PASS. H41: leave verified cache artifacts/deltas with source,
toolchain and checksums for coordinator pull; no VM ship-cache.sh. Prior original
VT1 T01/T02 obligations, IrImport delivery and RawBool seals remain unchanged;
this follow-up does not complete the whole original assignment.
