# H62/H63 Precompiles migration — authorized patch, root dependency blocked

Batch `solidity-h62-6-20261106`, lane `migrate-precompiles`, repository
`/workspace/solidity-lean`, branch
`codex/solidity-h62-6-20261106/migrate-precompiles`, base
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. Persistent goal unfinished.

Current merge-review repair restores the original `msmGas` and entire `Field.lean`;
the earlier definition-body overlay is historical, not the current proposal.
Targeted Field/BLS diagnostics pass8/8; full acceptance remains pending.

## Current checkpoint state

1. **Done:** pinned-base census and original clean v4.24 baseline.
2. **Blocked on root dependency:** authorized local directory changes implemented
   and validated, but the imported recovery producer adds a frozen-disallowed
   axiom on v4.35. No source outside this lane was edited.
3. **Blocked:** all16 modules pass on old toolchain; new compilation fails only
   the original Osaka `run_eq_none_iff` axiom assertion. Final passing new-build
   timing and full affected/final validation remain outstanding.
4. **Partial:** reviewable production patch, exact source contract, hashes,
   dependency request, tests and evidence are exported. Final root gate pending.

The coordinator clarified that VMs never receive host `relay.sh`: this lane is
its directory's registered writer and must apply statement-preserving migration
itself. Earlier OWNER-BLS/OWNER-POINT clearance questions are resolved by that
explicit instruction, not by silence. `decide +kernel` is allowed under H64.
The coordinator relays the following changes to the live owner at cut-over.

## Historical overlay changes (superseded by the revert below)

- `Solidity/Precompiles/Bls12381.lean`: both 128-entry discount-length proofs
  use kernel-checked `decide +kernel` instead of depth-failing `rfl`.
  New **private** `msmLookup` uses structural List/Nat `casesOn`, decreasing
  the table tail and preserving short-circuit traversal. Private
  `msmLookup_eq_getD` proves agreement for every table/index/fallback. `msmGas`
  uses that helper, and `msmGas_succ` rewrites by its agreement theorem after
  unfolding. All public statements, tables and cases remain unchanged.
- `Solidity/Precompiles/Field.lean`: `finFieldOps.toBEq` is explicit constructive
  `fun a b => decide (a = b)`, avoiding the newly inferred classical order
  package. The universal `FiniteDecision` fixture proves agreement with the
  standard comparison on both versions. The computational body is axiom-free.
- `Solidity/Precompiles/PointEval.lean`: the impossible `none` branch of
  `bind_check_eq_some` uses `cases h` instead of the incompatible
  `Option.noConfusion h`. Its exact polymorphic type is unchanged.
- `Solidity/Precompiles/Osaka.lean`: the stipend proof uses explicit
  `Nat.decLt`/`of_decide_eq_true`. Its original empty-axiom assertion now passes
  on v4.35. All axiom assertion comments and all original guards are unchanged.

Four producer files changed; seven remain byte-identical. There are two new
private core helper declarations; no new public core interfaces or area modules.
No frozen statement/premise/exclusion, proof budget, generated root, module map,
axiom pin or tracked toolchain was changed. No source sorry/new axiom/native_decide
or kernel-skip option was introduced. No push, merge, PR or freeze announcement.

## Toolchain, provenance and resource controls

Initial clean checkout `work` was `6cf853aea0417155aca29ddb91f1767d3f3a3cc4`.
Fetched master and exact base, verified base ancestry against remote master,
created the assigned branch without reset/discard. Setup remote master was
`821e3e8f4c7a5ac3a51dc5cba8be813bb173e310`.
AGENTS, Gate G0, area docs/history, verification and resource policies were read.
No Lean MCP is exposed; bounded per-file CLI diagnostics are used. No new or
replacement persistent goal was created.

The official coordinator-pinned `lean-4.35.0-linux.tar.zst` has SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Archive checksum matches `/workspace/h62-coordinator-inputs/toolchain-pin.json`;
all provided coordinator inputs were independently hash-verified. The private
installation is `/workspace/h62-migrate-precompiles/toolchains/lean-4.35.0-linux`.
Actual Lean 4.35.0 release commit:
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake `5.0.0-src+eb6cafb`.
Old Lean 4.24.0 release commit:
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; Lake `5.0.0-src+797c613`.
Tracked lean-toolchain remains v4.24; root migration lane owns its final edit.

VM: 16 GiB memory cgroup, CPU quota4 over CPUs0–4, no system swap. Each job:
12 GiB hard address-space cap, 4 GiB available physical/cgroup reserve guard,
LEAN_NUM_THREADS=1, explicit -j1, --tstack=131072, one heavy job at a time.
Writer lock is inherited by the Lean process. Exception cleanup and parent-death
lock behavior have executable controls. No systemd-run or other-worker kills.
No v4.24/master Lake cache was restored. Clean runs use absent output directories
and empty private olean roots; OS page cache was not explicitly flushed.
Per-process RSS is measured by wait4, not cumulative rusage.

## Commands and evidence

Evidence directory `/workspace/h62-migrate-precompiles/evidence/` contains exact
commands, versions, expected/completed modules, exits, wall/RSS and logs in each
run's `summary.json`. Use the in-scope `bounded-build.py` with `--toolchain` and
fresh `--out`; fixture reuse has an explicit diagnostic-only --import-products
label and is never treated as a clean benchmark.

| Command / run | Result | Decisive evidence |
|---|---|---|
| census.py --verify (original base) | pass | census.json:11 files,237 declaration lines,152 guards,3 guard_msgs |
| census.py --verify-migration (current) | pass | authorized-census.json; all source bytes match exact authorized transformations |
| acceptance.py (current) | pass | authorized-acceptance.log: all11 source mutation controls, missing/extra/cycle inventory, declarations/guards, failed/partial/missing-output/cache and parent-death lock controls |
| bounded KeySort old/new | pass | old-keysort-final and new-keysort-final: exactly Solidity.KeySort 1/1, actual versions |
| original old clean | pass | old-measured:16/16,46.390716473s,375120KiB peak |
| final migrated old clean | pass | authorized-old-clean-2:16/16,42.248164142s,389620KiB peak |
| final migrated new clean | fail | authorized-new-final:15/16 pass; sole Osaka line198 assertion failure;33.557409609s,601608KiB peak |
| fresh public signature diagnostic | pass for signatures only | authorized-interface-comparison.json:221 names/types match,6 axiom deltas remain |
| direct root axiom diagnostic | pass as diagnostic | root-trace-old/new print recover, recoverPoint and ecrecover |
| all isolated proof fixtures old/new | pass | kernel lengths, bind check, explicit finite decision, structural recursor agreement and stipend obligations; individual summaries/logs |
| ./run-lean.sh / final accepted comparison | pending | root dependency must first satisfy unchanged frozen directory assertions |

The old migrated tree has no measured checking slowdown against old baseline;
its peak RSS increased3.87%. **A failed new build is not an eligible speedup or
final time comparison.** New peak is60.38% above original old peak and is explicitly
escalated to migration root/gate. No resource regression is silently accepted.
No RUNTIME_GATE_PASS or whole-goal completion is claimed. Stop/escalate any
accepted >10% checking slowdown when the complete comparable gate becomes possible.

Initial off-git pilots are excluded from final gates. A mislabeled old-keysort
run omitted the selection flag; final KeySort runs correct it. Missing time
binary, duplicate lock, incomplete status and census/RSS bugs were repaired and
controlled. A direct internal lookup remained propext-dependent and broke a
rewrite; a List.rec fixture could not compile; both were replaced. A fold
prototype passed but was not selected because structural short-circuiting better
preserves traversal cost. An explicit Nat.beq field prototype broke an old
proof's definitional shape; constructive decide restored old compatibility
without editing Bn254. Rejected pilots remain off git, with source/evidence
provenance where applicable, and never count as passing final builds.

## Frozen interfaces and remaining root request

`frozen-sources.json` preserves original whole-source hashes; `migration-sources.json`
records current/base hashes and exact contract agreement. `contract.py` permits
only the listed transformations, including private helper/proof additions;
all other bytes must equal base. It is an exact source guard, not a kernel ABI
oracle. The generated inspection hashes normalized printed types, not kernel
Expr objects. It covers221 original source-named declarations outside Osaka;
private/generated/anonymous items are covered by source hashes and compiled
module checks. Osaka's11 original statement texts remain unchanged; it elaborates
but its frozen axiom assertion fails, so full acceptance is not claimed.

Fresh axiom deltas fell69→6: ecrecover/ecrecover_isSome gain Choice+Quot.sound;
ofHex/setupG2Compressed gain standard Choice+Quot.sound+propext; Fp12.add/sub gain
standard Quot.sound. All deltas are reported for root classification, not repinned.
The actual remaining required assertion is:
`Osaka.run_eq_none_iff`: expected [propext,Quot.sound], actual
[propext,Classical.choice,Quot.sound]. Its original stipend/gas assertions pass.

**ROOT-AXIOMS**: migrate-root-gate owns `Solidity/Secp256k1.lean`. Direct diagnostics
confirm `Secp256k1.recover` changes from [propext] and `recoverPoint`
from [] to [propext,Classical.choice,Quot.sound] under new inferred library instances.
Please migrate that producer preserving its exact API/semantics and original
axiom expectations, then provide the owner patch/dependency for bounded retest.
This lane will not edit or duplicate that approved external implementation,
weaken run_eq_none_iff, or update its frozen assertion/pins.

Direct dependencies: Roadmap.Evm, Hashes, Secp256k1; closure also Keccak and
RevertBytes. All five compile unchanged on new toolchain; compilation alone does
not certify identical axiom dependencies. Roadmap/root owners retain ownership.
Typed requests in owner-requests.json mark directory ownership resolved and retain
ROOT-AXIOMS, RSS-REGRESSION and FULL-GATE blockers. No human scope question remains.

## Proof boundaries, independent reviews and handoff

Structural lookup agreement covers all tables, all indices and all fallbacks;
finite comparison agreement covers every modulus/value pair. Their computational
bodies are axiom-free on both toolchains. Agreement proofs use only the reported
standard axiom sets; they are not inserted as axioms or new premises. The152
original executable guards are preserved. They are finite computation vectors,
not proofs of field/group laws or external-EVM equivalence.

Independent finder and skeptic used read-only review, neither Lean/server nor
edits. They caught and fixed earlier census, partial-PASS, RSS, inherited-lock,
old definitional-shape and lookup rewrite issues. Final authorized review evidence
is separate from the earlier blocked-handoff review; no review waives a gate.

Export current committed original patch, verified bundle, handoff and checksum
manifest from this VM/branch. Historical manifests and all non-Lean metadata are archived off git under H44;
`tests/h62/item6/migrate-precompiles/bulk.sha256` authenticates the complete archive. Coordinator owns
fresh-thread continuation; do not create/reset a goal or replacement thread.
After root producer repair: apply only an authorized dependency input, rerun clean
comparable new build and full affected/run-lean.sh validation with pinned toolchain,
escalate resource regressions, obtain fresh reviews and deliver final complete
handoff. The persistent goal must remain unfinished until every required gate passes.

## H70 relay disposition

H70 explicitly routes this lane to **wait** for migrate-root-gate's
`Solidity/Secp256k1.lean` recovery axiom disposition and recorded RSS review.
The four-file overlay at `d393a60b76120dfab477e62c569f11cf34cdcfcb` remains partial;
no new producer-source edits, Lean checks, budget changes or acceptance occurred.

For audit-precompiles at `5fcec7dca5ab0d6d321eaf29ca176045b5c38e0c`,
`DEP-BLS-435` has a producer fix available in that committed overlay: both
discount-length statements use the already verified kernel proof. The recorded
official-v4.35 build compiled BLS with exit0; the current BLS bytes match that
compiled committed source. **Consumer retest remains pending**, and the BLS
module pass does not establish a passing Osaka/frozen consumer import closure.
Machine-readable evidence and exact source hash are in
`tests/h62/item6/migrate-precompiles/h70-relay-disposition.json`.

`OBL-SUCCESS` is the G43/V14 owner's separate actual-compiler success theorem;
this lane does not change its frozen obligation, supply premises or claim that
the audit demonstrated failure of an actual compiler theorem. Raw/Bridge
prerequisites remain with their named owners. The supplied router receipt path
is host-only and absent locally; H70 reports one read failure. Missing receipt
bytes were not reconstructed, and no root disposition was inferred from them.
Coordinator retrieves this receipt; no new relay or edit permission is inferred.

H70 requester update `13ae4273bad4123baea9347dfa724ded432dfd57`: exact BLS source,
full BLS overlay patch, and minimal discount-proof patch are published with hashes
in `tests/h62/item6/migrate-precompiles/h70-bls-delivery.json`. Both independent
read-only reviews and pinned-base apply checks pass; consumer retest/full gates
remain pending. Reported host handoff hash/size remain locally unverified.

H82 explicit retirement: implementation STOPPED, handoff_to
`solidity-h62-6-20261106/migrate-root-gate`. Complete visible original assignment,
objective, original queues, exact scope registry, open-work ledger and pause-tool
limitation are committed under `tests/h62/item6/migrate-precompiles/retirement/`.
No H71 push permission is available; no push performed. Goal is not complete;
exposed tool cannot set PAUSED. No automatic implementation continuation authorized.

## H44 packaging split

All formerly tracked non-Lean metadata, handoff JSON/text, original assignment/scope
files and long per-file evidence manifests are preserved in the authenticated
archive listed by `tests/h62/item6/migrate-precompiles/bulk.sha256`. The archive
contains `tracked/<original repository path>` and actual `evidence/<relative path>`
bytes plus `referenced/<absolute path without leading slash>` for additional
manifest payloads; earlier metadata paths mentioned above refer to that archive, not current
tracked files. The deterministic generator is `archive-bulk.py` in this lane’s
scripts directory, invoked with metadata revision
`3b7be8c4a35d056444b278c589acb88821fe83ca` and the preserved VM evidence directory.
All Lean, existing scripts, theorems, gates and budgets are unchanged by the split.
The pre-existing master merge was preserved; no reset/history rewrite or push.
Retirement remains in force; this is packaging only, not implementation resumption.

Independent read-only finder and skeptic verified all 500 archive members and
all referenced hashes: 22 removed Git metadata files, 469 evidence files and nine
additional referenced artifacts. Both found no proof, gate, budget or existing
script change. No Lean rerun was necessary or performed for this packaging split.

## Merge review correction: restore dependent definitions

The coordinator's review of head `713f75a1430906476ffd7b87e5673aba038ebd4e`
identified definition-body changes requiring owner agreement/versioned interfaces.
The revert option is applied: `msmGas` again uses exactly the original table.getD
expression; `finFieldOps` again inherits its original equality implementation.
The now-unnecessary msmGas_succ proof normalization is removed. Private structural
lookup and agreement lemma remain additive, disconnected from the existing gas
definition. Kernel length proofs and other proof-only fixes remain. No original
statement, axiom assertion, gate, budget or exclusion was weakened. Earlier
validation/source hashes describe historical overlays and are not current gate
acceptance; additional axiom failures may return with the restored definitions.
No owner question remains for those two body changes because both were reverted.
This is only the requested merge-review repair; retirement remains in force.

Revert diagnostics: `bounded-build.py --fixture tests/h62/item6/migrate-precompiles/ReviewRevert.lean`
with official4.35 and fresh output, archived fixture imports Field/BLS;8/8 pass.
Independent finder/skeptic exact-original and contract checks pass; H44 evidence
is off Git and authenticated by `tests/h62/item6/migrate-precompiles/review-revert.sha256`.
