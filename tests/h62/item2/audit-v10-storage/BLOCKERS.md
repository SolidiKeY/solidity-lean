# Frozen v10-storage audit blockers

This is an owner-ticket and resumption queue, not a proof certificate.
Base: c6f550e281a7e5affa9a99bc2cdaed556dec00e4.
The official v4.35.0 archive matches coordinator toolchain-pin.json SHA256
7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d.
No files listed below were edited. The coordinator retrieves this committed ticket;
no relay.sh is available in the checkout, so no direct owner delivery is claimed.

| ID | Exact file and evidence | Migration owner | Required disposition |
|---|---|---|---|
| B-MIG-SYNTAX | Solidity/Syntax/Raw.lean: String.Slice/String mismatches, unavailable String.dropRight, endsWith function mismatch; dependency log | solidity-h62-6-20261106/migrate-syntax | Supply compatible owned migration commit/overlay; keep original signature audit frozen |
| B-MIG-HASH | Solidity/Hash/CollisionBound.lean:407 unsolved goal; :660/:680 omega failures; :950 onward guard-message mismatches | solidity-h62-6-20261106/migrate-hash | Supply compatible owned proof migration commit/overlay; no premise repair authorized here |
| B-MIG-SOURCE | Solidity/Source/Ctor.lean:641 simp error; :715 dependent elimination errors | solidity-h62-6-20261106/migrate-source | Supply compatible owned migration commit/overlay |

Reproduce from the repository root:

```sh
bash scripts/h62/item2/audit-v10-storage/validate.sh --evidence /workspace/audit-v10-storage-evidence/reproduce dependencies
```

The fixed TOML build directory is /workspace/audit-v10-storage-evidence/build-v4.35.0;
--evidence selects logs/cache, not a new build tree. The wrapper serializes writers.
Dependency reproduction exited 1, elapsed 54.7867672 seconds, observed peak group RSS
1608388608 bytes, no resource stop. This is a failed gate, not a slowdown comparison.

## Resume after owner resolution

1. Preserve the assigned branch and exact frozen inputs. Do not cherry-pick repairs
   to owned originals without coordinator authorization; review overlay ancestry.
2. After explicit coordinator hold release, re-run pinned version/KeySort prerequisite
   and affected dependencies. Then use
   per-file MCP diagnostics or repository run-lean policy for additive proof modules.
3. Obtain elaborated declaration names/types and classify every interface statement:
   global premise structures versus per-input feasibility, retaining all binders.
   The conservative source census includes controls/private helpers; none may be
   silently reclassified as a proved interface witness.
4. First witness candidates: LoopLaws.turn_step (same rc/rb/machine/result/flag must
   satisfy nonzero, condition and step together); LoopLaws.turn_exit (actual zero
   condition); LoopLaws.run_single_loop (actual terminating run, not merely a separate
   inhabited structure). SourceWordRead.read_total needs one shared E/Γ/frame/path/
   locals/state tuple and ordinary. SourceWordRead.complete adds value/machine/slot
   and must discharge ordinary/present/coherent together on its single shared tuple.
   Existing controls are possible inputs, not replacements for new simultaneous proofs.
5. Prove supported-program success/totality; negative reject-all/always-revert controls
   must fail the same success contract. Preserve observable failure and distinguish
   Source fuel from gas and EVM fork boundaries. Evm.Machine documents no gas model;
   its symbolic-slot success cannot establish bytecode/gas/fork correctness.
6. Complete all remaining statement witnesses, verification/census, finder/skeptic
   reviews, acceptance/full gates, proof budgets, and comparable timing checks.
   Emit one exact theorem-specific ESCALATE line for any established weakened/vacuous
   statement, with evidence and repair options; none has been established by this
   preliminary lexical census. Do not infer absence of vacuity from that fact.

All 3281 conservative declaration rows remain uncovered. No new Lean proof, axiom,
sorry, native_decide, heartbeat override, root registration or interface edit exists.

B-TIMING-REPEAT: final repeated KeySort 1.814585664 s versus prior guarded
1.617805099 s (+12.163%). Further Lean runs stopped under the threshold rule.
This is not an attribution to a proof change (there is none); proper comparable
before/after timing remains required after migration blockers are resolved.

## H70 routed disposition (2026-11-06 worker continuation)

The coordinator reports accepted relays for migrate-hash, migrate-root-gate,
migrate-source and migrate-syntax. This records router acknowledgment, not a fetched
repair or authority to edit their files. Some VM reads failed in the router receipt;
no unavailable file is claimed retrieved or forwarded here. relay.sh is host-only;
no installation request is needed on this VM.

**HOLD: no further Lean runs**, including the reproduction command above, until the
coordinator resolves Syntax/Raw, Hash/CollisionBound, Source/Ctor and the repeated
KeySort timing sample. B-TIMING-REPEAT disposition owner:
solidity-h62-6-20261106/migrate-root-gate. Original write scope remains unchanged.

H70 requested source classification is saved in
[candidate-bundles.json](candidate-bundles.json). Five bundles retain all binders,
dependent data and joint per-input obligations. They are not verified witnesses and
do not promote any census row. Bulk exact frozen-signature attachments are generated
by scripts/h62/item2/audit-v10-storage/classify_candidates.py outside Git.

Coordinator requests remain attached to these exact original-file paths:
/workspace/solidity-lean/Solidity/Syntax/Raw.lean,
/workspace/solidity-lean/Solidity/Hash/CollisionBound.lean,
/workspace/solidity-lean/Solidity/Source/Ctor.lean.
Timing evidence remains /workspace/audit-v10-storage-handoff/evidence/reproduce/keysort.json
and /workspace/audit-v10-storage-handoff/evidence/final-prerequisite/keysort.json.
No missing VM file or unstated repair is needed to review the source classification.

## H70 requester continuation: full static triage

Requester disposition at head 2d53437157aeb2385aeaaab7b7bb891e92566058 names
migrate-syntax Raw, migrate-hash CollisionBound and migrate-backend producer repairs
as waits. B-MIG-BACKEND is a coordinator-directed producer dependency, not a newly
observed Lean failure. Relevant frozen interface inspection:
[producer-field-classification.md](producer-field-classification.md), original path
/workspace/solidity-lean/Solidity/Backend/StorageOps/ProducerInterface.lean.
The exact backend repair diff/file list has not been supplied. This grants no edit
permission. Earlier Source/Ctor and KeySort holds have no explicit release; no Lean
runs or new measurements occurred. relay.sh remains host-only.

surface_classification.py now retains all 3281 rows in one static ledger. It records
syntax and markers only, without treating any row as premise-free or witnessed.
Thirteen selected declarations have manual joint-input classifications, including
eight address/read/write/copy contracts; their witness count remains zero.

## H70 Hash partial overlay and next semantic batch

Owner message provides a reviewed PARTIAL Hash overlay, not completed migration.
[Static overlay review](hash-overlay-review.md) records exact checksum/context/header
checks, no application and no Lean validation. Full migration and Syntax.Raw remain
pending. The current router lists no ticket destinations or pending current-owner
deliveries; this worker creates no outgoing relay request from that receipt.
Current requested waits: migrate-syntax Raw, migrate-hash CollisionBound and
migrate-source Ctor. Earlier timing/backend holds have no explicit release here.

Manual source planning now covers 25 statements in four complete selected modules:
LoopLaws: 3, SourceWordRead: 2, TargetOperations: 14, LayoutAccess: 6. This is not witness
coverage: all 3281 rows remain uncovered. SC/LS plan aliases in candidate-bundles.json
preserve nonempty query/access/family cases, universal hash range and every correlated
input. No original proof, premise, interface or budget is changed.
