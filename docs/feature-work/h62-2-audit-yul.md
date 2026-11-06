# H62 item 2 — audit-yul

Status: **blocked, not complete**. All four original checkpoints remain binding.
Q-REFUTATION-01 needs a scope decision: the literal requirement to witness every
premise bundle conflicts with intentional refutation theorems. No exclusion,
premise, observation or frozen interface has been changed. The persistent goal
has not been replaced or reset.

Repository: `/workspace/solidity-lean`. Assigned branch:
`codex/solidity-h62-2-20261106/audit-yul`. Frozen base:
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
The old clean `work` branch was preserved. The assigned remote ref did not
exist; fetching published master recovered the exact base, whose ancestry was
verified before creating this branch. No push, merge, PR or deployment occurred.
The final committed head and artifact hashes are recorded in the off-Git handoff.

## Checkpoint accounting

| Checkpoint | State | Evidence and outstanding obligations |
|---|---|---|
| 1 — exact signatures and owners | Partial | Conservative inventory of 1,960 mapped/imported files, 19,230 named theorems, 1,887 anonymous examples and 268 structures. Every selected blob and module map matches the base. Kernel-type/implicit-binder reconciliation, structure fields and exact producer ownership are unfinished. |
| 2 — simultaneous witnesses | Blocked | Three unchanged endpoints have joint witnesses. One full premise telescope is proved impossible. Ten further explicit-False refutations are candidates awaiting local proof certification. Remaining witnesses are unfinished. |
| 3 — meaningful success | Partial | Actual literal-assignment visitor accepts every 256-bit word and returns exactly the certificate used for source/scalar execution with arbitrary caller tails. Reject-all, arbitrary-certificate REVERT, and exact source-horizon refusal controls pass. Native failure/gas/fork and full public Source/G24/assembly closure are unfinished. |
| 4 — fidelity census | Partial | Deterministic generator, frozen-blob check, exact parser-input binding and structural acceptance. Full elaborated statement/owner/witness census and full validation remain pending. |

The inventory deliberately retains every declaration in the source superset;
it does not claim every named theorem has hypotheses. Classification of actual
elaborated telescopes remains open. It accounts for each source declaration by
one unique ID. Owner labels are area-based and explicitly provisional. Private
kernel names and section-variable inclusion require reconciliation.

The final census has 21,083 parser-confirmed source spans and 302 candidates:
268 structures, 32 examples and two named WordLogic theorems using custom
notation. Source spans are not elaborated Lean types. Parser recovery/errors
remain in evidence. No lexical signature is promoted to a witness.

## Checked additive proofs

[Success.lean](../../tests/h62/item2/audit-yul/Success.lean) supplies all data and
proof arguments together for these exact frozen endpoints:

- `Solidity.Yul.Compilation.ProducerExpressions.executes`
- `Solidity.Yul.Compilation.ProducerStatements.executes`
- `Solidity.Yul.Composition.CorrectnessInstances.Stages.publicCorrectness`

The first two use real literal/assignment certificates, emitted instructions,
locals, temporary prefix and caller stack. The last jointly supplies the
existing toy Stages, full PublicBoundary record and TablesLinked proof. It
establishes global-premise inhabitation at that toy instance, not actual
assembly admission or general per-input feasibility.

`assignment_compile_eq` connects the executable visitor to the tested output.
`assignment_total` and `assignment_success` cover every word. The generic
REVERT control quantifies every matching certificate, rather than only the
chosen fixture. Fuel-one refusal is an actual compiler boundary; it is not a
native gas statement. Scalar has no fork/gas parameter.

[ImpossiblePremises.lean](../../tests/h62/item2/audit-yul/ImpossiblePremises.lean)
packages precisely S, FailureProjection, encode, decode and roundtrip from
`Solidity.Lowering.P8.SpecExecution.no_countable_resource`. Their joint
existence is refuted through the unchanged original ResourceContractLaw1 proof
dependency and FrozenInterface. This certificate has **no axioms**. The
original mapped statement and its signature hash are unchanged. A direct
SourceRealization import was attempted and failed in its Source/Horizon
prerequisite; that validation failure remains recorded below.

Other checked proofs use only `propext`, `Classical.choice` and `Quot.sound`
where reported. Added sorry, axiom, native_decide and heartbeat overrides: zero.
No core representation or dependency changed. ParseSignatures uses Lean's
standard parser and IO initialization only; it never elaborates or certifies
a source proof through an unsafe acceptance path.

## Scope decision and owner tickets

[owner-tickets.md](../../tests/h62/item2/audit-yul/owner-tickets.md) contains one
escalation line per identified refutation and two neutral options. These are
intentional negative statements, not findings that their mathematics is wrong.
The exact all-premise witness requirement cannot hold for the certified case.
Neither option is approved or recommended on the user's behalf.

Route SourceRealization to VY5/P8a-SPEC, copied to V07 for the frozen P8a
contract. Other candidates route to their listed area producers. No relay.sh
was found; saved tickets await coordinator delivery. No original-file edit was
requested or attempted, and no absent reply is treated as permission.

## Commands and validation

Use `/workspace/.setup/tools/lean-4.24.0-linux/bin/lean` and its sibling Lake:
Lean 4.24.0, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Release;
Lake 5.0.0-src+797c613 (Lean 4.24.0). This audit follows the frozen checkout's
pin. The coordinator's official 4.35.0 archive pin is retained for the separate
migration scope; no toolchain cut-over or v4.24 master-cache restoration was done.
All five supplied coordinator-input SHA256 values passed verification.

Final proof checks use `scripts/h62/item2/audit-yul/check_serial.py`, with
`--evidence /workspace/h62-audit-yul-evidence/final-proofs`,
`--dependency-lib /workspace/h62-audit-yul-evidence/impossible/lib`, the explicit
`--lean` path above, and the three audit .lean files as targets. Exit zero.
Every child uses LEAN_NUM_THREADS=1, -j1, --tstack=131072 and -M=11000.
Writer locking, process-group monitoring, cgroup/host headroom and no-swap
checks are enforced. No systemd-run, parallel heavy Lean or heartbeat increase.

KeySort compiled from source. The actual sort-check command was the serial
runner with `--run SolkeyCheck.lean --key` and the frozen rule file at
`/workspace/.setup/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key`.
Exit zero: **parsed 377 taclets, 131 read-bearing, table covers 131; OK**.
This is an external conformance check, separate from proof certification.

The direct SourceRealization import check failed in unchanged Source/Horizon:
exit -6, std::bad_alloc, 305.158 s, peak sampled RSS 5,562,658,816 bytes, virtual
cap 12,559,687,680 bytes. This virtual-address failure does not establish a
resident-memory requirement. No cap was raised. Full affected and run-lean.sh
validation remain pending; no RUNTIME_GATE_PASS is claimed.

An earlier isolated dependency-root setup error in Source/State was corrected
by unioning fresh dependencies into one search root, then checked successfully.
The failed attempt remains in the evidence. Target symlinks are unlinked before
compilation to preserve the prior evidence library, and retry logs are unique.

Reproduce the census with:

```
python3 scripts/h62/item2/audit-yul/generate.py --lean /workspace/.setup/tools/lean-4.24.0-linux/bin/lean --output /workspace/h62-audit-yul-evidence/reproduced-complete --witnesses tests/h62/item2/audit-yul/witnesses.json
python3 scripts/h62/item2/audit-yul/acceptance.py /workspace/h62-audit-yul-evidence/reproduced-complete/census/census.json --output /workspace/h62-audit-yul-evidence/acceptance
```

Bulk census/parser/uncovered outputs stay off Git under
`/workspace/h62-audit-yul-evidence`. Deterministic generators and the small
witness registry are in Git. Parser diagnostics are JSON fields, and all
1,960 files must be present exactly once. A stale input, duplicate/missing
parser record or changed frozen blob is rejected.

No performance refactor occurred. The 51-file fresh baseline and additive
checks have individual command/time records. Successful additive proof checks
were 0.806 s for Success and 0.404 s for ImpossiblePremises. No comparable
passing before/after full build exists; timing delta is unavailable, not zero.
The failed original import cannot be used as an acceptance or timing pass.

Structural acceptance and byte-for-byte census reproduction passed. Layer,
generated-root, fragment and document-path checks exited zero; the document
check reports 115 resolving ambiguous references. Current ParseSignatures was
rechecked through the full generator after its final diagnostic-format change.

## Independent reviews and handoff

Independent read-only finder and skeptic reviews used no Lean server and made
no edits. They found and verified fixes for truncated let signatures, mutual
namespace handling, frozen/source-parser provenance, resource reserve guards,
dependency-output symlink overwrites and retry logging. Final reviews confirmed
all three complete joint witnesses and the exact impossibility telescope, with
no statement weakening. Their reports and remaining limits are saved in evidence.
Final reproduction also exposed merged-stream corruption of eight parser
records; diagnostics now stay inside each JSON record and completeness is checked.

Outstanding typed blockers: Q-REFUTATION-01 scope decision; ten uncertified
refutations; remaining exact signatures/types/owners and joint witnesses;
native failure/gas/fork and full public totality; direct-import/final validation;
owner-ticket delivery. No H55 work was duplicated. Registration information is
supplied under tests; no generated root, central map or axiom pin was edited.
Resume the same VM, branch, frozen assignment and existing goal after the scope
decision. Do not create a replacement goal or treat this checkpoint as completion.
