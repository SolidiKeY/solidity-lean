# H62 item 2 — v08-adapters audit (unfinished)

Owner: `solidity-h62-2-20261106/audit-v08-adapters`.
Repository: `/workspace/solidity-lean`.
Branch: `codex/solidity-h62-2-20261106/audit-v08-adapters`.
Frozen base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Original rendered prompt SHA256: `5cacd891e4eb0f7c11882c5370c149cf789d69a846d5ca83b10b7c6fd650a2b6`.
Persistent goal retained; get_goal is not exposed. No replacement goal created.

## Checkpoint status

| Checkpoint | Status | Evidence / remaining obligation |
|---|---|---|
| 1. Frozen signatures and owners | partial | Conservative 881-file, 7,949-candidate source inventory; exact blobs checked against base; all owners await confirmation; inherited variables and 26 ambiguous signatures await elaboration. |
| 2. Simultaneous hypotheses | partial | Five original resource-law targets have reviewed kernel-checked joint witnesses; 7,944 candidates remain uncovered in acceptance output. Candidate count includes controls and premise-free declarations; exact public-interface classification is pending. |
| 3. Compiler success and negative controls | pending | No supported-program compiler totality, reject-all/always-revert compiler controls, or executable gas/fork boundary suite added. Resource schedules are not execution evidence. |
| 4. Witness/fidelity verification | partial | Five witness targets verified and linked to frozen source signatures; exact full elaborated census and all owners remain pending. No full-audit acceptance or runtime gate pass. |

This is a reviewed backfill checkpoint and scope-blocker handoff, not completion
of the four-checkpoint queue or its 8–10h useful-work budget.

## Frozen inputs and scope

Initial clean checkout was `work` at `6cf853aea0417155aca29ddb91f1767d3f3a3cc4`.
Fetched origin/master and exact base; base is an ancestor of fetched master
`821e3e8f4` (full observed SHA is saved in provenance evidence). Created the
assigned branch at the exact base without resetting or discarding work.
No existing original, generated root, module-map fragment, pin, toolchain file
or central registration was edited. New Lean helpers remain under the exclusive
tests directory. No integration registration is requested until the audit is complete.
No push, merge, PR, pre-gate, deployment or systemd-run occurred.

The coordinator-input SHA256 manifest was independently checked: all five inputs
match. Official Lean archive SHA256 is
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Lean: `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release.
Lake: `5.0.0-src+eb6cafb`, Lean `4.35.0`.
No v4.24 artifact cache is used. Original tracked toolchain remains untouched.

## Inventory and joint witnesses

`census.py` expands explicit braces, same-row directory shorthand and contextual
control globs, retains every lexical theorem candidate, deduplicates by file,
line and local name, and verifies every scanned source blob against the frozen
commit. The output includes original signature text and its SHA256, module hash,
private/public visibility candidate, unresolved status and owner confirmation
status. Names are candidates, not verified Lean fully qualified names. Type-level
match branches remain explicitly unsupported rather than truncated. The full
module hash retains the surrounding variable/include/omit source context; that
context still requires elaboration. No lexical flag establishes inhabitation.

`witness-ledger.json` carries exact frozen source signatures and links:

| Original target (prefix `Solidity.Source.FailureResources`) | Joint witness |
|---|---|
| `Bound.le_trans` | `trans_joint`: one a/b/c triple with BOTH inequalities |
| `Bound.withFailures_mono` | `replacement_joint`: same r/s, replacement p, and inequality |
| `dropped_not_noFail` | `refusal_joint`: p/i with the exact dropped request |
| `frame_not_noFail` | `refusal_joint`: SAME p/k/cut with the exact frame failure |
| `Bound.not_le_of_points_ne` | `schedule_change_joint`: r/s with distinct schedules |

These targets have per-input feasibility hypotheses and no inhabited global
producer premise. Witnesses use nonzero horizon, balance, request/frame indices
and failure cut; `exact_refusals` consumes unchanged refusal laws on that witness.
All five new helper theorems have guarded empty axiom reports. No new sorry,
axiom, native_decide, trust shortcut or raised heartbeat budget is present.
The remaining resource declarations include premise-free laws and an intentional
diagonal refutation; none is silently counted as a witnessed interface.

## Typed blockers and owner tickets (prepared, dispatch pending)

No `relay.sh` exists in this checkout or available workspace, so no exact-file
owner request was transmitted. Coordinator retrieval of this committed handoff
must dispatch these tickets; absent replies grant no write permission.

**MIG-STRING-001 — external-owner migration dependency.** The unchanged private
`_private.Solidity.SortCheck.Parser.0.Solidity.KeyTacletParser.headerName?`
fails at `Solidity/SortCheck/Parser.lean:76:13` because String.trim was removed.
Owner: area producer / coordinator migration lane (not this exclusive audit scope).
KeySort itself compiles, but checker compilation/conformance and final gates do not.

ESCALATE: _private.Solidity.SortCheck.Parser.0.Solidity.KeyTacletParser.headerName? migration — official pinned v4.35.0 rejects String.trim at Parser.lean:76:13; options: owner supplies a semantics-preserving reviewed migration overlay, or human authorizes a precise isolated edit exception for this dependency. No out-of-scope repair made.

**PREMISE-P8-001 — missing producer, not an arbitrary-S impossibility proof.**
`CreationPremises.Inputs.admission` and `LibraryPremises.Inputs.admission` require
`DeclarationGraphAdmission.Producer.base.failures : P8a.FailureProjection S`.
`ResourceContractLaw1.nat_encodable_resource_impossible` rules out that projection
ONLY when explicit encode/decode/roundtrip data for `S.lang.Res` are available.
The arbitrary-S frozen Inputs do not supply them. Their docstrings' assertion of
uninhabitedness is therefore not a generic proof. No intended concrete producer
or full joint witness has been supplied. Owners: CR/P8a, VY5 resource (H16), V08,
and V17/V07 constructor or G42.04/P4 library producers; H55-G49 coordination
retained, no duplicate H55 work.
Affected CreationPremises statements: meaning_origin, actual_source, reached_body,
creation, installed, try_success, runtime_success, settlement_failure, try_failure.
Affected LibraryPremises statements: source_caller, source_library,
no_second_payment, delegated, library_account_preserved, source_roles_separate.
Options: producer owners supply the full intended concrete joint witness, or
owners submit a frozen-contract repair proposal while retaining the blocker.
No consumer theorem is marked mathematically vacuous solely from the docstring.

**AUD-REFUTATION-001 — audit classification of intentional refutations.**
The conservative map census includes a theorem whose hypotheses prove False.
A simultaneous witness for its extract/replace/rightInverse hypotheses would
contradict the unchanged theorem itself. Its status remains uncovered pending
explicit treatment in the interface census; this is not silently excluded.

ESCALATE: Solidity.Source.FailureResources.no_horizon_retraction — frozen extract/replace/rightInverse hypotheses imply False by its diagonal proof; no simultaneous witness can exist. Options: retain the statement and this audit blocker while the owner explains its intended interface boundary, or obtain an explicit human census-classification decision for intentional refutation lemmas without changing the theorem. No exclusion or premise change assumed.

## Commands, gates and measurements

All heavy Lean work is serial under the writer lock, LEAN_NUM_THREADS=1,
explicit -j1, one CPU, a hard per-child 12 GiB ADDRESS-SPACE limit, host swap zero,
and a monitored 4 GiB available-memory reserve. This is not an aggregate RSS
cgroup claim. Per-file wall budget is 600s. No Lean MCP is available.

Evidence root: `/workspace/h62-audit-v08-adapters-evidence`.

| Command / operation | Outcome | Decisive evidence |
|---|---|---|
| `git fetch origin master c6f550e281a7e5affa9a99bc2cdaed556dec00e4`; merge-base; branch creation | pass | `provenance.json` |
| Coordinator manifest hashes; official archive SHA256; actual Lean/Lake versions | pass | `provenance.json`, `prerequisite-435/versions.txt` |
| `bounded_prerequisite.py --repo /workspace/solidity-lean --evidence .../prerequisite-435 --toolchain .../toolchain/lean-4.35.0-linux --key /workspace/.setup/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key` | fail | KeySort exit0 1.204s; AST exit0 5.613s; annotations exit0 1.204s; Parser exit1 3.809s. Checker never executed. Full commands in results.json. |
| Same runner with `--audit-module tests/h62/item2/audit-v08-adapters/FailureResourceWitnesses.lean --evidence .../failure-resource-final` | pass, limited | Four-module fresh closure, all exits0; five guarded empty axiom reports; source-sha256.json stable. |
| `census.py --repo /workspace/solidity-lean --out .../census`; repeat | pass, lexical only | 881 files, 7,949 candidates, 26 unsupported signatures; byte-identical regeneration, determinism.log |
| `check_census.py .../census/census.json` | pass | CENSUS_REGRESSION_PASS; equation/type-match/comment/character/name/path regressions |
| `accept_witnesses.py --repo ... --census .../census/census.json --run .../failure-resource-final --out .../witness-acceptance.json` | pass, backfill only | five witnessed targets; 7,944 uncovered candidates; owners/fidelity/totality explicitly pending |
| Acceptance with a failed Lean record substituted | expected rejection | acceptance-negative/negative-control.log; no accepted output emitted |
| Full affected run-lean.sh, checker acceptance, final runtime gate | pending/blocked | Parser migration outside scope; no RUNTIME_GATE_PASS |
| Valid paired before/after checking benchmark | pending | No speed refactor made; isolated timings are observations, not a controlled comparison or >10% performance gate pass. Stop rule retained. |

The initial fixture compile failed due to a mistaken constructor name
RequestFailure.runs; it was corrected to frozen TxFate.runs. Failed evidence is
retained separately and never accepted. Successful fixed and final runs are
separate. The final proof outputs do not rely on the failed run's generated
sorryAx placeholders.

## Independent milestone reviews

Finder and skeptic independently reviewed read-only without Lean/server use.
Fixed confirmed findings: equation proofs swallowed following definitions;
missing frozen-source verification; private-name collisions not labelled;
quoted-name/character handling; type match branches misidentified as equation
proofs; overbroad interpretation of Nat-encoding obstruction. Finder confirmed
all five exact premise mappings. Skeptic confirmed no blocking issue for this
partial resource backfill, with full-audit limitations retained. Reviews are
saved in `reviews.json`, including final acceptance-tool review. Proof-to-target
correspondence is independently reviewed; the acceptance script reconciles
source/signature provenance and saved kernel-run evidence, and does not itself
elaborate statement equivalence.

## Continuation and handoff

This is the fresh-thread handoff after setup, census/review repair, bounded
prerequisite diagnosis, and resource-witness backfill. The original persistent
goal remains unfinished; any blocked transition is not completion. Coordinator
must resume this same VM/goal/branch, never create a replacement goal.

Next: dispatch owner tickets and resolve migration/classification; elaborate all
candidate names/types/variables and confirm owners; build every required full
joint witness; implement supported-program compiler success/totality plus
reject-all/always-revert controls and real gas/fork/failure observations; finish
full affected gates and controlled timings; rerun independent reviews per
milestone. Never register helper modules centrally without owner approval.

Original patch, bundle, absolute handoff copy and SHA256 manifest are exported
off Git. Their full paths and hashes, full committed head and base are in
`export.json`. Bulk census, logs, toolchain archive and proof artifacts remain
off Git, regenerated by committed scripts. No empty marker commit is required.
