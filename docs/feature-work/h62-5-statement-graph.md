# H62 item 5: statement graph

Owner: `solidity-h62-5-20261106/statement-graph`. Base:
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. Branch:
`codex/solidity-h62-5-20261106/statement-graph`.

This is an isolated implementation checkpoint, not completion of the frozen
assignment. Production G49/G50 declaration selection, census, typed premise
witness/discharge mapping, owner coordination and the final full gate remain
outstanding. No production progress count is claimed.

## Implemented contract

The optional exporter under `tests/h62/item5/statement-graph/` imports Lean;
no core module imports it. `h62_statement`, `h62_premise` and `h62_helper` are
persistent Lean attributes. `#h62_tag "statement" Imported.declaration` adds
read-only overlay metadata to an imported declaration without editing its
producer. Imported overlays with conflicting classifications reject at export.
`#h62_export "filename.json" [declarations]` resolves names in Lean and reads
`ConstantInfo.type`, telescope binders, structure constructor field types and
actual projection declarations. It verifies reference existence in the elaborated
environment, exports type expressions with closed local contexts, fixes printer
options, and records transitive axioms. `H62_GRAPH_OUTPUT_DIR` must identify an
off-git output directory. Export selection is explicit; it is not a whole-repository
census. No prose/regular-expression reconstruction supplies statement edges.

The Python catalog assigns stable IDs, areas, node kinds, owners and binder roles.
Every exported declaration must appear, and every typed binder must be classified
explicitly. Ordinary data parameters need an audited reason; propositions,
structure fields and cataloged premise interfaces cannot be classified as ordinary
data. Every premise needs a separate producer owner. In production, each node and
premise owner references an item in the supplied ownership snapshot and must match
its owner. The snapshot hash is included in the graph. Fixtures are explicitly
marked and cannot claim production ownership.

`dependencies` come from elaborated types, including structure field types.
`proofDependencies` come from declaration bodies and never control readiness;
`proofHelpers` is their helper-classified subset. Dead selections, omitted tagged
dependencies, conflicting tags, cycles, missing owners and unsupported completion
claims reject. Base/tree IDs, export/catalog/ownership hashes and the graph digest
bind output provenance. The acceptance runner requires clean committed sources
and verifies that HEAD and source cleanliness remain unchanged.

Status definitions are disjoint: `done` requires an explicitly completed checked
theorem, allowed axiom evidence, no open named premises and completed dependencies;
`blocked` means open premises or dependencies; `ready` means an unfinished
statement/premise has no such blockers; `open` covers unfinished helper nodes.
Every area and selected progress-root closure has numeric counts for these states,
node totals and open typed premises. All discovered logical/certificate premises
currently remain open. There is no typed witness discharge yet: these are
conservative inventories, not actual producer-premise completion measurements.

Claims run beside the prose registry. Each state is bound to one immutable graph
digest. A POSIX advisory lock serializes cooperating writers; a fsynced temporary
file, atomic replacement and directory fsync publish one transaction. Claims
require the catalog's producer owner, unique unexpired tokens and finite bounded
leases. Graph changes, double claims, expired renewals, stale tokens and attempts
to claim completed nodes reject. Expiry permits a new token for the same assigned
producer; it never transfers producer ownership. Production time is sampled after
lock acquisition. Tokens are coordination capabilities, not an authentication
boundary for mutually hostile filesystem users.

## Validation and trust boundary

The official Lean 4.35.0 Linux archive matches coordinator SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Actual versions: Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake 5.0.0-src+eb6cafb.
Initial 4.24 checks preceded the coordinator pin and do not establish a final gate.

Before this checkpoint, pinned serial fixture acceptance passed 30 Python tests,
12-process exclusive-claim contention, stale-owner/double-claim negative controls,
Lean unknown/duplicate/conflicting-declaration controls, structure-field export,
and same-process/fresh-process byte equality. MCP diagnostics for both Lean files
returned success=true, partial=false, items=[]; the installed MCP dependency emits
its known event-loop-close warning during shutdown. The unchanged KeySort control
passed; the second provisional seven-run median changed from 1.260098 s to
1.212763 s (-3.76%). These provisional runs preceded clean-tree enforcement and
are not committed-tree attestations. Final checkpoint evidence is recorded in the
off-git handoff after committing and rerunning the corrected harness.

Run from this checkout, substituting the saved absolute evidence directory:

```sh
python3 -B scripts/h62/item5/statement-graph/verify.py \
  --lean-bin /workspace/.setup/tools/lean-4.35.0-linux/bin \
  --pin /workspace/h62-coordinator-inputs/toolchain-pin.json \
  --archive /workspace/.setup/tools/lean-4.35.0-linux.tar.zst \
  --evidence /workspace/h62-statement-graph-evidence/committed-acceptance
/workspace/solidity-lean/.venv/bin/python -B \
  scripts/h62/item5/statement-graph/mcp_check.py \
  --lean-bin /workspace/.setup/tools/lean-4.35.0-linux/bin \
  --pin /workspace/h62-coordinator-inputs/toolchain-pin.json \
  --archive /workspace/.setup/tools/lean-4.35.0-linux.tar.zst \
  --evidence /workspace/h62-statement-graph-evidence/committed-acceptance
```

The runner enforces one heavy job, `LEAN_NUM_THREADS=1`, explicit `-j1`, a
12 GiB virtual-memory bound, no swap, a continuing 4 GiB available reserve and
bounded individual commands. Python optimization is rejected. It generates
large outputs, command/exit logs, timings and a checksum manifest off git.
No v4.24 per-master cache or systemd-run is used. Core source is unchanged;
KeySort timing measures an unchanged control, not whole-project performance.

Lean checks the isolated fixture theorem terms. Python regressions test graph
and filesystem coordination behavior; their synthetic models are not kernel
proofs, and JSON/catalog input is trusted external tooling input. No new axiom,
sorry, native_decide, heartbeat increase, frozen-statement edit, axiom pin edit,
module-root edit or change to H55's theorem is present. Required full
`./run-lean.sh` and production census/progress validation remain pending before
RUNTIME_GATE_PASS or assignment completion.

## Independent reviews

Independent read-only finder and skeptic agents used no Lean server/process.
Both found missing structure fields, Type-valued certificates, tagged dependency
coverage, stable binder expression contexts and correct producer ownership.
These were corrected and covered by negative tests. The finder also found the
pre-lock lease clock; the skeptic found optional axiom evidence. Both were fixed.
Their second pass found dirty-source provenance, imported-overlay conflicts,
MCP resource gaps and Python optimization bypasses. Corrections are included in
this checkpoint; final re-review and committed-tree evidence belong in the saved
handoff. Premise discharge remains explicitly unfinished rather than hidden by
an assertion of completion.

## Coordinator handoff and blockers

Repository: `/workspace/solidity-h62-statement-graph`; original clean checkout
`/workspace/solidity-lean` is preserved. Exact published base was fetched and
verified as an ancestor of origin/master before this isolated branch was created.
Verified coordinator inputs are at `/workspace/h62-coordinator-inputs/`.
All five G49/G50 items belong to H55-G49 in its ownership snapshot.

- `B-H55-INVENTORY` (producer-data dependency): no committed declaration/premise
  inventory or typed witness mapping is supplied for H55's final theorem.
- `B-H55-RELAY` (coordination dependency): no relay.sh is present in the pinned
  tree or discovered workspace. A coordinator relay path or producer inventory
  was requested. No absence of reply is treated as permission.
- `B-PRODUCTION-GRAPH` depends on those inputs: area census, production DAG,
  actual G49/G50 counts and declaration/owner compatibility acceptance remain.
- `B-FINAL-GATE`: final affected/full repository validation and timing evidence
  remain mandatory after production integration; no runtime pass is claimed.

Backfill completed here is limited to isolated type/field/certificate controls,
malformed-input controls, deterministic reproduction, timing and claim races.
There is no continuous-cleanup scope claim or duplicate H55 proof work. No push,
merge, PR, pre-gate or publication was performed. Resume the same goal and branch;
do not create a replacement goal. The final saved handoff records committed head,
patch/evidence paths and hashes. Registration advice is in the task's additive
`REGISTRATION.md`; existing generated roots/maps remain read-only.

## Saved checkpoint validation and fresh-thread handoff

Implementation commit `0d29ea3685bc2d457f875482cfaabf98a186a8d3`, tree
`283a46ec2b8e84f886ea5859620bb56c17f90b6d`, passed corrected clean-tree
acceptance. Evidence: `/workspace/h62-statement-graph-evidence/final-acceptance/`.
The final run passed all 30 Python tests, 12-process exclusivity, imported-overlay
conflict checks, inhabited dependent Type-certificate controls and private-declaration
coverage. Ten explicitly selected fixture declarations and a 34-declaration census
matched byte-for-byte within one process and across fresh processes. Every selected
fixture declaration's transitive axiom list was empty. These are fixture counts;
they make no production G49/G50 claim.

The unchanged KeySort seven-run median was 1.112130489 s before and 1.157862073 s
after (+4.1121%, below 10%). Final MCP diagnostics for Exporter and Fixture
returned success=true, partial=false, items=[], with its dependency's known
shutdown warning. Layers reported 857 core modules and zero elaborator/parser
adapter reachability; generated roots/fragments checks and git diff --check passed.
Both independent reviewers confirmed all reported checkpoint code findings resolved
at the implementation commit, including private-name recovery in the census.
Neither reviewer ran Lean. Review summaries and exact commands are saved off git.

Additional backfill is reproducible through
`scripts/h62/item5/statement-graph/census.py` with the same four required arguments
as verify.py. It compiles the exact inspected Roadmap dependencies serially with
4.35, then exports the actual namespace including private declarations and generated
constructors/recursors, without assigning proof ownership or progress. Its production
run failed before exporting: unchanged `Solidity/Hash/CollisionBound.lean` has an
unsolved goal at 407:56, omega failures at 660:4 and 680:4, then axiom-message guard
mismatches at 950–968. The failure's elaboration-error sorryAx is not a checked or
committed proof. No owner-file edits or trust-policy changes were made.
Evidence: `/workspace/h62-statement-graph-evidence/roadmap-census/CollisionBound.log`.
`B-MIGRATION-HASH` is an external owner/toolchain compatibility blocker, in addition
to B-H55-INVENTORY, B-H55-RELAY, B-PRODUCTION-GRAPH and B-FINAL-GATE above.

The implementation checkpoints are: tags/exporter done; per-area production DAG
partial; exclusive claims done; production G49/G50 progress partial. Typed witness
mapping/discharge, actual production census and all final/full gates remain binding.
No RUNTIME_GATE_PASS or complete-goal assertion is made. This thread has reached
its checkpoint/backfill handoff; coordinator should resume the exact original goal,
VM and branch after supplying H55 inputs and a producer-approved migration fix.
Do not launch another goal or reset/discard this branch. Final absolute patch,
bundle, handoff and evidence paths/hashes are recorded at
`/workspace/h62-statement-graph-handoff/`.

## Coordinator input update: pending G49 inventory

The coordinator answered Q-H55-INVENTORY: `h64-shapes.json` is on the
G49-final-theorem VM and is not yet on origin. The coordinator will relay it
with the producer's next CLOUDVM-RESULT. No further inventory question is open.
Continue available inputs; the G49/G50 work-item entries are explicitly
`pending-input` in `tests/h62/item5/statement-graph/pending-inputs.json`, with
existing H55 owner references. These are metadata placeholders, not invented
Lean declarations or satisfied dependencies. H55's theorem remains read-only.

The graph accepts these entries separately from typed declarations. They are
blocked and unclaimable, retain `declaration=null`, `exists=null` and unknown
dependency inventories, and cannot supply completion/declaration/dependency
fields. Progress includes `pendingInputs`, `typedDeclarations`,
`knownOpenPremises` and `premiseInventoryComplete`. When any input in a root's
closure is pending, `openPremises=null`; the numeric known count remains a
lower bound, never a complete zero-premise claim. Fully available root counts
remain exact under the existing conservative open-premise semantics.

`Pending.lean` produces an empty elaborated-type export; acceptance builds the
pending-only production graph against the verified ownership snapshot. Mixed
available/pending model tests verify that available typed nodes and counts are
preserved and a pending entry cannot hide an omitted tagged declaration.
The independent EVM input census can now run with `census.py --area evm` without
importing the failing CollisionBound module. Its results are separately recorded;
it makes no G49/G50 statement or owner inference. No full runtime gate is implied.

### Pending-input checkpoint evidence

Validated implementation: `e846768d844272d595c1927922b28383037b0a49`, tree `336b91a1e4985d43f7d82560d31d061b7ec263b4`.
Committed-tree acceptance passed 32 tests, the existing 12-process claim race,
pending-only production generation and mixed available/pending regressions.
The production placeholder graph contains five blocked pending inputs, zero
typed declarations and `openPremises=null`; its known count is zero with
`premiseInventoryComplete=false`. No completed statement is inferred.
Evidence: `/workspace/h62-statement-graph-evidence/pending-acceptance/`.

Both independent read-only reviewers confirmed the changes without using Lean
or its server. Per-file MCP checks passed Exporter, Fixture, Pending and
EvmCensus with no diagnostic items. Known dependency shutdown warnings are
archived. KeySort control medians were 1.112864061s before and 1.062098248s
after (-4.5617%, within the slowdown bound). Layers, generated roots/fragments
and diff checks passed. These are bounded controls, not whole-project timings.

The independent pinned EVM input census passed: 391 elaborated declarations,
34 structure fields; the census explicitly includes generated declarations.
Its kinds are 118 theorems, 217 definitions, 12 inductives, 32 constructors and
12 recursors. These are census records, not 391 interface-statement graph nodes.
Evidence: `/workspace/h62-statement-graph-evidence/evm-input-census/`.
No inferred proof-owner assignment or G49/G50 completion is attached to them.
The full Roadmap census and final full gate still require the separate
CollisionBound migration repair; no owner file has changed.

Q-H55-INVENTORY and B-H55-RELAY are resolved by the coordinator's explicit
relay arrangement. B-H55-INVENTORY is now `pending-input`, awaiting
`h64-shapes.json` from the producer's next result. No question or further
permission request is open. B-PRODUCTION-GRAPH, typed witness discharge and
B-FINAL-GATE remain binding. The goal is not complete. The new handoff is at
`/workspace/h62-statement-graph-handoff-pending/`; the previous exported handoff
and archive remain intact. Resume this same original goal and branch when
inputs or owner-approved migration repairs arrive.

## H70 owner overlay relay

The coordinator relayed the reviewed Hash owner patch from
`solidity-h62-6-20261106/migrate-hash` at
`2a18afcdba00a85645b0b3079704f78ffcd78860` for isolated migration validation.
It explicitly grants no original-file edit permission. Only the CollisionBound
portion is needed for the Roadmap census; Adaptive is not applied or edited.
The exact relayed patch and provenance are stored as small reproduction inputs
under the owned test directory's `overlays/` subdirectory.

`census.py --hash-owner-overlay` verifies the checkout and pinned-base bytes
against blob `b54c93a5b24340a19160c1fb378d057ccee60f84`, applies the patch
only in an off-checkout source copy, verifies target blob
`092971eda8c7d6997276a92ba19b25b7ce05844e` against the published prefix,
and compiles that copy with an explicit package root. The original Hash source
remains unchanged. The owner commit object is not local; its identity is relayed
metadata, while file base/target hashes are independently verified.

The census summary distinguishes original source hashes from validation source
hashes and includes the overlay patch hash, owner provenance and a combined
validation-input digest. It must not be represented as validation of the plain
repository tree or a full migration gate. Exact-base, wrong-base, changed-patch,
inside-checkout and unexpected-copy preservation controls are included.
`relay.sh` is host-only; no local relay script or original-file permission is
inferred from routing. G49 full production inventory remains pending coordinator
relay. Metadata and census records remain separate from discharged proofs.

### H70 boundary after exact overlay validation

The exact copied CollisionBound module compiled on pinned 4.35 with exit 0;
its original checkout blob remains `b54c93a5b24340a19160c1fb378d057ccee60f84`.
The next unchanged module, `Solidity/Roadmap/Contracts.lean`, failed at 1104:
its `PublicCorrectness.transfer` axiom-message guard expects no axioms but reports
`propext`, `Classical.choice`, `Quot.sound` under 4.35. This is an owner/trust-policy
boundary, not permission to update a pin or expected guard message. No Contracts
proof, statement, guard or trust policy has been changed. The full Roadmap census
is still unsuccessful; no production census or compatibility pass is claimed.

`census.py` now saves input provenance before compilation, including original and
validation source hashes, owner overlay and combined input digest, so failed gates
are bound to their precise inputs too. Each completed compiler invocation records
original-source, HEAD and checkout-cleanliness checks. The skeptic's destination
finding was fixed by rejecting every registered worktree and any other Git checkout
before writes, with a preserved-original-checkout negative control. Both read-only
reviewers confirmed the fix without Lean/server use. The exact decoded patch is
stored in JSON to preserve unified-diff spaces while passing whitespace checks.
Q-H70-CONTRACTS requests an owner-reviewed fix preserving statements/trust policy,
or continued waiting for the fleet/G49 migration. Host-only routing creates no
local file-edit authorization. G49 producer inventory remains pending input.

### H70 committed checkpoint handoff

Validated implementation `2e563d9f5dc9f1d3552b20f702eeee8eefc4b7c6`, tree `b9e11e9a7270000705530a848607e9b38110d7a3`:
37 isolated acceptance tests passed, including all original graph/claim cases
and five owner-overlay controls. KeySort medians: 1.164584963s before,
1.160787181s after (-0.3261%); this unchanged control is not whole-project
migration timing. Layers/generated roots/fragments/diff checks passed.
Evidence: `/workspace/h62-statement-graph-evidence/h70-acceptance/`.
Both independent read-only reviewers confirmed the final overlay/provenance
changes; neither ran Lean or a Lean server.

The guarded isolated census run records input digest
`29e283dee59e2888f577b5b4aa54c46bacbf955b67d1b87a5e5051f7a3d06797` before compilation.
CollisionBound copy, Keccak and EVM exit 0; unchanged Contracts exits 1 at its
1104 axiom guard. All four command records show original sources unchanged,
stable HEAD and clean checkout. The original CollisionBound blob still equals
the verified pinned base; the patched target exists only off checkout.
Evidence: `/workspace/h62-statement-graph-evidence/h70-roadmap-final/`.

B-MIGRATION-HASH is resolved for this exact isolated copy only; full migration
and cut-over gates remain pending. B-H70-CONTRACTS now records the unchanged
`PublicCorrectness.transfer` axiom-message guard mismatch. No guard, proof,
axiom pin or trust policy was modified. Its owner-reviewed resolution and the
actual G49 exported production inventory are still needed before production
DAG/typed owner compatibility and witness discharge can complete. Pending
G49/G50 entries remain metadata, not discharged proofs. Q-H70-CONTRACTS records
the owner-routing question; host-only relay routing grants no original-file edit
permission. No further scope is inferred from this checkpoint.

New patch, bundle, evidence and handoff are saved under
`/workspace/h62-statement-graph-handoff-h70/`. Earlier exports remain intact.
The full original goal remains unfinished; continue the same VM/branch/goal
when reviewed inputs arrive, without creating a replacement goal. No merge,
push, PR, pre-gate, publication or original producer-file edit occurred.

## H70 routing disposition at requester 372e4628

The next coordinator relay reports Hash owner ticket head
`78c110f83dc1a30700acd1b5bd34b19f61da6ccd` with overlay source head
`2a18afcdba00a85645b0b3079704f78ffcd78860`. Its decoded CollisionBound
patch SHA256 exactly matches the already validated partial overlay:
`3aebc61f1a1979d4e36d669e3c33f5ae8c848d38a3ca0574c62329bdc154bbff`.
No identical Lean gate is repeated. This is still a partial Hash overlay;
full migration gates and Syntax.Raw remain pending on that lane.

`h70-routing.json` records the machine-readable production metadata disposition.
The owner routes are now H55 G49-final-theorem for production declaration inventory
and H62 migrate-roadmap for Contracts:1104. The coordinator reports no pending
current-owner delivery, but host relay journals determine acceptance; neither
owner agreement nor validation follows from this relay. Q-H70-CONTRACTS is
resolved as **wait for the routed owner fix**. H64 excludes guard relaxation.
No further permission question is open and no original-file permission is granted.

All five G49/G50 entries remain explicit pending inputs. No type, statement,
dependency, compatibility match or discharged premise is inferred. The failed
Contracts guard and the absent actual G49 production declaration inventory remain
the two input boundaries. Current metadata can be regenerated against the verified
ownership snapshot, with unknown total open premises represented as null. The
existing 37-test and isolated-overlay evidence remains bounded to its recorded
implementation/source hashes; this routing-only update is not a new proof gate.
New exports are saved under `/workspace/h62-statement-graph-handoff-h70-routing/`.
Continue the same original VM/goal/branch when owner-reviewed inputs arrive.
