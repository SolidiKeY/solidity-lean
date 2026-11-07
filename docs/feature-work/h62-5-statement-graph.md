# H62 item 5: statement graph

H145 archival notice: historical receipts, source-hash manifests, routing/chain
records and handoffs named below now live in the private coordination repository:
https://github.com/SolidiKeY/solidity-lean-coord/tree/4cb216278ddc62582604b4348d65749fcf9bfeb6/evidence/solidity-h62-5-20261106/statement-graph/
The private archive preserves their exact bytes and source revision. References
to “committed evidence” in older milestones describe those earlier revisions.
Current checker inputs, executable fixtures and checksum constants remain here;
evidence records are no longer code-branch inputs.

## H151 historical gaps and current waits

H151 supersedes historical instructions below to wait for unrecoverable artifacts.
The following exact retired-member deliveries are **UNVERIFIABLE**: drift-reports
`faca44dc415dfbdab9b9ea6b0664f1e755abaa57`, artifact-fixtures
`9cc85b14fa3f611e183379c257b10b19e1aa5325`, and runtime-fixtures
`f8975f25b12a5e9723b00ec794b261708280092c`. Their cumulative source artifacts and
original runtime captures were unavailable after coordinator and lane lookup.
Authenticated assignment metadata and reported results do not establish their
source integration, gate passes or delivery. Those original claims remain
unproven; these missing historical artifacts are documented gaps, not waits.
Previously archived evidence that is available remains available; this designation
applies only to the missing deliveries and captures.

Missing original H70 overlay captures are likewise **UNVERIFIABLE**, not an
artifact-recovery wait. The historical CollisionBound fixture still requires its
exact pinned base and must refuse a different source blob. Fresh reproduction
from recoverable pinned inputs can establish a new result with its own source
identity; it cannot authenticate a lost capture. No fresh reproduction or repaired
overlay acceptance is claimed here, and no guard is relaxed.

Fresh evidence may be generated from available code and authenticated assignments
where scope and active holds permit. It must identify its actual source revision
and current checker, rather than relabeling historical results. Evidence belongs
in the H145 private archive. Missing final heads cannot be treated as merged or
replaced by a nearby snapshot. This gap classification does not complete the
retired queues or the original statement-graph assignment.

Remaining active waits are typed G49 Source/runtime inputs from
`solidity-h62-3-20261106/g52-differential`, identification and typed inputs from
the unresolved Bridge producer, explicit Contracts empty-guard and Raw
compatibility/axiom acceptance, and coordinator runtime/pin-registration
confirmation. H146/H147 shared refresh and warming belong to the host merge
wrapper; no success is inferred. Existing timing STOPs, the pin pause, H58 audit HOLD,
statements, dependent definitions, interfaces, budgets, axioms and exclusions
remain unchanged. Historical wait lists below describe their earlier checkpoints.

A fresh limited reproduction on source `316571df66984bb4597810ad44ef686eceea87a4`
passed all 30 supplied fixture cases for each of the three available drift tools,
with two byte-identical output runs per case. This is 90 external fixture controls,
not the frozen acceptance entrypoint, complete pinned corpus, coordinator rerun,
Lean validation or a before/after timing gate. Source and fixture hashes are
recorded privately; none of these fresh results authenticates a missing capture.

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

## H82 registry-tooling consolidation intake

The human-approved consolidation adds all six retiring member queues to this
same original goal. No replacement goal or VM is created. The survivor stays on
its assigned branch. Full frozen assignments and exact member scope manifests
must arrive in authenticated final handoffs before any member task execution;
quoted summaries and host receipt paths are not substitutes for those bytes.

`h82-chain.json` records schema-v1 waits and announced/published heads. The two
published branches were fetched for read-only reconciliation: trust-fragments
matches its announced head; pin-fragments has advanced to 7587ff4e7d0c39eb46db95a37080106b9919d08d,
a descendant of announced 578d7d41508856c54984be665e7e954212f1d521. Neither is
assumed final or merged. Other member branches were not advertised by origin.
All six final authenticated handoffs and explicit stopped/goal-paused
acknowledgements are missing locally; result-size-cache's uncommitted work must
be preserved. No successor relay acceptance or retirement stop request is sent.
Pin-fragments' explicit pause and +46.58% writer STOP remain binding; no rerun or
proposal resumption is allowed by this intake.

Retiring scopes remain untouched until the barrier clears, then each verified
final head must merge first before its task work. The authoritative H82 scope
manifest and H81 resource policy were requested as VM-readable inputs. While
waiting, work continues only in this lane's original unpaused scope. No heavy
Lean check is launched without the current resource policy. Claude-owned
implementations remain read-only and no messages are sent to Claude lanes.
The physical G49 producer is now a Claude external dependency; metadata retains
the logical owner reference until an authoritative ownership/input relay arrives.

H82 supersedes exact-file agreement demands for allowed statement-preserving
Codex work; it does not authorize a statement, definition-dependency, signature,
budget, axiom-set or exclusion change. The specific Contracts:1104 wait still
stands, with its exact empty guard preserved: H30 standard-axiom re-pinning does
not authorize changing it. Full PassCorrect, witness/vacuity, public-shim/editor
requirements and all member frozen acceptance/STOP constraints remain binding.

### H82b authenticated intake and typed witness checkpoint

The H82b package at `/workspace/h82-handoffs/h82b-20261106T180909Z`
passed its archive, manifest and all 557 per-file hashes. Its authoritative
assignment envelopes, live scope and stopped/head receipts resolve the metadata
waits. Legacy rendered-wrapper hashes remain provenance; no byte equivalence
with the extracted assignment text is asserted. Three exact final heads are
integrated: result-size-cache `6c93ebcd`, pin-fragments `7587ff4e`, and
trust-fragments `8dc693e4`. Drift, artifact and runtime final Git objects remain
unavailable. Metadata receipt does not establish their merge or any gate pass.
The coordinator-requested origin/master merge is `fe5140232485efba2d47ff55f0ac90e497c1e22f`.
All own uncommitted work was preserved through that merge.

Optional `#h62_witness` registrations now compute the universal closure of an
actual elaborated binder or constructor-field type. A safe kernel-checked helper
must match that closure with rigid consumer universes and no unresolved
metavariables or transitive axioms. Exported witness evidence is separate from
statement and proof-helper dependencies. The graph verifies location, exact type,
producer ownership and preceding named premise prerequisites. Witness availability
alone cannot discharge an earlier open premise or complete a Type-valued interface.
The fixture separates inhabited positive witnesses from intentional contradiction.
No production statement, definition, axiom guard, exclusion or proof budget changed;
no new source axiom, sorry or native_decide was added.

At this checkpoint 44 external Python controls pass; exporter per-file MCP
and direct serial exporter/WitnessFixture compilation pass with official Lean
4.35.0. Evidence is under `/workspace/h62-statement-graph-evidence/h82-witness-*`.
The authenticated H78/H81 policy is applied conservatively: one Lean job, explicit
-j1, 8 GiB address-space cap, no swap and 4 GiB available reserve. Full fixture
acceptance, new negative controls and fresh timing remain pending at commit time.
Production G49/G50 declarations and Contracts' exact empty guard fix remain waits;
no production discharge or RUNTIME_GATE_PASS is claimed. Pin writer STOP remains
unchanged and its explicitly paused proposal was not resumed.

Final witness checkpoint gates supersede the pending note above. At committed
source head recorded in `h82-witness-evidence.json`, full clean-tree fixture
acceptance passed, including 44 Python controls, deterministic same/fresh-process
exports, unsafe/axiom/type/index/duplicate/universe/import rejection checks and
all graph count assertions. Certificate and Pair now explicitly inhabit Type;
MCP exposed the earlier inferred-Prop fixture gap. The corrected acceptance
checks actual elaborated sort expressions and the certificate binder's isProp
flag. Two harness-only assertion failures (nonexistent field and repr layout)
were fixed without weakening those checks; failed evidence is retained off git.
Both read-only reviews found no remaining static blocker. Exporter and corrected
WitnessFixture per-file MCP diagnostics pass without warnings. MCP library
shutdown prints an event-loop warning after results; diagnostic calls succeed
and exit zero. No Lean server was used by either reviewer.

Official versions: Lean 4.35.0 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
Lake 5.0.0-src+eb6cafb. All bounded KeySort controls pass. Seven-run medians on
the corrected fixture tree are 1.209114830s before and 1.162983514s after,
-3.8153%; this is an unchanged-core control, not a project speedup claim.
The evidence manifest binds actual outputs and the tested committed head.
Full production DAG/counts, actual G49/G50 inventory, Contracts empty-guard fix,
project final gate, and all inherited open member obligations remain unfinished.
No known timing STOP was rerun, no frozen production statement/guard changed,
and no original goal was created, reset, completed or claimed paused.

### Fresh-thread handoff after three implementation milestones

The typed witness fixture, local H55 v1 compatibility and trust-fragment snapshot/
resource hardening milestones are committed and independently reviewed. Follow
user-required fresh-thread handoff now; do not self-launch a replacement goal or
VM. Original VM environment:
ccarenv_b64_Y2NhcmVudl9mNWI2NjA5Mjg2NDA4MTkxYjNlNzQ5ZGM2YWM0NTI5OQ.
Repository /workspace/solidity-h62-statement-graph, same assigned branch,
original goal objective rendered-prompt provenance SHA256
9b5f127834cb2597a16f03dd05cba17c2467359fefcd5b5ba42db8e88933075a.
No exposed get_goal/pause operation; do not invent a goal ID or create another.
Implementation head before this documentation checkpoint:
6f3e173b0fd103d0b4d59e88e3248a8399ea3c24. Entire original/H82 queue unfinished.

Exact origin SHA fetches for drift faca44dc415dfbdab9b9ea6b0664f1e755abaa57,
artifact 9cc85b14fa3f611e183379c257b10b19e1aa5325 and runtime
f8975f25b12a5e9723b00ec794b261708280092c each exited 128 with upload-pack:
not our ref. Preserve those typed artifact waits and recover original bundles
through coordinator; do not assume authenticated metadata contains Git objects.
Next independent queue work remains integrated H55 local controls and trust
registration acceptance after required inputs, plus original graph production
inventory when relayed. Explicitly paused pin proposal remains stopped. No
full-project gate, production proof discharge or whole-goal completion claimed.

### H70/H90 continuation: independent refusal coverage

Coordinator routed compatibility waits to migrate-root-gate (Contracts:1104 exact
empty guard and Syntax.Raw); G49 inventory forwarding is staged for Claude and
no stale/retired owner was contacted. Routing is not validation or owner agreement.
No fresh-thread creation, goal reset or replacement is inferred from the router.
H86 unavailable raw evidence remains an explicit regeneration limitation.

Independent graph backfill now generates named regression docstrings for witness
refusals, including disabled kernel checking and unresolved witness universes.
A direct syntactic unused-universe fixture was rejected by Lean before reaching
the exporter; a first low-level driver lacked the Command/Core monad lift. Those
failed harness attempts are retained and not counted as intended refusals. The
corrected control uses a safe kernel-checked True definition with an unused
universe parameter, then confirms registerWitness refuses its unresolved level.
The kernel-skip control confirms the command refuses before adding any helper.
No theorem is accepted with kernel checking disabled; no axiom/sorry/native_decide
or production declaration/budget/guard change was introduced.

All witness negatives require exact JSON error bodies, never filename text,
warnings or setup failures. Forty-five Python controls pass. The corrected direct
probes pass; full clean-tree optional fixture acceptance remains pending at this
commit. Existing production inventory/full gate waits remain. The separate H55
size proposal hit +21.4335% timing STOP and is stopped/unaccepted; it was not
rerun unchanged while these independent controls were developed.

Final committed-tree refusal acceptance passes at the source head recorded in
h70-controls-evidence.json: 45 Python controls, intended JSON diagnostic bodies
for all witness refusals, deterministic exports, original graph controls and
bounded KeySort. Seven-run KeySort medians 1.315427167s before and 1.368037786s
after (+3.9995%, within 10%); unchanged-core control only. Both independent
read-only reviews found no blocking delta and used no Lean/server. Source and
output hashes bind this actual acceptance; no production statement/guard edit,
axiom/sorry/native_decide, budget change or RUNTIME_GATE_PASS.

The queued trust coverage backfill accounts for all frozen source occurrences:
44 blocks, 1380 headline occurrences/1373 distinct names, 77 imports and 17 print
commands. Two regenerations are byte-identical, and all current fragments match
the pinned central source SHA256 ece2e6cebbee95d82fec246892993662e81dcfd895831981583d2b0867a37482.
This is current committed-source coverage, not declaration-existence proof or
authentication of unavailable original worker runtime evidence. The held audit
was not started. H55 size controls are functionally improved but their +21.4335%
performance STOP remains binding. No master publication, retired-lane revival,
fresh-thread creation, goal recreation/reset or claim of whole-goal completion.


### Published G49 source locator intake

Coordinator supplied the exact-master source inventory at SHA256
`af4f1a69410a9df1f408d2e2d9d9b82b39f926ce48c6bb601c16092514ed733e`.
The intake verifies all five inline bodies and Git file hashes at
706e36825929d6d0084dc08b88de9349abcd25aa, checkpoint ancestry
5f7c70b16090b25ea706dddf3e666d94fb5a09fe, and the published shape/bridge
metadata. Git replacement objects are disabled and shallow/grafted/custom
history overrides refused. The fetched master was merged into this lane before
this checkpoint. No Claude-owned source or frozen statement was edited.

All five pending views now display the source-located shared conditional theorem
`Solidity.Roadmap.G49Final.g49_g50_of_fold`. These are owner slices of one theorem,
not five checked theorem instances. Source labels retain ten named top-level
binders, nine context/function/package inputs including three certificate
packages, and all fifteen named PublicObligations fields, including externally
owned fields. Five reported bridge requests remain pending and undelivered.
Thirty-two explicit source declaration anchors do not assert generated projection
existence or exhaustive lane coverage. Historical producer checking claims and
hashes are explicitly reported metadata, not fresh local checks.

The source catalog remains pending-input, blocked and unclaimable: exists and
elaborated types are unknown, typed declarations are zero, no statement edges
come from source text, and expanded atomic open-premise counts remain null.
Graph validation checks pinned named coverage and internal consistency; only
source_intake.py's main command authenticates the catalog against the delivered
packet and exact Git blobs. Neither mechanism elaborates Lean or discharges a
premise. Reproduce with `python3 -B scripts/h62/item5/statement-graph/source_intake.py
--output /tmp/g49-source-catalog.json`, then compare with pending-inputs.json.
The command requires the authenticated coordinator packet and ownership snapshot.

Fifty-two Python controls pass, covering source omissions, changed package roles,
missing/substituted bridge requests, missing views/locators, owner/provenance
changes, false typed/done promotion, exclusive-claim refusal and determinism.
Finder identified missing source-census coverage and replacement-sensitive
ancestry; both were fixed. Skeptic confirmed the source/type boundary and noted
the ancestry environment qualification, now explicitly refused. Neither reviewer
used Lean/server. Exact catalog regeneration is byte-identical.

The first inline validator hit cold CLI +11.9968% and was stopped. Moving source
validation behind a lazy source-only entry point preserves byte-identical legacy
fixture output, with seven-run cold median 0.040133073s to 0.042375455s (+5.5874%)
and warm median 0.000367768s to 0.000338361s (-7.9961%). These are Python fixture
compatibility controls, not project or Lean performance measurements. The failed
inline version and harness setup failures remain in off-git evidence. No unchanged
STOP was rerun. Repo-relative source pins, counts and timing outputs are committed
in g49-source-intake-evidence.json; generated graphs and bulk logs remain off git.

Actual G49 source-input wait is resolved; elaborated production types, full
per-area DAG and G49/G50 counts remain incomplete. Wait for migrate-root-gate's
Contracts:1104 exact empty-guard repair and Syntax.Raw compatibility, and for
actual producer bridges. No new Lean/Lake/KeySort run or RUNTIME_GATE_PASS is
claimed for this Python/metadata-only change. Prior official Lean 4.35.0 and
Lake 5.0.0-src+eb6cafb checks remain historical. Exact retired member source
objects faca44dc415dfbdab9b9ea6b0664f1e755abaa57,
9cc85b14fa3f611e183379c257b10b19e1aa5325 and
f8975f25b12a5e9723b00ec794b261708280092c remain unavailable; no substitution.
H97 cold +12.7602%, H55 size +21.4335%, pin +46.58% STOP/pause, H67 central
reconciliation and H58 audit HOLD remain unchanged. Entire same-goal queue and
required operational handoff remain unfinished.


### H107 Wave 0 tooling safety nets (OT-W0-TOOLING)

Implemented before other new queue work, after merging origin/master
33eb46304cdb536e6c8b686223c6d8e456b703ae. No production Lean source changed.
The exact architecture audit tree fa5acebd43214bbe642258d862f903bcf08d3f89
reproduces 95 pinned boundary edges, not today's 107. Immutable baseline SHA256
is d202b21ddde800b40237b9c4a95482c17b8d5ea8d2c78c1b42e4bad7344ac80b;
its deterministic Git-object generator, snapshot, checksum and shrink-only active
subset are committed. docs/parallelism.md P1 now explains the boundary policy.
Existing elaborator/parser bans are retained independently. The closure scanner
handles comments, indentation and multiple modules; unsupported import syntax
fails closed. Paths through existing exceptions remain debt, not new CORE members.

The gate retries failed named build steps exactly once only if the captured log
contains `Lean exited with code 135`, printing `RETRY-SIGBUS <step>`. It preserves
the first log plus the combined attempts. The full run-lean wrapper is a build
step: its read-only prefixes repeat on retry, while separately named static gates
never retry. Ordinary/thread failures remain failures. Backup-copy failure is
explicitly fail-closed. No actual SIGBUS occurred in this checkpoint; injected
controls establish the retry behavior, not proof of shared-cache crash recovery.

Independent finder/skeptic reviews (neither Lean/server) identified deletion and
recreation restoring removed allowances, failed backup yielding a false pass,
hidden multi-import edges, and configured merge-diff filtering. Fixes include
actual-parent history checks with explicit separate merge diffs, permanent subset
checks, deletion rejection, backup failure propagation and robust import scanning.
Nine H107 controls now cover these, cycles/transitive paths, success/ordinary
failure, persistent SIGBUS, once-only recovery and the full-build wrapper. All 61
graph/tooling controls passed before the final merge-diff flag hardening; the nine
H107 controls passed again after it, including log.diffMerges=first-parent.
Node syntax checks, bash -n, fragments/register checks and exact95-byte regeneration
pass. History scanning avoids unrelated empty merge probes; final layer output is
byte-identical to the checkpoint (about2.27s versus16s observed gate timing; this
is a changed static tool, not a Lean speed claim).

The required real `bash scripts/coord-tools/gate.sh checkpoint` ran once under the
verified official Lean4.35.0 archive, LEAN_NUM_THREADS=1, serial Lean flock with
explicit -j1, 8GiB AS/aggregate bound, no swap and4GiB reserve. Lean reports
4.35.0/eb6cafb; Lake5.0.0-src+eb6cafb. KeySort built successfully in1.2s, but the
library aborted with `failed to create thread: Resource temporarily unavailable`;
this is not the SIGBUS marker and was not retried. Checkpoint exit1 after94.154s,
peak aggregate RSS912216064 bytes, no memory/headroom stop. Layers correctly fail
on12 boundary edges added after the95-edge audit, and existing doc-path ambiguity
and99 unrecorded axiom-pin changes also fail. Trust/orphans/roots/fragments and
build-touched pass. No pin edits, guard relaxation, new allowances or hidden retry
were used to turn those failures into success. The checkpoint preceded the final
history-scan optimization; final static checks preserve identical layer failures.

Repo-relative source pins, exact12 edge endpoints, gate outcomes and limits are in
h107-tooling-evidence.json. Bulk checkpoint logs remain off git with a checksum
manifest and handoff archive. The H107 implementation is reviewable as one tooling
increment; successful task-branch final gates and the whole original/H82 queue
remain unfinished. Existing STOPs/H58/H67 holds and original producer/artifact waits
are unchanged. No push, master publication, new goal or RUNTIME_GATE_PASS.


### H112 Wave 0B documentation and pin-drift gates

OT-W0B-GATES was completed after H107, after fetching and merging master
8dbbb58e6eda3d7a8e7e55fbb31e24acf5eb5990. Exact intake at parent
7dbf2748b5b0a02e42cccd6cf25c91fa77c9aade found the requested five missing
references across four files, and99 unrecorded pin changes with zero policy
errors among16140 source pins. The older approximate4500 count was not padded
or substituted for actual data. The five references name unadopted destinations,
an off-git failed experiment, or a synthetic negative input; exact source/ref
historical exceptions now carry reasons. Other sources citing those paths and
other missing paths in the same source still fail. Existing ambiguous references
remain warnings in the default gate and failures under its unchanged strict mode.

The99 exact file/name/kind/old-axiom-set/new-axiom-set changes are frozen in
scripts/g07-unrecorded-baseline.json, SHA256
4d98b1810853c54992feb064f1a7b028e23d8212fd2aad8b8b65e81895d7c701.
The separate active subset can only shrink, including across deletions/recreation
and merges with configured first-parent diff defaults. Linked worktrees use the
actual absolute graft path; shallow/custom histories are refused. A changed file,
name or axiom set is new drift. Every original policy error remains unconditional:
nonstandard axioms, growth, missing recorded pins, malformed prints and mismatched
targets cannot be hidden by this baseline. No central pin inventory or fragments
were rewritten; no source theorem, definition, empty guard, axiom set, exclusion
or proof budget changed. The core import baseline95 is untouched.

Both requested real gates now pass on staged tracked sources: doc-paths exit0
with5 explicitly explained historical pairs; axiom-pins exit0 with0errors,
0unrecorded changes and99baselined changes. Node syntax, bash syntax,
fragments/register and baseline SHA checks pass. Four legacy and ten new controls
pass (14total), covering real CLI success/new-drift/error failures, permanent
shrinking, deletion/merge resurrection, linked-worktree graft refusal, immutable
hash/schema identities, exact doc exception scope and optimized Python refusal.
The exact-source Git-tree reproducer exits0 and yields byte-identical pinned
baseline bytes, independent of today's source drift. It executes no Lean.

Finder and skeptic reviewed read-only without Lean/server. Their absolute-path
and optimized-assertion findings were fixed and tested; no static H112 blocker
remains. An initial disposable doc fixture omission is retained as failed test
evidence, not counted as a product failure or ignored. Before/after single locked
observations: doc34.646257s to33.501830s, pins18.364501s to17.595592s. These are
observations, not a repeated benchmark or proof of Lean performance. Bulk logs
and evidence remain off git with SHA manifests; repo-relative source/output pins
and actual gate outcomes are in h112-tooling-evidence.json. docs/contributing.md
explains the checks and exception boundaries.

H112 makes these two tooling gates green; it does not claim a successful full
checkpoint, fresh kernel validation, production premise discharge or
RUNTIME_GATE_PASS. H107's12 import repairs, runtime readiness, Contracts exact
empty-guard/Raw compatibility, typed G49/bridge inputs and exact missing retired
artifacts remain waits. Preserve H97+12.7602%, size+21.4335%, pin+46.58%STOP/pause,
trust/H67/H58 holds and the whole original/H82 queue. H110 same-thread continuation
is authorized; no replacement goal/thread/VM, Claude source edits, push or master
publication. This is one tooling increment with its committed handoff section.

H112 CI integration: the checks job previously used actions/checkout's default
shallow history, incompatible with permanent shrink validation. Its checkout now
uses fetch-depth0 and it runs the two gates plus their regression controls before
the independent layer check. Lean build/audit jobs are unchanged; no held audit
was started. This integration fix is included in the same H112 increment.


### Authorized current-master import baseline and merge pre-gate

OT-W0-TOOLING follow-up explicitly authorizes the current-master baseline at
fea090bf9fec1a372ad32952a5e72eb4d7015888:107edges, original95plus exactly12.
The original95raw snapshot/hash and active cleanup history are preserved. A new
immutable current snapshot pins all107 and full12introductions, SHA256
880486dcbe8f1004449dc9f1d90f25a9964d0b2c5ea64dad3de3dd5cfc548b8d.
The original95active set and additional12active set independently shrink forever;
removing an old edge cannot be bypassed by moving it into the new component.
No further re-pinning or baseline growth is authorized by this change. No CORE
classification, Lean import, statement, definition, axiom, exclusion or budget
was changed. The12 are explicit debt candidates to remove:

| Direct boundary edge | Verified introducing commit | Disposition |
|---|---|---|
| `Solidity.Roadmap.G49Final.PassCorrectAdapters` → `Solidity.Lowering.P8b.Frozen` | `138f7a568b6aeb4a98fad985b8d7b0c628356c5e` | Open cleanup candidate |
| `Solidity.Yul.Composition.Controls` → `Solidity.Source.StateExamples` | `e75bad809cfda97eedc97d694eaeeac3243ae353` | Open cleanup candidate |
| `Solidity.Yul.Composition.Interface` → `Solidity.Backend.Environment.ByteConstants` | `e75bad809cfda97eedc97d694eaeeac3243ae353` | Open cleanup candidate |
| `Solidity.Yul.Composition.MonetaryLifecycleControls` → `Solidity.Source.StateExamples` | `9572b8d3edd01e1dc11689a85f016d9d25f92af7` | Open cleanup candidate |
| `Solidity.Yul.Composition.P6FrameCorrectness` → `Solidity.Backend.MemoryOps.PhysicalFrameImage` | `705ed8517c55ea42897c6991d252ffd45a2836be` | Open cleanup candidate |
| `Solidity.Yul.Composition.PhysicalBytes` → `Solidity.Yul.Views.Bytes` | `d36a280a9e6a68eefc2283b62e4623b3bfbeabdc` | Open cleanup candidate |
| `Solidity.Yul.Composition.PhysicalControls` → `Solidity.Yul.Views.OwnedBoolDeclarationControls` | `d36a280a9e6a68eefc2283b62e4623b3bfbeabdc` | Open cleanup candidate |
| `Solidity.Yul.Composition.PhysicalFrames` → `Solidity.Yul.Views.OwnedBoolFrame` | `d36a280a9e6a68eefc2283b62e4623b3bfbeabdc` | Open cleanup candidate |
| `Solidity.Yul.Composition.PhysicalMemory` → `Solidity.Yul.Views.MemoryControls` | `d36a280a9e6a68eefc2283b62e4623b3bfbeabdc` | Open cleanup candidate |
| `Solidity.Yul.Composition.PhysicalMemory` → `Solidity.Yul.Views.MemoryImages` | `d36a280a9e6a68eefc2283b62e4623b3bfbeabdc` | Open cleanup candidate |
| `Solidity.Yul.Composition.SourceCatchBinding` → `Solidity.Lowering.Readonly.SourceTryEffects` | `eb9c75194d65f896c9bc483050ecea67fbe41318` | Open cleanup candidate |
| `Solidity.Yul.Composition.SourceCatchBinding` → `Solidity.Source.FailureRuntimeControls` | `eb9c75194d65f896c9bc483050ecea67fbe41318` | Open cleanup candidate |

Attribution uses the import line's Git blame and verifies it is absent from all
introducing parents. Each source file/hash/line is in the snapshot, reproduced
from the exact source commit. These12 also occur in the original pin's parent
1d99e32a08271752468b027a5495233c77a66f91; the original95came from the older
fa5acebd architecture audit. Thus attribution names the actual introduction,
without treating the first checker commit as their source introduction.
The reproducer rejects shallow/grafted/custom history and checks its full output
hash before emitting bytes. This is source/history evidence, not Lean elaboration.

`gate.sh touched`, the repository merge pre-gate used by coordinator merge reports,
now runs layers before touched builds and exits immediately on layer failure,
even for a tooling-only merge. Checkpoint/full modes use the same front check;
the later outer duplicate was removed, while run-lean.sh's own existing check
remains. Per-file diagnostics are unchanged. Run this on the prospective combined
merge tree; no automatic merge, push or host timer deployment is performed here.
CI now runs the focused Python pre-gate/history controls. Disposable mocked-build
controls verify an invalid layer never invokes Lake and valid layers precede it.

Fourteen focused controls pass, covering old/new component shrink/deletion/merge
history, legacy debt smuggling, immutable snapshots, importer parsing, SIGBUS
behavior and fail-before-build ordering. Independent read-only finder/skeptic
reviews used no Lean/server; a missing attribution-history guard was fixed and
covered, and reproduced bytes match the pin. Final real tooling gates and source
head are recorded in the accompanying evidence manifest/handoff. No new Lean
module or full proof build is required for these tooling-only changes.


Follow-up final local gates pass: all66 Python graph/tooling controls,14 Node
pin controls, node syntax, bash syntax, both baseline checksums and
fragments/register checks. The real touched pre-gate logs PASS layers then
PASS build-touched with targets:none; no Lean process/build was invoked. The
negative integration uses the real checker on a newly added forbidden core
import and verifies no Lake invocation. Attribution reproduction is byte-identical
to the pinned107snapshot. Repo-relative source pins and exact candidate ledger
are committed in w0-followup-evidence.json; full logs remain manifested offgit.
No full-build/proof timing or RUNTIME_GATE_PASS is claimed. The original statement
graph queue and producer/trust/runtime/artifact waits remain unfinished. Host merge
runner deployment/adoption follows coordinator integration, not this local test.
