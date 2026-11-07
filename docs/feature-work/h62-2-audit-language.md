# H62 item 2: audit-language — resumed partial witness checkpoint

Batch `solidity-h62-2-20261106`, owner `audit-language`.
Repository `/workspace/solidity-lean`; branch
`codex/solidity-h62-2-20261106/audit-language`; frozen base
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
VM environment: `ccarenv_b64_Y2NhcmVudl9hNTQ3YjYwNzYwNjA4MTkxOGJhYmM3MGZiMTJjYzk0Mw`.
The exported `handoff.json` records the full committed head without a self-hash
inside this commit. This is an incomplete checkpoint, never completion of the
four-checkpoint assignment. The existing goal must remain unfinished.


## Coordinator finder portability corrections on 2026-11-07

The held head is `60f3df88d6dcb7b9dd1a31e9e8358e8348a01484`. Historical
receipt paths remain provenance/defaults; each receipt now also declares its
member relative to the evidence root. A shared resolver is used by verification,
export authentication and the other receipt readers. With `H62_EVIDENCE` set,
only that root is used: missing or corrupt relocated files fail, without reading
the historical absolute path. Absolute relative-members, parent traversal and
symlinks escaping the selected root are rejected. Identity, SHA256, reconstruction,
fidelity, source, axiom and witness predicates are unchanged.

The subsequent coordinator review found that gate-repair patches still used a
separate path join. `approved_revisions` now routes those reads through the same
containment resolver. Valid-byte file and directory symlink escapes are rejected
before opening outside patch contents; normal authentication still succeeds.
The regression demonstrates the old held implementation attempting that read,
then checks rejection through the actual gate-repair entry point.

The regression reproduces both reported failures using the held scripts, then
accepts both repaired flows while all legacy-root file reads are forbidden.
It also runs from relocated input data with setup-time legacy reads forbidden.
All 20 controls pass, including gate-repair escapes, corruption/missing receipts, no fallback, default
path behavior, containment and the five contiguous registration rows. This is
saved acceptance replay using source bytes matching actual recorded check hashes;
it invokes no Lean and establishes no new proof or full runtime gate.

The blank line before the FixedPoint registration row is removed. No Lean file,
statement, proof budget or existing gate predicate changes. The latest user
explicitly authorizes pushing the original lane branch after these corrections;
no default-branch push or publication is authorized. Original audit obligations
remain unfinished and are retained in `resume.json` and the exported handoff.

## Requested master merge resolution on 2026-11-07

Merged fetched master `df554535e9c8d308276a99ea23611c7d63ae5919` into the
existing lane parent `bdc5942ac81e4e6b733fc2a7ae7711df97a6c71e`, as explicitly
requested. The only conflict is the cast simplification in FixedPoint's
`tmod_between`. Retaining the local `rfl` cast equality preserves the earlier
portable gate repair; the complete resolved file equals its pre-merge lane bytes
(SHA256 `bcfc09c015e3d03927ad142617d8741ede4b9621786a6021bdfe69d3010ce66d`).
Every other upstream merge result is preserved. No new proof implementation,
statement, computational definition, axiom, exclusion or budget change is made
by this resolution. Existing upstream changes remain attributed to the merge.

Fresh official v4.35 checks pass for KeySort and the resolved FixedPoint module,
with explicit `-j1`, 8 GiB address-space cap, zero swap and 4 GiB reserve. Independent
read-only finder and skeptic reviews confirm all 18,532 previously unconflicted
index entries remain unchanged and no unresolved entries or markers remain.
This establishes the focused resolution checks, not full build/runtime acceptance
or a new timing comparison. The full audit remains partial; earlier waits persist.

`merge-resolution.json` and the external evidence directory's
`merge-fixedpoint-20261107/` record both parents, chosen blob, checks and reviews.
No history is reset and no push or default-branch merge is performed. The new
merge head is recorded by the exported handoff to avoid a self-reference in Git.

## Coordinator build-touched repair on 2026-11-07

The failed coordinator head is `683cab3cabe94700b2275f6f380c014e05c1e824`.
After fetch, current origin/master is `05d2c25872c4bb963a0ca7f605905e6e1e99eedc`,
already an ancestor of that lane head; no reset, rebase or new merge was needed.
This is the cleanup increment base, not a claim that the failed head was accepted.

Hash proofs now use their existing branch facts with `ite_true`/`ite_false`,
removing all references to the renamed `ite_eq_left`/`ite_eq_right` lemmas.
FixedPoint's remainder proof uses a local cast equality proved by `rfl` rather
than either version-specific named cast lemma. Only five proof bodies change;
all 102 theorem and 173 declaration headers remain unchanged. No statements,
computational definitions, axioms, exclusions or proof budgets change.

Both repaired files pass three fresh official v4.35 serial checks without
warnings, with the same 8 GiB address-space cap, explicit `-j1`, zero swap and
4 GiB reserve as three pre-edit checks. Median Hash time changes from 4.724 s
to 4.221 s (-10.65%); FixedPoint from 1.9136 s to 1.9167 s (+0.16%). Neither
crosses the greater-than-10% slowdown stop. Raw trials are retained; these focused
measurements do not establish full-build performance or a v4.24 gate pass.
The first attempted cast-lemma removal failed locally; that failed evidence is
retained, and no failed artifact is reused in final fresh checks.

A small committed gate-repair manifest pins the exact two source/patch hashes.
Full patches stay off Git. The checker, verifier and exporter accept this revision
only when explicitly selected, checking the exact path set, original frozen base,
strict patch context, source headers, options and current bytes. Historical H70
producer receipts remain unchanged. Set `H62_EVIDENCE` to relocate external patch
artifacts; no workspace-root path is hardcoded in the new validation script.

The repository pin remains v4.24 while the mandatory migration archive is v4.35.
The requested newer-name errors have been removed without choosing a different
build or reusing old-toolchain caches. The global documentation-path check finds two unchanged fixture-placeholder
references in a different audit lane; they are recorded, not repaired here.
The coordinator must rerun its actual gate;
no coordinator/full/runtime pass is inferred from local v4.35 checks. Original
51-certificate coverage, remaining queue, version/fidelity waits and goal remain
unfinished; this repair adds no new witness theorem.

## Resumed at accepted master on 2026-11-07

The latest user explicitly requested re-baselining and continuation. The original
lane fast-forwarded from `e8801a56d985202d80a12b5e8f2ea6525d8bb239` to accepted
master `4f0a2d6abe3a920d8c5a20c8c06d373a1014824d`; original frozen base and all
lane commits remain ancestors. Earlier retirement/H44 sections below are history.
The original goal is incomplete; no goal was created/reset or API state invented.

Under H82, the exact two authenticated H70 producer proof patches are now applied
locally. All 102 theorem headers/section contexts and declaration headers remain
unchanged. FixedPoint and Hash/CollisionBound both pass bounded official v4.35
checks. The checker retains original frozen-byte guards and permits only exact
checksum-authenticated postimages when explicitly supplied; it has no generic
snapshot override. Other changed core sources still fail closed.

There are now 51 kernel-checked full-leading-telescope certificates: the previous
12, three additional catalog statements and all 36 FixedPoint core statements
with leading arguments. The same concrete unsigned 8-bit, zero-digit type supplies
the intrinsic values and their proofs, with actual 255+1 overflow and a nonzero
divisor. Closed `Fx.solc_lossy` has no leading hypotheses and stays accounted for
as an uncovered conservative candidate; no statement was dropped. The 4,146-row
frozen census now has 4,095 uncertified candidates, pending interface classification.
These are feasibility results, not compiler totality or solc code generation.

Acceptance verifies actual target-import bytes against the frozen source or exact
approved proof postimage, plus current witness-module hashes, axiom lines and exact
association markers. All 51 pass; reassigned witness controls are rejected. Both
new and existing mismatch commands reject the wrong imported telescope. Witnesses
introduce no axioms, sorry, native evaluation shortcuts or increased proof budgets.

The ownership input defaults to a repository sibling and can be relocated with
`H62_COORDINATOR_INPUTS`; its required SHA256 is unchanged. Regeneration produces
the exact original census bytes. New scripts avoid a fixed VM workspace root;
absolute paths in saved manifests remain required evidence provenance.

The next Source/Hoare attempt stops before Lean: accepted master's
`Source.Machine.St` adds an imported resource cursor field absent at the frozen
base. No replacement premise, state definition or unauthorized repair is invented.
A compatible version/fidelity artifact remains a typed producer dependency. The
Syntax.Raw report remains pending rather than a newly observed local failure.

Actual tools: Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`,
and Lake 5.0.0-src+eb6cafb. Fresh bounded KeySort passes (2.413 s prerequisite run;
1.413 s witness import run). Every Lean invocation uses explicit `-j1`, no swap,
a bounded address-space cap and a 4 GiB available reserve. Existing source proofs
were not refactored for performance; no comparable passing old migration baseline
or full-build timing result is claimed.

Evidence is under the externally supplied evidence directory's
`resume-20261107/`: exact re-baseline record, applied receipts, prerequisite and
witness checks, fidelity/negative acceptance, byte-identical census, static gates,
actual versions and independent finder/skeptic reviews. Layer, generated-root,
fragment, documentation-path and whitespace gates pass. Full runtime/Bridge/Solkey
checks remain pending; the repository launcher still selects v4.24, whereas this
lane must use the pinned official v4.35 archive. No RUNTIME_GATE_PASS is claimed.

This is the required fresh-thread handoff after five work items, on the same
original VM/branch/goal. `resume.json` retains every open queue/backfill item and
wait. No replacement goal/thread is self-launched and no completion is requested.
The full assignment remains partial: semantic coverage, remaining witnesses,
compiler success/failure/gas/fork obligations, producer routing and full gates.

## H44 reviewability split — historical packaging

The generated 389-file scope/ownership inventory is preserved off Git at
`/workspace/h62-audit-language-evidence/h44/scope-manifest.full.json`.
The tracked retirement `scope-manifest.json` is now a small pointer with the
absolute path, size and SHA256, plus original scope metadata. The deterministic
`scope_manifest.py` generator reconstructs the exact original bytes from the
pinned frozen census. The full inventory travels in the portable evidence
archive, whose internal and external checksums authenticate it.

This cleanup adds no proof or scope and changes no Lean modules, theorems, gates
or budgets. The worker remains retired; only the requested packaging correction
is authorized. The branch already contains coordinator merges. Export records
both the original frozen base and the cleanup increment base; `increment.patch`
and the incremental bundle apply to the latter. The cumulative `original.patch`
contains only this lane's owned paths relative to the frozen base.

Exact scope reproduction and whitespace checks pass. The global documentation
checker fails on five unrelated references whose citing files equal the cleanup
parent; none is changed here. The failures remain recorded in H44 split evidence.

## H82 retirement — historical, superseded by explicit 2026-11-07 resumption

The human explicitly stopped this worker and assigned the handoff to
`solidity-sol2-20261104/numeric-literals`. No further proof implementation,
continuation, replacement goal or VM is authorized. The final retirement commit
adds handoff documentation and export tooling only. All original Lean sources,
the four audit Lean modules and their prior 12 joint certificates are unchanged.

The pending command to apply two proof-only migration overlays and extend the
checker was rejected by automatic approval review after the stop instruction.
It did not execute. Zero patches were applied and no new Lean checks were run.
Earlier source receipts remain authenticated, unapplied partial prerequisites.
H82 withdraws earlier exact-file agreement waits for statement-preserving edits;
validation and authoritative producer-routing obligations remain for the successor.

The tool inventory exposes no pause-goal operation. Its only goal mutation is
`codex_goals_stop_goal(outcome: complete | blocked)`, which cannot express PAUSED;
no false transition was requested. The existing goal remains incomplete, and the
worker is stopped. Coordinator must apply the requested PAUSED state using its
available control. No accessible H71 push authorization is established, so no
branch was pushed; the original no-push rule remains effective here.

Mandatory authenticated handoff inputs are tracked under
`tests/h62/item2/audit-language/retirement/`: complete original rendered prompt,
full original work/backfill queue, small authenticated scope pointer (full
generated 389-file inventory off Git under H44),
retirement state/open obligations/waits and their SHA256SUMS. Portable evidence
contains actual coordinator inputs and current/historical proof/scan logs,
without compiled caches or extracted toolchain. Export records final base/head,
branch, clean status, cumulative patch and bundle, archive hashes and exact gates.
Earlier sections below are historical and retain their original limitations.

## Subsequent H70 partial deliveries and remaining-domain refinements

Current follow-up parent: `c2ffe26194e661f11b6ef4673090fdc97021ed74`.
The existing generic classifier is unchanged. A separate, narrow source pass
records 418 refinements across 279 rows: 212 closed primitive denotations,
60 already-known generic primitive values, 137 fixed-point values and nine
nested address subtypes. It resolves 221 previously unknown binder domains
and enriches 197 data domains with their existing range constraints. This
makes 139 additional rows source-resolved: current totals are 3,664 source
rows resolved and 482 still unresolved, from the same 4,146 candidates.
Zero exclusions, signature changes, owner changes or new witnesses occur.

The facts are read from frozen `AST`, `Semantics`, `ContractWorld` and
`Language/FixedPoint` declarations. The closed bool branch stays Bool;
uint/int retain their `inRange` subtypes; generic primitive values keep
branch uncertainty. Address retains both its outer 160-bit bound and nested
word range; it is not silently replaced by Roadmap's Fin address. Fixed-point
values retain `t.inRange v = true`. Every actual argument and proof component
still needs a simultaneous witness. These source annotations establish no
inhabitance, imported semantic telescope or compiler success theorem.

The pass requires the exact reviewed baseline SHA256, recomputes the frozen
census, uses exact family/alias evidence and tracks lexical namespaces rather
than dotted theorem-name parents. It refuses arbitrary suffix methods,
unsupported root namespace blocks, function-returning-address domains,
wrong/unbound receivers, qualified local shadows and near-prefix namespaces.
Generic `p.Denote` enrichment additionally requires existing evidence for the
exact frozen family and an explicitly primitive-typed receiver. Active-open
resolution remains outside this narrow pass; ambiguous cases stay pending.

### Partial owner receipts

The two received artifacts are preserved off Git in `h70-received/` and
registered in `tests/h62/item2/audit-language/received-overlays.json`:

| Component | Latest reported ticket | Advertised SHA256 | Source-only review |
|---|---|---|---|
| Hash/CollisionBound | `a3f49ee0ec1829e63022c90194048d5a1ffe0d22` | `3aebc61f1a1979d4e36d669e3c33f5ae8c848d38a3ca0574c62329bdc154bbff` | Seven strict hunks; postimage prefix `092971eda`; 65 theorem headers unchanged. |
| Language/FixedPoint | `479f6e0079409a1867483dbffe5051932b8fa754` | `a3cbeea6c8a243df761166dd558825898f2bbda8c8fa7d8a74850cd27cb8ad82` | Eleven strict hunks; postimage `0a4d4cfc2a241fa46dd1183c895f9ac54d18beef`; 37 theorem headers unchanged. |

The Hash artifact's earlier ticket was `78c110f83dc1a30700acd1b5bd34b19f61da6ccd`;
its reported source remains `2a18afcdba00a85645b0b3079704f78ffcd78860`.
FixedPoint's reported source is `d8e1d9721455d3671882f19aa7155fbbd2d91415`.
Reported commit identity is distinct from local Git-object verification.
Both artifact bytes now match the advertised SHA256. Three errors in the
first local FixedPoint transcription were corrected only after the recovered
bytes matched that exact digest; the initial `f686…` capture remains unchanged
as negative-control evidence. This was a local capture correction, not a
repair to owner source or an accepted fuzzy patch.

`overlay_review.py` reconstructs strictly in memory, checking the allowlisted
path, original/postimage Git blobs, every hunk position/count/context, theorem
headers/captured section variables, declaration headers and source trust/options.
It never writes the postimage, applies a patch or invokes Lean. The original
files remain byte-identical to the frozen base. All 102 source theorem
headers remain unchanged; elaborated fidelity and proof validity are pending.

Host receipt paths and journal delivery do not establish owner agreement,
validation, new original-file permission or cut-over. Both producers say full
migration/affected gates remain pending. The Hash relay additionally reports
`Solidity/Syntax/Raw.lean` pending; its migration owner is recorded from the
pinned snapshot. No new Raw failure or passing gate is claimed by this worker.
Internal worker obligations now use the actual audit-language owner key,
with no separate relay requested, instead of descriptive pseudo-destinations
such as “audit-language after prerequisite delivery.” Producer-resolution
information for the same 262 exact paths remains a coordinator request.

### Continuation validation and remaining work

- `overlay_review.py --registry tests/h62/item2/audit-language/received-overlays.json
  --output <evidence>/h70-overlay-review-final`: source-only pass, 102 unchanged
  theorem headers, zero applied overlays and Lean validation explicitly pending.
- `refine_remaining.py` final output is `h70-remaining-reviewed/`; the replay
  `h70-remaining-reproduced/` matches classification, unresolved-domain and
  summary files byte for byte. Exact commands/timings/resources are in
  `h70-remaining-generation-gates.json`. The earlier `h70-remaining-final/`
  is a historical pre-hardening snapshot, marked by `NOT-AUTHORITATIVE.json`;
  use `h70-remaining-reviewed/` for the current result.
- `continuation_acceptance.py` passes all 4,146 row identities, preserved
  owners/signatures/conclusions, frozen fact hashes, branch/subtype/shadowing
  guards and ten corruption/fidelity controls. The controls reject wrong
  old/new blobs, context drift, truncation, extra files, traversal, changed
  premises, changed budgets, forged owners and unauthenticated transcription.
  Evidence: `h70-continuation-acceptance.log` and its `negative-controls.json`.

This continuation adds no Lean module or theorem and runs no new Lean gate.
The previous twelve joint certificates are unchanged. The generic source
classifier, all originals, toolchain and proof/resource budgets are unchanged.
The measured source pass/replay is separate from a Lean before/after benchmark;
full affected build/timing gates remain pending with the owners.

The four continuation items are authenticated partial-receipt review,
remaining-domain/feasibility annotations, corruption/shadowing controls and
repeatable validation/handoff. Finder and skeptic reviews are read-only,
without edits or Lean jobs/servers; confirmed hardening requests were fixed.
The original four-checkpoint goal remains unfinished. Continue imported
semantic classification, joint witnesses and meaningful supported-program
compiler success/failure/gas/fork obligations after validated prerequisites;
retain all unclassified statements/owners and full gates as typed blockers.

## H70 continuation: exhaustive source classification, semantic boundary retained

H70 accepted both migration owner relays. Their repairs remain waits, not
permission for this audit lane to edit originals. `relay.sh` is host-only;
its absence on this VM is not an installation task or blocker.

Every one of the 4,146 frozen source candidates now has a per-statement source
classification, with zero omissions/exclusions and zero parse errors. Records
include explicit and leading-result binders, source-declared proof/data sorts,
Type-valued certificate fields, shared-variable dependencies, section context,
include/omit/open history, definition evidence and separate ownership roles.
Private declarations remain included (194 private, 3,952 public/protected).
This classifies a conservative source superset; it does not declare every
candidate an interface or turn source analysis into semantic certification.

3,525 rows have source classifications for all header and referenced-context
domains. 621 rows retain inferred/ambiguous domains explicitly in
`h70-classification-final/unresolved-domains.json`. Section include/omit,
auto-implicit parameters, actual private names and full imported telescope
fidelity remain semantic obligations even for source-resolved rows. No new
joint witness, global-premise inhabitance or totality claim was made.

Known source-reviewed contract roles retain global laws separately from
per-input feasibility: `PublicCorrectness`, Type-valued `Validator`, bounded
`PaddingCorrect`, associated-code `MacroRefinement`, and the normal
Source/model obligations. For example a validator's universal soundness law
must coexist with its concrete validation-success, admission, well-formedness
and profile premises; a proof that its structure is inhabited does not supply
the whole tuple. Source field defaults and predicate-valued data fields are
not treated as proof premises. Ambiguous symbol identities remain unresolved.

| Ownership classification | Files | Declarations |
|---|---:|---:|
| One documented live scope owner | 127 | 1,270 |
| Cleanup writer only; producer unresolved | 18 | 105 |
| No documented live producer reservation | 244 | 2,771 |

There are zero distinct-owner conflicts. The two DirectRuntime claims name
the same owner and are deduplicated. Cleanup and migration reservations never
stand in for a live producer, and unclaimed paths never default to `master`.
The 262 exact paths needing authoritative routing are in
`h70-classification-final/owner-routing.json`; the small in-scope request is
`tests/h62/item2/audit-language/owner-resolution-request.json`.
These are routing classifications, not new write authorization.

The classifier reads frozen Git objects (including dependency definitions for
name/sort evidence) and requires the external census to equal a fresh
canonical census from the frozen maps, declarations and checksum-verified
ownership snapshot. It rejects altered signatures, forged owners and missing
candidates before creating output. It does not compile or edit dependencies.

H70 validation:

- `classify.py --census <evidence>/census-final/census.json --output
  <evidence>/h70-classification-final`: exit 0; 58.753 seconds, 732,300 KiB
  peak RSS. Exact command/outcome: `h70-classification-gate.json`.
- `classification_acceptance.py` against that report: exit 0, all 4,146 IDs
  reconciled, zero exclusions, and three provenance attacks rejected.
  Evidence: `h70-classification-acceptance.log` and its `negative-controls.json`.
- Independent deterministic regeneration: exit 0, 61.475 seconds, 735,008 KiB;
  classification, owner routing and unresolved-domain files match byte for
  byte. Evidence: `h70-reproduction-gate.json`.
- The source-tool repeat was 4.63% slower; this is not a Lean before/after
  regression measurement. No existing proof implementation or statement was
  refactored. Full affected build/timing gates remain pending.

Finder and skeptic independently reviewed this continuation without edits,
Lean jobs or servers. Confirmed findings were fixed: default values falsely
looked like proof fields; multiline proof fields were truncated; ambiguous
names could select an unrelated certificate; external census owners/signatures
were trusted; ASCII iff could be mistaken for a leading arrow. Regressions
exercise these cases, dependent validator laws, existential conclusions,
owner-role deduplication and the actual provenance attacks. Both final
reviews pass for the source-classification checkpoint only. Initial failed
preflights are retained as logs and are not counted as passing gates.

The four H70 work items are source telescope classification, corrected owner
roles/routing, mixed global/per-input contract evidence, and deterministic
acceptance/negative controls. The original goal remains unfinished. Next work
requires the named migration prerequisites and authoritative producer routing,
then the 621 unresolved source domains, imported semantic fidelity, remaining
joint witnesses, compiler success/negative controls, gas/fork boundaries and
all final gates. The prior twelve certificates and all four Lean files remain
unchanged; no Lean check or full runtime gate is newly claimed by this
Python/documentation continuation. H70 evidence is off Git and enters the
updated exported patch/handoff/checksum manifest.

## Work completed in this thread

1. Recovered the older clean checkout without discarding work; fetched master,
   verified the exact base is an ancestor of published origin/master, and
   created the assigned isolated branch at that base under the writer lock.
   All five coordinator-input SHA256 checks passed. `get_goal` is not exposed;
   the coordinator explicitly says this optional absence is not a blocker.
2. Built a deterministic conservative source census and reconciled every named
   theorem/lemma command in the two module-map areas: 389 resolved files,
   4,146 declarations, no unresolved first-column file references or scan
   errors. Duplicate map rows share one path/declaration ID. This includes
   Bridge, controls and private declarations rather than silently excluding
   them. It is a source superset, not an elaborated interface classification.
3. Added feature, lattice and checked-arithmetic witness/client modules plus
   twelve full-telescope certificates. `hypotheses_of%` derives the existential
   input/proof tuple from the imported constant's exact leading forall binders;
   dependent hypotheses use the same local inputs. A checked command compares
   each certificate type to its indexed target and emits a canonical receipt.
   The wrong-target Lean guard and an in-memory index-reassignment attack both
   reject. No independent-inhabitant argument is substituted for a tuple.
4. Added actual ABI one-boolean decoding with both values, nonzero output,
   malformed/truncated reverts, insufficient fuel and allocation panic. The
   companion success requirement rejects always-revert and always-fuel-error
   **decoders**. This is backfill, not compiler totality or gas/fork coverage.

Four useful work items have been handed off, meeting the requested 3–5-item
fresh-thread interval. Do not self-launch a replacement goal/thread. Resume
this exact VM/goal/branch through the coordinator after prerequisite delivery.
Further independent backfill and all original queues remain authorized.

## Checkpoint status and uncovered obligations

| Frozen checkpoint | Status | Remaining work |
|---|---|---|
| 1. Exact signatures and owners | Partial | Raw frozen signatures, file hashes, complete source prefixes and scope candidates are recorded. Complete Lean name/signature verification, distinguish interface hypotheses from controls/parameters, and confirm every live owner. |
| 2. Joint hypothesis witnesses | Partial, dependencies blocked | Twelve kernel certificates are mapped exactly once. 4,134 source declarations have no certificate; not all have yet been classified as hypothesis-bearing interfaces. No universal coverage claim. |
| 3. Supported-program success | Blocked | Source/compiler totality, reject-all/always-revert compiler controls and observable failure/gas/fork boundaries remain required. ABI decoder evidence does not discharge these. |
| 4. Fidelity and witness census | Partial | All twelve mapped receipts and source-signature hashes reconcile. Every uncovered source declaration and owner candidate is reported; full elaborated census/verification remains pending. |

`tests/h62/item2/audit-language/witness-index.json` records the twelve targets.
`Unmodelled` is an inhabited diagnostic structure, not a compiler producer.
Feature exclusion feasibility is per input. No inhabited global compiler
premise structure has been established by this checkpoint.

No weakened/vacuous frozen statement has been established by this partial
review, so there is no theorem-repair escalation or interface edit. Compilation
failures below are migration dependencies, not mathematical counterexamples.
Future confirmed vacuity must emit the required single `ESCALATE:` line per
fully qualified theorem with evidence and repair options, preserving the blocker.

## Pinned runtime and gates

Official archive: `lean-4.35.0-linux.tar.zst`; SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Actual Lean: `4.35.0`, release commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
Actual Lake: `5.0.0-src+eb6cafb (Lean version 4.35.0)`.
No root toolchain file or v4.24 per-master cache was used for the new checks.
Lean MCP tools are not exposed; focused checks use explicit serial Lean `-j1`
with `--tstack=131072`. Full `./run-lean.sh` remains a required pending gate.

All final focused checks acquire the repository writer lock, reread frozen
source bytes and use fresh off-Git libraries. `check.py` chooses a virtual
memory cap below both 12 GiB and current cgroup/host available memory minus
4 GiB reserve and 256 MiB headroom. It monitors the reserve every 0.1 seconds,
requires no host swap, kills only its own process group on reserve/300-second
stops, and records the failed command. No `systemd-run` was used.

| Command/gate | Outcome and decisive evidence |
|---|---|
| Pinned `lean -j1 --tstack=131072 Solidity/KeySort.lean` | Exit 0, 1.521 s, 507356 KiB peak RSS; `toolchain/keysort-v435.json`. The final guarded focused sequence also rebuilt KeySort successfully. |
| `python3 scripts/h62/item2/audit-language/acceptance.py` | Exit 0: 389 files, 4146 reconciled declarations, kernel certification false; `acceptance-final.log`. |
| `check.py --lean <pinned>/lean --output <evidence>/final-reviewed` with all four audit files | All nine original/helper compilation records exit 0; `final-reviewed/checks.json`, per-file logs and `final-reviewed-command.log`. No warnings in final helper logs. |
| `verify.py --census <evidence>/census-final/census.json --checks <evidence>/final-reviewed/checks.json --output <evidence>/fidelity-final` | Exit 0: 12 checked full-telescope certificates, 4134 source declarations uncovered; `verify-final.log`. |
| `verify_negative.py` with the same census/checks | Exit 0: wrong-witness reassignment rejected; `verify-negative.log`. |
| `node scripts/check-layers.mjs` | Exit 0: 857 core modules, zero reaching elaborator or checked-parser adapters; `layers-final.log`. |
| `bash scripts/coord-tools/register.sh --check` | Exit 0; `roots-final.log`. No registration applied. |
| `bash scripts/coord-tools/fragments.sh --check` | Exit 0; `fragments-final.log`. No fragments generated. |
| `check.py ... Solidity/Source/Hoare.lean` | Exit 1 on unchanged Hash/CollisionBound dependency; `hash-final-blocker/checks.json`. |
| `check.py ... Solidity/Language/FixedPoint.lean` | Exit 1 on unchanged fixed-point proofs; `fixedpoint-final-blocker/checks.json`. |
| `./run-lean.sh`, Bridge validation, final SolKey check and full acceptance | Pending; no full-gate or RUNTIME_GATE_PASS claim. |

Exact absolute commands, hashes, resource observations and exits are in the
JSON records. The early unavailable `/usr/bin/time` attempt and initial
helper/parser failures were corrected, not counted as passing gates. Early
focused records predate the improved cgroup guard; only `final-reviewed` is
used for final certificate acceptance.

No existing original file was refactored or rechecked on a changed statement.
There is no valid same-resource before/after full-build timing baseline yet;
no speedup or <=10% regression claim is made. Per-file timings are saved.
A comparable whole affected validation/timing gate remains pending with the
migration prerequisites. Stop and escalate any later >10% slowdown.

## Independent reviews

Read-only finder and skeptic used no Lean job/server and made no fixes. Both
identified attributed declarations, equation/where boundaries, mutual scope
and root-name handling; these were fixed and independently reconciled. They
also found cgroup reserve, fresh-library, timeout evidence and witness-target
association gaps; all were fixed. The final finder and skeptic confirmed all
twelve checked receipts/current hashes and reported no material artifact bug.
Their review remains limited to this partial checkpoint, not full assignment
acceptance. Summaries are saved in `<evidence>/reviews.json`.

## Typed blockers and owner handoff

See `tests/h62/item2/audit-language/owner-tickets.json` for self-contained exact
file requests and reproduction evidence. The Hash migration owner is
`solidity-h62-6-20261106/migrate-hash`; its unchanged file fails at lines
407, 660 and 680 under the pinned release. The language migration owner is
`solidity-h62-6-20261106/migrate-language`; unchanged FixedPoint fails from
line 152 onward. Existing originals remain read-only. No failure artifact
is reused and no proof/premise is weakened to make these pass.

The saved tickets request coordinator delivery of owner-approved migration
prerequisites while preserving frozen statement identity. `relay.sh` is absent
in this checkout; tickets are saved for retrieval, not falsely reported sent.
Migration overlay ownership never replaces live producer ownership. No H55
source-relation or final-theorem work was duplicated or edited.

A fresh thread must first reread this handoff, the unchanged frozen prompt,
owner tickets and all gate records, then continue the 4,134-declaration backlog
and supported-program/compiler/gas/fork obligations. Any registration requires
owner approval; a proposed optional test-library/map fragment is supplied in
`tests/h62/item2/audit-language/registration-fragment.md`, not applied.

## Artifact paths and trust boundary

All bulk data and compiler products are outside Git under
`/workspace/h62-audit-language-evidence/`:
`original.patch`, `handoff.json`, `SHA256SUMS`, `census-final/`,
`fidelity-final/`, `final-reviewed/`, both final blocker directories and
review/runtime/gate JSON logs. `export.py` regenerates the patch and checksum
manifest from the committed head. The manifest excludes extracted toolchain
contents (the verified original archive is hashed) and intermediate `.olean`
libraries; final checked source hashes and all proof logs remain included.

The census/ownership matching, source hashes and attack test are external
Python checks. Lean kernel checking establishes only the explicitly compiled
witnesses/ABI facts. No external EVM/solc equivalence, global compiler producer,
full success contract or uncompiled theorem is claimed. New source counts:
zero `sorry`, zero `axiom` declarations, zero `native_decide`, no raised proof
budget. Standard imported axioms are printed; telescope certificates use at
most `propext`. No merge, push, publish, PR or deployment was performed.

## H151 historical evidence gap

**UNVERIFIABLE:** the original frozen ownership snapshot identified by SHA256
`7f5d40d46d386ed17731db55ed87f0564f5c9e667bddee00c0f12b28772f9cce`
and the complete historical portable evidence packet could not be recovered from
authenticated intake. The historical ownership-bound census and its full evidence
replay remain unproven. Current registry files and other snapshots do not replace
those bytes. H151 removes recovery of this historical packet from producer waits;
it does not turn any historical claim into a passing gate.

Fresh source and kernel checks may proceed using available Git objects and
explicitly identified current inputs. Such checks must distinguish current
ownership from historical ownership and must not be credited as reproduction of
the missing packet. Preserve the original strict checksum refusal in the census
checker. Existing checked witnesses retain only their individually recorded
scope; full interface coverage, simultaneous witnesses and final acceptance remain
open. Evidence belongs in the private coordination repository under H145.

Fresh H151 recovery is available through
`scripts/h62/item2/audit-language/source_only.py`. It reuses the original frozen
Git scanner and map areas, yielding 389 files and 4,146 conservative source
candidates. It assigns no historical owners, certifies no witnesses and asserts
no historical replay. Deterministic reproduction and output-refusal controls
passed. Both independent read-only reviews accepted these boundaries; a dangling
symlink refusal and exclusive output creation address the skeptic's robustness
suggestion. This is source recovery, not elaborated interface coverage or final
acceptance. Bulk output and validation evidence remain private under H145.
