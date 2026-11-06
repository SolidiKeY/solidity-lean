# H62 item 4: generic StorageOps controls

Status: **blocked, full assignment unfinished**. Checkpoint 1 now delivers a
reviewed census and complete source-contract classification of all 230 original
files and 6,036 declarations, with deterministic acceptance. It does not
claim a generic StorageOps proof, semantic correspondence, migration, runtime
gate, or acceptable before/after checking-cost delta.

Branch: `codex/solidity-h62-4-20261106/generic-storageops`.
Exact frozen base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Repository: `/workspace/solidity-lean`. The initial clean `work` branch pointed
to `6cf853aea`; fetching origin/master supplied the missing base. Its ancestry
was verified with `git merge-base --is-ancestor BASE origin/master` before
creating the assigned branch. No old checkout changes were discarded.

## Scope and census

The only repository additions are in the two assigned test/script directories
and this document. All 230 original Backend/StorageOps modules remain byte-for-byte
identical to the base. There are 6,036 explicit declarations across those files.
The 84 `*Controls` files contain 1,623 theorem declarations: 1,007 public and
616 private. These are **candidate cases including proof helpers**, not 1,623
independent semantic cases. No declaration has been silently excluded.

The full original declaration inventory includes each source path, line,
qualified source name, visibility, kind, exact source header, ambient binders,
contextual statement SHA256 and declaration SHA256. These are source pins,
not kernel-elaborated type hashes. File SHA256 pins also preserve definitions,
imports, options, observations, proofs and comments. A conservative namespace,
section and mutual-block scanner masks nested comments and strings. Eight scanner
regressions include binders, mutual scope, proof-only drift, proposition-level
let assignments, keyword boundaries and malformed input. Current-corpus independent sweeps found no missed declaration starts.

Current format-2 full inventory stays off git under H44:
`/workspace/h62-generic-storageops/evidence/inventory.json`.
SHA256: `30e9490cd6efae5027c910b827a675e3afdc8b614fd462a27b3e0debb4f8af90`.
The prior format-1 inventory is retained as `evidence/inventory-v1.json`, digest
`fd5361469fe3e59603d8e1612e5abb306c586ad1a2f97a2576ab7c178179f336`.
Format 1 truncated 105 theorem headers (72 family laws and 33 public control
claims) at proposition-level `let` assignments. Format 2 retains the full
contracts and **every** old hash in `legacy_v1_statement_sha256`. Acceptance
reconstructs all 6,036 old rows and checks the exact prior inventory digest.
No underlying Lean statement or declaration bytes changed.
The compact [manifest](../../tests/h62/item4/generic-storageops/inventory-manifest.json)
pins all 230 files, totals and full inventory digest. Regenerate with:

```sh
python3 -B scripts/h62/item4/generic-storageops/census.py \
  --output /workspace/h62-generic-storageops/evidence/inventory.json
python3 -B scripts/h62/item4/generic-storageops/accept.py
```

Acceptance independently compares the current file set and each file's bytes to
`git ls-tree` and `git show` at the frozen base. It fails on source or inventory
drift; `--write` only regenerates the manifest and never authorizes changing the
base or passing changed original statements.

## Audit 9/11/16 disposition

The coordinator's verified audit has SHA256
`31ab16906906a9b22fd28700aacc72d2ee0ffe81cea723ae209eb28e5299286a`.

| Item | StorageOps application and remaining obligation |
| --- | --- |
| 9, parameterize twin controls | Applicable method: preserve intrinsic element/path/operation types and all observations while sharing a law. The named Passes/PrimitivePackets/InternalFlow/MemoryCopies examples are other families. No ownership is claimed over them. Every row now has a parameter-regime disposition; all runtime/result quantifiers are retained. Proved semantic equivalence and exact-instance migration remain checkpoint 2 work. |
| 11, shared lemmas and fixtures | Applicable method: e.g. repeated private names `graph` (48), `hash` (48), `locations` (46), `ix` (43), `one` (40), `zero` (39), `run` (36). The classifier additionally records 435 exact source-template repeat groups (1,535 declarations), erasing only the declaration name; these are source-backed helper candidates, not proof of equivalent resolved types. No helper extraction or shared HeapRepr/AllocatorRepr replacement is claimed. |
| 16, table plus one semantic lemma | Applicable method to per-case StorageOps controls. Tables must retain negative/refusal and retained-versus-live observations and accompany an intrinsic parameterized semantic law. No `decide` table substitutes for that law. Yul Raw/vector generation remains H55; no generator is duplicated here. |

Every declaration has all three audit dispositions plus evidence: parameter
regime for item 9, exact source-template group or unique-template retention for
item 11, and whole control-claim versus supporting-declaration treatment for
item 16. These are complete applicability/preservation dispositions, not proved
semantic equivalence groups or selected original migration patches. Those are
checkpoint 2 obligations, pending owner/dependency gates.

## Complete source-contract classification (H70)

The full additive classification is `evidence/semantic-classification.json`,
SHA256 `ea9995ef1ff96bcea13c16b5154127a6c8cfc16fa0cbdabddbdf9d5d9873e945`.
The 22 MB bulk artifact stays off git under H44. The tracked
[classification manifest](../../tests/h62/item4/generic-storageops/classification-manifest.json)
pins it; the manually enumerated
[domain map](../../tests/h62/item4/generic-storageops/semantic-domains.json)
covers exactly all 230 original files, including the declaration-free
`SourceSelfCopy` compatibility import.

| Declaration disposition | Count |
| --- | ---: |
| Public control claims | 1,007 |
| Private control claims (including fixture lemmas) | 616 |
| Control fixtures and adapters | 3,214 |
| Other family proof claims | 922 |
| Other family definitions and adapters | 274 |
| Interface/type definitions | 3 |
| **Total original declarations** | **6,036** |

All 1,623 original control claims are retained as whole contracts; tuple/list
fields and conjunctions are not padded into independent case counts. Each row
retains source identity, exact formal parameters, ambient binders, result type,
all four hash pins, and source documentation. All 3,491 nonclaim definitions
retain their full original definition text, including endpoint fields. These
JSON audit records are not a replacement untyped semantic model.

The classification records exact proposition structure and meaning: quantified
contracts, local let bindings, generated-value or ordered-observation equalities,
partial outcomes, graph observation absence, explicit compiler refusal/revert,
coverage/bounds, predicate facts and distinguishing inequalities. It keeps
implication premises, disjunction alternatives, equivalence sides and negations
separate from positively asserted outcomes. In particular `some none` is a
present outer result; `readLive = none` is an unavailable graph observation; a
composed map/bind returning none is not automatically compiler refusal. Exact
origins remain in the stored contract where no narrower interpretation is
justified. All 309 local-let nodes are traversed. Runtime parameters are never
replaced by finite table enumeration.

The per-file scope taxonomy covers 34 intrinsic-graph, 47 numeric-access/trace,
90 represented-composition, 28 structured-target, 24 represented-target-adapter,
two mixed-control, two published-compiler-fragment, two reached-endpoint and one
compatibility-import modules. These are broad layer boundaries; the exact
per-declaration contracts remain authoritative. No Source, bytecode, gas, world,
rollback or cryptographic closure is inferred from lower-layer facts.

```sh
python3 -B scripts/h62/item4/generic-storageops/accept_classification.py \
  --output /workspace/h62-generic-storageops/evidence/semantic-classification.json
```

This acceptance runs frozen-tree identity checks, eight scanner regressions and
13 classification regressions, validates all 6,036 declaration identities and
contracts, refuses missing/duplicated cases or lost audit fields, checks the
classification/domain manifests, and reconstructs the complete old inventory.
It establishes complete source-contract inventory classification. It does not
establish parameterized semantic equivalence, a typed Lean fixture table,
exact owner-approved original instances or any runtime/proof/timing gate.

## Validation and resource evidence

The coordinator supplied five input files under `/workspace/h62-coordinator-inputs`;
all five SHA256 values match `sha256.json`. The later coordinator instruction
requires the exact official `lean-4.35.0-linux.tar.zst` archive with SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
It was downloaded and verified before extraction outside git. The preinstalled
4.24.0 toolchain was not invoked for migration checks. The definitive final
reproduction explicitly disables local artifact-cache reads and writes; earlier
probes used separate build directories but did not explicitly disable all local
cache reads, so those earlier probes alone do not establish cache isolation.
No tracked toolchain file or module registration was edited.

Actual versions:

```text
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
```

The VM has a 16 GiB cgroup memory cap and zero host swap. Checks hold
`/tmp/solidity-lean-feature-groups-20261025/writer.lock`, set
`LEAN_NUM_THREADS=1`, pass explicit Lean `-j1 -M12288 --tstack=131072`,
and use the supplied guard with a sampled 12 GiB process-group RSS stop and 4 GiB
available-memory reserve. The hard cgroup cap remains the preprovisioned 16 GiB; the 12 GiB group stop
is sampled, not a new kernel memory limit. No systemd scope is created. The build configuration
and products live outside git in separate v4.35 directories. `enableArtifactCache = false` and explicit Lake cache environment settings
disable the local artifact cache in the definitive reproduction; `--no-cache`
also disables package cache downloads. `XDG_CACHE_HOME` is isolated. Earlier
probe configurations did not disable the local cache explicitly. No Lean MCP tool was
exposed; serial CLI checks used the official toolchain. No runtime-pass label
is inferred from provisioning or from the prerequisite.

| Check | Result / evidence |
| --- | --- |
| Eight census scanner tests | Pass, exit 0. |
| H70 complete classification acceptance (13 classifier tests plus frozen source/pin validation) | Pass, exit 0; `evidence/classification-acceptance.log`. |
| Frozen-source deterministic census acceptance | Pass, exit 0; all 230/230 original file hashes match the exact base. |
| Pinned v4.35 KeySort | Pass, exit 0; 1.517 s, sampled peak group RSS 519,495,680 bytes. `evidence/keysort-v435.log{,.json}`. |
| v4.35 `lake ... --no-cache build Solidity.Backend.StorageOps.OperationFamilies` | **Fail**, exit 1; 20.011 s, sampled peak group RSS 1,657,294,848 bytes. `evidence/dependencies-v435.log{,.json}`. |
| Reproduction driver, isolated fresh output | KeySort passes (1.513 s); dependency build **fails**, driver exit 1 (18.970 s, 1,667,461,120 bytes). `evidence/reproduction-driver.log`, `reproduction/dependencies.log{,.json}`. |
| Corrected driver, freshly extracted verified archive | KeySort passes (1.514 s, 519,446,528 bytes); dependency build **fails**, driver exit 1 (19.211 s, 1,666,662,400 bytes). `evidence/final-keysort.log{,.json}`, `evidence/final-dependencies.log{,.json}`. |
| Definitive corrected driver, local artifacts disabled | KeySort passes (1.717 s, 518,828,032 bytes); dependency build **fails**, exit 1 (20.295 s, 1,657,606,144 bytes); no guard stop. `evidence/isolated-keysort.log{,.json}`, `evidence/isolated-dependencies.log{,.json}`, `evidence/isolated-lakefile-v435.toml`. |
| Full affected validation / normal run-lean.sh / sort-conformance | Pending: dependency migration failure; no RUNTIME_GATE_PASS. |
| Before/after same-condition comparison | Pending: no migration implemented, so no delta or >10% acceptance claim. The fresh dependency failures are reproduction checks, not before/after measurements. |

An initial timing invocation found `/usr/bin/time` absent; no Lean check ran
in that invocation and it was not counted as passing. The Python guard then
provided the actual measurements above. Peaks are 100 ms sampled RSS, not exact
maximum allocations.

Reproduce after obtaining the pinned archive/toolchain and inputs:

```sh
flock -n /tmp/solidity-lean-feature-groups-20261025/writer.lock \
  python3 -B scripts/h62/item4/generic-storageops/reproduce-dependency.py \
  --toolchain /workspace/h62-generic-storageops/lean-4.35.0-linux \
  --output /workspace/h62-generic-storageops/reproduction-isolated
```

## Independent read-only reviews

Finder and skeptic used neither Lean server nor heavy builds. Both independently
confirmed all 230 original file pins and found a real mutual/end scope bug that
misnamed 139 declarations (117 theorems); the finder additionally found missing
ambient variable context in statement hashes. Both were fixed and covered by
regressions. Both rechecks pass for the frozen textual corpus, agree on all
6,036 qualified declarations and the inventory digest, and explicitly reject
interpreting this as semantic proof or full assignment completion.

Final tooling review also found that a guard stop could return success for
a SIGTERM handler exiting zero, extracted tool binaries were not linked to the
archive pin, and inherited Lean paths could defeat build isolation. The guard
now forces nonzero on every stop and kills surviving group descendants; two
process regressions cover timeout/normal failure. Reproduction freshly extracts
the verified archive, clears inherited Lean paths and explicitly disables the
local artifact cache (the finder caught that `--no-cache` alone is insufficient). Acceptance checks use
explicit failures rather than optimization-sensitive Python assertions.
Read-only rechecks and their evidence are retained in the external handoff. Nothing in these source checks proves a StorageOps semantic
statement; no theorem, helper lemma, new axiom, `sorry`, `native_decide`, raised
heartbeat budget or frozen-interface change was introduced.

## Blockers and next checkpoint

`B-TOOLCHAIN-RAW` is an external migration dependency: pinned Lean4.35 rejects
String/Slice APIs at `Solidity/Syntax/Raw.lean` lines 597, 650, 665, 682 and 684.
The file is outside this lane's exclusive write scope. Do not patch it here;
coordinator must supply the migration owner's compatible dependency and arrange
an authorized integration overlay. The exact errors and failing command are in
the saved dependency logs.

`B-V10-RELAY` remains the required exact-file owner agreement. H70 reports
tickets accepted by `solidity-h62-6-20261106/migrate-syntax` and
`solidity-v07-v11-20261030/v10-storage-operations`. Accepted ticket routing
does not grant original-file permission. `relay.sh` is host-only; no worker
installation or new relay mechanism is attempted. No existing family file was edited. Obtain V10 exact-file approval
before changing `Solidity/Backend/StorageOps/OperationControls.lean` or another
original selected after the census; owner applies migration patches. New helpers
stay additive in the assigned test directory, registration fragments await the
coordinator, and generated roots/module maps/axiom pins stay untouched.

Checkpoint 1 source census/classification is complete. Checkpoints 2–4 remain
blocked: prove the intrinsic parameterized law and typed fixture table; establish
correspondence and retain negative/refusal coverage with semantic acceptance;
measure same-condition before/after timings and complete all final validation.
No H55 work was duplicated. The goal remains blocked/unfinished, not complete.
Resume on this same VM/branch after the dependency is supplied; do not create a
replacement goal or push, merge, publish, pre-gate or change proof budgets.

Final static checks: Python syntax and this document's relative link pass;
`git diff --check` passes. Guard regression output is saved in
`evidence/guard-tests.log`; optimization-enabled census acceptance output is
saved in `evidence/acceptance-optimized.log`.

H70 independent read-only reviews covered the entire regenerated classification.
Finder and skeptic verified all 6,036 exact contracts/hashes, 230 file rows,
all 3,491 nonclaim definitions, and all old pins. Confirmed findings fixed:
masked literal/comment operators; overly narrow module domains; confusing
generated-data equations with observations; tuple recognition; condition versus
asserted-result handling; and quantified result contracts mislabeled closed.
The final finder recheck passes all 13 classifier regressions and manifest
`ea9995ef1ff96bcea13c16b5154127a6c8cfc16fa0cbdabddbdf9d5d9873e945`.
The skeptic independently confirmed source preservation, 309 traversed let
nodes, and 435 source-template groups/1,535 members. Its final recheck also
passes all 13 classifier regressions and the exact final artifact digest. Neither
reviewer ran Lean or wrote files. No new Lean validation is claimed in H70; the
earlier pinned 4.35 prerequisite/failure evidence above remains explicitly prior
run evidence on unchanged original sources.

## H70 fixture/equivalence work plan

`fixture_plan.py` produces a complete, explicitly unproved work ledger for all
1,623 control claims (1,007 public, 616 private) in 84 module packets. Each row
retains the exact original parameters, result type, ambient binders, proposition
shape and hashes. Each packet retains every local fixture/adapter; this is
conservative support retention, not a resolved dependency graph. Imported
fixtures remain covered by the pinned original family sources. The bulk ledger
stays outside git; `fixture-plan-manifest.json` pins deterministic reproduction.

This advances checkpoint 2 planning only. No ledger row is an inhabited Lean
fixture, semantic equivalence proof, permission or passing Lean gate. Source
repeat groups remain candidates; singleton obligations are never discharged by
grouping. All original files remain read-only.

The first proposed generic law is the existing typed scheduler composition:
`modifyMany effect (left ++ right) slots =
 (modifyMany effect left slots).bind (modifyMany effect right)`.
Quantify the existing K/DecidableEq, n/Schema, element Ty, slots, effect and lists.
Prove by induction on left, generalizing slots, using the actual modifyMany
cons equation and Option.bind_assoc. This must not assume success or omit
repeated keys. Its failure corollary must preserve none after any suffix; a
successful fixture must also rule out an always-failing scheduler. This law is
a proposal, not a checked theorem in this handoff.

The initial typed fixture design retains dependent Schema/Ty and keyed Slot
inputs, actual partial effects, both runtime key lists, and the original typed
observation function. Expected outputs remain data; a generic operation theorem
must derive them independently. Arbitrary runtime parameters stay quantified.
Use the original OperationControls forward/reverse late-failure, family-success
and same-key-order countercontrols as initial exact-instance obligations after
the Raw dependency is supplied. V10 agreement is still required before changing
OperationControls. Subsequent packets use their own graph/representation/target
strategy and exact contracts; the scheduler law is not claimed to cover them all.

Reproduce plan coverage with `python3 -B
scripts/h62/item4/generic-storageops/fixture_plan.py --output
/workspace/h62-generic-storageops/evidence/fixture-plan.json`. Scope and all
three outstanding proof/validation checkpoints remain unchanged.

Independent finder and skeptic reviews pass for this plan: all 1,623 contracts,
84 packets and 3,214 local fixture definitions retained, no equivalence or
permission claimed. Deterministic plan reproduction passes. The fixture-plan
tests check full coverage and reject five corruptions: case omission,
duplication, changed result, removed fixture and fabricated proved equivalence.
No Lean validation was run for this planning-only follow-up.

## H82 successor: deterministic frozen plan tests

The authenticated final member head was merged into the surviving storage branch.
The original plan test read the edited working tree while comparing the frozen
manifest, so it correctly rejected inventory drift before exercising the plan
checks. The test now obtains its exact pinned family from Git into a temporary
tree and binds both inventory and declaration-body reads to that tree. The
classifier, acceptance commands, manifests and frozen counts are unchanged.
A corruption test confirms that a changed inventory hash is still rejected.

All 26 generic tooling tests pass; the ten inherited audit tooling tests also
pass. The earlier live-drift failure and the intermediate mixed-tree failure
are retained. These are scanner/plan tests, not Lean proofs, witness coverage,
semantic correspondence or acceptance of the modified live family. All 1623
claim proof obligations and the original trust/migration holds remain open.

## Rejected scheduler append extraction

A candidate additive generic append law over the unchanged modifyMany
definition was tried in two exact-statement late-failure controls. The generic
law and repaired consumers passed kernel checks. The first consumer scripts
failed on list normalization/partial application; those failed receipts are
retained and not accepted. The repaired consumer file took 4.36 seconds against
a 3.60-second unchanged warm baseline, a 21.1% increase exceeding the frozen
10% STOP limit. The scheduler file itself measured 1.90 versus 1.88 seconds.

The complete candidate was rejected. OperationFamilies and OperationControls
were restored byte-for-byte to the committed tree, and the rejected patch and
measurements remain outside Git. No unchanged retry, accepted generic helper,
correspondence result or completed family migration is claimed. All 1623
original control proof obligations remain in the retained plan.

## Additive append law and typed fixtures

A distinct proof-only optimization proves modifyMany_append by explicit Option
cases and list induction. It retains the original scheduler definition, key
order, repeated keys, partial failures and actual intermediate slots. The law
and four additive fixture theorems use no axioms. A typed five-case fixture
table covers empty execution, successful clear, repetition, first failure and
late failure; the arbitrary-split theorem uses the generic law rather than
a table of expected outputs. The final scheduler file measured 1.93 seconds
against the unchanged 1.88-second warm baseline (2.66% increase, one sample).

The attempted original-control instances were stopped after guards incorrectly
expected no axioms. C212 directly checked the exact frozen original source:
both original controls already use propext and Quot.sound, matching the
optimized candidates. The prior axiom-growth interpretation was wrong. All
31 local import files match the C207 dependency context byte-for-byte. Both
original consumer proofs remain restored; no migration or optimized-consumer
performance acceptance is claimed. The accepted scope remains the additive
zero-axiom law and test fixtures only. All 1623 original claim obligations
remain in the frozen plan.

append_acceptance.py verifies that removing precisely the additive theorem
packet reproduces the frozen OperationFamilies source byte-for-byte, and that
all original declaration signatures remain exact. Its tampering tests are
source-preservation checks, not kernel proofs or full-family acceptance.
The failed consumer guards and previous timing rejection remain preserved;
full affected validation, whole-family correspondence and all original holds
remain open.

## Correction of the C207 axiom comparison

C212 preserves the original and candidate axiom messages and exact dependency
hashes. A reflexive proof is not sufficient evidence of an empty axiom set: its
referenced fixture definitions also matter. The measured original and candidate
sets are both [propext, Quot.sound]. Historical sealed reports are retained,
but their claim of growth from an empty set is superseded by this correction.
The independent C206 21.1% timing STOP remains unchanged. Neither this correction
nor the additive law completes the 1623-case generic migration.

## Optimized consumer timing STOP

After correcting the original axiom baseline, C214 measured the distinct
explicit-case/direct-term optimized consumer instances under fresh matched
serial conditions. Both original and candidate files passed kernel checks.
The optimized file took 4.33 seconds against 3.65 seconds for the unchanged
original, an 18.6% increase exceeding the 10% limit. The two proof rewrites
were rejected and OperationControls restored byte-for-byte. No unchanged retry
was made after this STOP.

This is a performance rejection, not axiom growth. C212's measured original
and candidate sets remain equal. The additive generic append law and typed
fixtures remain available, but no original-case migration is accepted and all
1623 frozen migration obligations remain open. Rejected source and raw timing
receipts remain outside Git with their exact before/after context.

## Fifteen finite coverage proof instances

The published lexical scanner identified fifteen identical two-index coverage
patterns in the nested-array transport controls. A general bounded-Nat to
dependent-Fin helper now discharges those exact finite membership obligations.
The helper permits arbitrary outer/inner bounds and uses no axioms; the fixed
fixture sizes remain original data, not admitted-source restrictions. Every
semantic correctness theorem application, store, location, observation and
negative case remains unchanged. Decidable coverage checks do not replace the
operation correctness proof with expected outputs.

Exact packet accounting preserves all 286 original declaration statements and
all fixture definitions, with precisely fifteen proof-body replacements and
one added helper. Six tampering controls pass. Both original and candidate
files pass kernel checks and existing guards; the otherwise unguarded child
bridge was directly checked on both sides with equal standard axiom sets.
One matched warm sample measured 53.61 seconds before and 54.38 seconds after
(1.4% increase, within 10%); no speedup is claimed. Independent read-only
reviews found no issue.

This is a bounded coverage-proof refactor, not full semantic classification,
fixture-table correspondence or acceptance of all 1623 control claims. The
earlier timing STOPs and corrected C207 axiom interpretation remain retained.
Full affected/lane validation and all original producer obligations stay open.

## Second coverage stage

C216 reuses the same general helper for fifteen additional finite membership
subproofs in the same fifteen callers. Cumulative accounting now covers thirty
subproof replacements, not thirty semantic theorem migrations. All 286 original
statements and fixture definitions remain unchanged. Both kernel checks and
existing axiom guards pass; the remaining child bridge has equal directly
measured standard axiom sets. One matched warm sample measured 51.83 seconds
before and 52.62 seconds after (1.5% increase, within 10%). Exact-byte packet
checks and six tampering controls pass. Independent read-only finder and skeptic
found no issue. Full-family correspondence and original lane closure remain open.

## Retained-cycle semantic case ledger

C218 records manual source obligations for all five frozen controls in
TargetRetainedCycle.Controls: three successful execution equations, seven
ordered tuple components, the successful uncleared-child counterexample, two
refusal orders, and five changed-payload conjuncts. The ordered case retains
all 18 store slots and nine sampled context fields. Whole-machine execution
equalities remain distinct from those finite observations. Stable reuse of an
already-cleared child does not restore its original payload; older retained
tail, opaque cell and outside words remain separately accounted for. Neither
a revert result nor the final execution index establishes rollback or gas
adequacy. No Source or physical-machine adequacy follows.

The generator checks exact frozen module bytes, all five statements and
fixture support. Source drift, omitted/duplicated cases, shortened observations,
changed statements and a fabricated proof-acceptance flag are rejected. Both
independent read-only reviewers found no issue. This ledger adds zero verified
proofs and supplies no generic instance or correspondence acceptance; the
1623-claim implementation queue and all existing timing/resource holds remain
open. No production source, premise, definition or axiom inventory was edited.

## Target-only self-copy case ledger

C220 accounts for all three frozen SourceSelfCopyTargetControls statements.
The first is actual structured Evm.run returning the original whole Machine
after consuming equal source/destination operands. The second records the
original and self-copy ten-slot views plus nine sampled context fields. The
third is only a different-empty-source afterCopy view equation, not an execution
or refusal theorem. It clears the live destination prefix while preserving
older nested tail11, older outer child2 header1/payload71 and outside sentinel99.
The historical SourceSelfCopy filename and compatibility namespace supply no
ordinary Source evaluator, numeric/physical bridge, static-call, gas or world
rollback adequacy.

The two ledgers reuse one source-accounting builder. A regression compares the
entire retained-cycle report with its frozen C218 generator; every prior field
and manual obligation remains identical. Exact module bytes, all three original
statements and fixture support remain pinned. Source/case/observation/statement
and fabricated-proof-acceptance mutations are rejected. This adds three manual
source plans and zero new verified proofs or generic correspondence instances;
the full 1623-claim queue remains unfinished. Production sources are unchanged.

## H113 parent page-cache accounting correction

Coordinator decision H113 authorizes the lane monitor to exclude active_file
and inactive_file page-cache charges from parent headroom accounting. The
monitor now records parent and runtime non-reclaimable usage separately, each
as max(0, memory.current - active_file - inactive_file), and sets parent_other
to max(0, parent_non_reclaimable - runtime_non_reclaimable). Raw parent_other
and every cache/non-cache term remain in each receipt. This avoids subtracting
runtime-owned cache from other users twice. The preserved monitor's 12 GiB cap,
zero swap, serial thread check, 16 GiB parent cap, 1 GiB reserve and host-headroom
checks are unchanged. H111 changes only the launching shell stack limit.

The fresh preflight passes: raw parent_other 5184303104 bytes becomes adjusted
286285824 bytes. Four controls pass, including rejection of actual non-cache
pressure and consistent handling of runtime-owned cache. Separate direct Lean
and Lake version probes and the serial KeySort build pass; an earlier configured
driver version probe rejected its flag ordering and is retained as a failed
probe. Both read-only reviewers found no issue. Historical resource refusals
and the denied reclaim attempt remain failed receipts; they are not relabeled.
This resource correction establishes no new theorem or whole-lane validation.
