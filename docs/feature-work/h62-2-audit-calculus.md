# H62 item 2: calculus / try-evidence empty-statement audit

Owner: solidity-h62-2-20261106/audit-calculus.
Frozen base: c6f550e281a7e5affa9a99bc2cdaed556dec00e4.
Branch: codex/solidity-h62-2-20261106/audit-calculus.
Repository: /workspace/solidity-lean.

## Status: partial, persistent assignment unfinished

None of the four assignment checkpoints is complete. This checkpoint commits
reviewed census tooling and the first bounded fixture proofs; it is not final
acceptance. No frozen interface, premise, observation, exclusion, generated
root, central module map or axiom pin was edited. No original producer file was
edited. No H55 work was duplicated. No merge, push or publication was performed.

## Census and statement fidelity

The deterministic scanner at
`scripts/h62/item2/audit-calculus/census.py` enumerates every explicitly named
Lean path in both frozen module-map documents, including prose and brace
expansions. Shared files have one record with both area memberships. It records
361 files, 5,283 source theorem/lemma candidates, including 110 private source
declarations. Three replay commands require elaborated generated-declaration
accounting. No missing literal path was found.

Source signatures/names are lexical candidates, not the authoritative census.
Raw source, hashes and section directive history are retained. Directive history
is not effective Lean context (in particular include-in scoping). The exporter
in `tests/h62/item2/audit-calculus/KernelCensus.lean` records actual imported
kernel theorem names, dependent telescopes and structural type expressions.
The first serial full run stopped after 32 provisional module exports. Its
TermSize resource failure is described below. Old-format exports are not
accepted by the current freshness checks; a complete refreshed kernel census
remains pending. Generated/private/projection constants remain explicitly
pending classification and/or witnesses.

## Joint witnesses and component success

`tests/h62/item2/audit-calculus/CreationWitnesses.lean` proves nine closed joint
witnesses for all source-authored theorems of Creation/Artifact.
`tests/h62/item2/audit-calculus/FailureWitnesses.lean` proves nineteen for all
source-authored theorems of Failure/Correct. The extractor existentially binds
EVERY parameter and proof premise from the actual unchanged theorem constant,
at universe-zero specialization, with dependent types preserved. The verifier
reconstructs this telescope, checks the witness theorem type and checks axioms.
Those 28 joint witness proofs have empty axiom sets.
`tests/h62/item2/audit-calculus/StaticTransportWitnesses.lean` adds three checked
joint proofs using one storage invariant, nonempty returned bytes, receiver 7
and self=true. Two cover mapped interfaces (declared-return-byte transport and
storage-only transport); raw StaticInvocation is a supporting transitive
interface, absent from the literal 361-file roster, and is NOT counted as
mapped coverage. Its storage-only fixture has a changed ledger and balance.
These three proofs use only propext/Classical.choice/Quot.sound. A simultaneous
credit-boundary theorem uses propext. No source/native frame production or
opaque-call authentication is inferred from these component witnesses. These statements have
per-input bounds/stack/frame requirements; their intrinsic records are witnessed
jointly, not by separate inhabitance assertions. Broader global premise
structures remain unclassified and unwitnessed.

The unchanged failure emitter satisfies a new component contract requiring
successful compilation and exact checked terminal observation for every
supported input/machine. Closed controls reject compilers that reject all
inputs or always emit REVERT. Returned bytes, custom revert bytes and the
1023-word initial-stack refusal are observable. Existing emitter totality has
only the baseline propext/Classical.choice/Quot.sound dependency set. No source
compiler totality, gas adequacy, world result or historical-fork execution
claim follows from this slice; all remain assignment obligations.

`scripts/h62/item2/audit-calculus/acceptance.py` reconciles current proof
receipts, frozen source hashes and exact kernel expressions. It preserves
module+name provenance instead of silently collapsing three repeated public
names. Raw static type expressions match their fresh exports byte-for-byte;
an integration failure exposed the roster/supporting-dependency distinction,
which is now represented separately. No statement was normalized or weakened.

Current mathematical checks:31 joint proofs = 30 mapped + 1 supporting; 5,253
source candidates remain uncovered. Strict transitive artifact acceptance is
still pending a fresh dependency cut, so these are not full census acceptance
numbers. The acceptance command invalidates its previous output before checking
and fails rather than publish a stale report. --require-complete also rejects
remaining coverage, owner, semantic, validation and performance gaps.

`owners.py` checks the coordinator ownership snapshot checksum and applies only
H30-WRITER inclusion/exclusion rules. It establishes253 coordination contacts:
252 VA1, 1 H28 SolkeyAgreementH28/Freshness.108 files lack a matching exact-file
contact. These contacts are not semantic-producer transfers. Producer-family
routing: creation G44.02/V14; failure G38/V12; static boundary P2/P3/RO. This
CORRECTS the earlier provisional V14 label for failure emission. Exact semantic
producer confirmation remains pending; migration overlays grant no live-owner
transfer. Q-OWN-01 asks for the authoritative unresolved-owner mapping.

## Runtime and gates

The local checkout was old and clean. The assigned remote branch was absent;
fetching origin/master recovered the exact base, whose remote ancestry was
verified before branch creation. Existing work branch was preserved.
All coordinator input hashes matched their supplied manifest.

No Lean MCP tool is exposed. Official Lean 4.24.0 release archive was downloaded
and unpacked outside Git for this additive frozen-base audit; repository
lean-toolchain remains untouched. Actual Lean commit:
797c613eb9b6d4ec95db23e3e00af9ac6657f24b. Lake:
5.0.0-src+797c613 (Lean 4.24.0). This interprets the coordinator's 'Migration ONLY'
pin as scoped to migration lanes; Q-TC-01 asks for correction if intended for
this audit too. No v4.24 distributed/per-master cache is used. No runtime-gate
pass is claimed under the v4.35 migration pin.

`scripts/h62/item2/audit-calculus/bounded_lean.py` runs one Lean process at a
time with the writer lock, LEAN_NUM_THREADS=1, explicit-j1,--tstack=131072,
--memory=12288,1800-second CPU cap, no swap,12 GiB owned-group RSS monitoring
and 4 GiB available reserve. The VM cgroup's hard memory limit is 17,179,869,184
bytes. Reserve/RSS are monitored every 0.25 seconds, not a hard RSS partition.
Each child owns a process session so a resource stop terminates its own group.
No systemd-run is used. No heartbeat limit was raised.

The initial driver incorrectly capped virtual address space at 12 GiB.
Calculus/TermSize then aborted with failed-to-create-thread (exit-6). The same
unchanged file passed after correcting that bound:50.025 seconds,
peak RSS 1,660,481,536 bytes versus virtual 13,775,151,104 bytes; 59 internal threads
were observed despite the requested-j1 worker setting. This confirms the
repository's virtual-reservation warning. The failure remains in evidence and
is not counted as a passing full run.

Schema 2 receipts now bind source, actual Lean binary, object, direct import
objects, helper, immutable log, scratch and JSON hashes. Export always checks
the current helper first and removes stale indexes on failure. Reuse requires
a matching hash-bound schema 2 DIRECT compilation; legacy artifacts cannot be
promoted into source-bound success. Acceptance recursively certifies import
artifacts and enforces one Lean binary across every edge. Earlier legacy
adoptions are provisional and must be rebuilt or matched to a real direct
compile; they do not pass strict acceptance. Twelve adversarial receipt
controls cover failures, tampering, stale helpers, legacy promotion and mixed
SDKs. Receipt tests are external tooling tests, not Lean proof substitutes.

Passing recorded checks:

- KeySort per-file prerequisite: exit 0, 2.339 seconds.
- Six adversarial scanner controls: exit 0; twelve receipt controls: exit 0.
- Kernel exporter and three witness modules: exit 0;31 exact joint verifications.
- Per-module export integration: exit 0 for both selected modules.
- Layers: exit 0, 857 core modules, zero frontend/adapter reachability.
- Generated roots and fragment checks: exit 0, no central edits required.
- Frozen Solidity/module-map diff versus base: empty.

Earlier failed diagnostics (Fits elaboration, dependent observation elimination
and stack recursion) were fixed; no failed check is counted as passing. The
first timing wrapper lacked /usr/bin/time and exited127 before Lean; the Python
runner replaced it and KeySort was rerun successfully. Complete actual commands,
exits, versions and timings are in off-Git JSONL receipts. Initial selected
original dependency closure: 13 files, 84.157 seconds. Subsequent unchanged
Artifact/Correct checks were 0.875/2.051 seconds versus initial 1.219/2.964; these
are warm/cold observations, NOT a controlled before/after performance gate.
Full affected validation, final run-lean.sh, matching-cache before/after and
strict transitive acceptance remain pending. No >10% performance acceptance is asserted.

## Independent reviews

Finder /root/finder_census and skeptic /root/skeptic_census were independently
read-only, without Lean/server execution. They found and verified fixes for
let-signature truncation, multiline global premises, mutual namespace scope,
prose-path omissions and generator locations. Six adversarial tests preserve
these controls. Finder additionally caught an entire-module overclaim; wording
now distinguishes nine source theorems from29 kernel constants. Both reviewed
the 28 joint witness receipts as distinct, axiom-free and nonvacuous, and
confirmed component totality/control scope. Their remaining warnings are kept
as unfinished obligations, not waived. New reviews confirmed the static witness fidelity,253 / 108 owner inventory and
G38/V12 correction. Finder required removing legacy artifact promotion;
that path was removed and refusal controls added. Both reviewers confirmed
module provenance and30 mapped / 1 supporting scope accounting. Finder's final
SDK-edge check was added with a negative mixed-SDK control. Full review
evidence is off Git.

## Continuation and handoff

Off-Git evidence directory: /workspace/h62-audit-calculus-evidence.
The next reviewed handoff covers the resource-bound repair, hash-bound receipt
and owner tooling, and the static transport fixtures. These are bounded
work items; none completes the four-checkpoint assignment. Per the fresh-thread instruction, hand off
to the coordinator after these items using the SAME VM, branch and existing
persistent goal. No replacement goal or competing continuation was created.
get_goal is not exposed; the coordinator explicitly said this is not a blocker.

Next: refresh the serial dependency/kernel cut using only hash-bound direct
compiles (the full run has NOT passed), then export every mapped file; resolve exact-file
owners and classify global versus per-input premises; prove ALL remaining joint
witnesses; cover generated declarations explicitly; add actual supported source
compiler success and failure/gas/fork/world boundaries without touching frozen
interfaces; perform independent reviews, full gates and controlled timings.
Do not mark the goal complete. No proven public vacuity requiring ESCALATE has
yet been identified; uncertain/uncovered statements remain pending, not cleared.

Registration fragment for coordinator review only: the four audit modules
KernelCensus, CreationWitnesses, FailureWitnesses and StaticTransportWitnesses remain in the authorized
tests directory. No area registration or relocation is authorized by this note.
