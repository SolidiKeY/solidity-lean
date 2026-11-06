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
Only two mapped modules have been exported so far: 92 theorem constants,
including 64 generated/helper/projection constants beyond source declarations.
Those 64 are explicitly uncovered pending classification and/or witnesses.

## Joint witnesses and component success

`tests/h62/item2/audit-calculus/CreationWitnesses.lean` proves nine closed joint
witnesses for all source-authored theorems of Creation/Artifact.
`tests/h62/item2/audit-calculus/FailureWitnesses.lean` proves nineteen for all
source-authored theorems of Failure/Correct. The extractor existentially binds
EVERY parameter and proof premise from the actual unchanged theorem constant,
at universe-zero specialization, with dependent types preserved. The verifier
reconstructs this telescope, checks the witness theorem type and checks axioms.
All 28 joint witness proofs have empty axiom sets. These statements have
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

`scripts/h62/item2/audit-calculus/acceptance.py` reconciles current passing proof
receipts, source hashes and exact kernel expressions, and refuses duplicate
statement accounting. Partial report: 28 verified source candidates, 5,255
uncovered source candidates, plus 64 additional uncovered kernel constants.
`--require-complete` fails while any required coverage or limitation remains.
Producer-family candidate V14 for these two backend files follows the supplied
G44/G45 owner keys; exact-file owner confirmation remains pending. Every other
unresolved owner remains explicit rather than inferred from Git authorship.

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

`scripts/h62/item2/audit-calculus/bounded_lean.py` runs private-output diagnostics
serially with the writer lock, LEAN_NUM_THREADS=1, explicit -j1, 12GiB address
space cap, 1800-second CPU cap and 4GiB available reserve, without swap or
systemd-run. It is not a substitute for final run-lean.sh/Lake gates.

Passing recorded checks:

- KeySort per-file prerequisite: exit 0, 2.339 seconds.
- Six adversarial scanner controls: exit 0.
- Kernel exporter and both witness modules: exit 0, exact joint verification28.
- Per-module export integration: exit 0 for both selected modules.
- Layers: exit 0, 857 core modules, zero frontend/adapter reachability.
- Generated roots and fragment checks: exit 0, no central edits required.
- Frozen Solidity/module-map diff versus base: empty.

Earlier failed diagnostics (Fits elaboration, dependent observation elimination
and stack recursion) were fixed; no failed check is counted as passing. The
first timing wrapper lacked /usr/bin/time and exited127 before Lean; the Python
runner replaced it and KeySort was rerun successfully. Complete actual commands,
exits, versions and timings are in off-Git JSONL receipts. Initial selected
original dependency closure:13 files,84.157 seconds. Subsequent unchanged
Artifact/Correct checks were0.875/2.051 seconds versus initial1.219/2.964; these
are warm/cold observations, NOT a controlled before/after performance gate.
Full affected validation, final run-lean.sh, matching-cache before/after and
acceptance remain pending. No >10% performance acceptance is asserted.

## Independent reviews

Finder /root/finder_census and skeptic /root/skeptic_census were independently
read-only, without Lean/server execution. They found and verified fixes for
let-signature truncation, multiline global premises, mutual namespace scope,
prose-path omissions and generator locations. Six adversarial tests preserve
these controls. Finder additionally caught an entire-module overclaim; wording
now distinguishes nine source theorems from29 kernel constants. Both reviewed
the28 joint witness receipts as distinct, axiom-free and nonvacuous, and
confirmed component totality/control scope. Their remaining warnings are kept
as unfinished obligations, not waived. Full review evidence is off Git.

## Continuation and handoff

Off-Git evidence directory: /workspace/h62-audit-calculus-evidence.
Three bounded work items are reviewable: scanner controls, kernel/joint tooling,
and first creation/failure fixtures. Per the fresh-thread instruction, hand off
to the coordinator after these items using the SAME VM, branch and existing
persistent goal. No replacement goal or competing continuation was created.
get_goal is not exposed; the coordinator explicitly said this is not a blocker.

Next: extend serial kernel export to every mapped file; resolve exact-file
owners and classify global versus per-input premises; prove ALL remaining joint
witnesses; cover generated declarations explicitly; add actual supported source
compiler success and failure/gas/fork/world boundaries without touching frozen
interfaces; perform independent reviews, full gates and controlled timings.
Do not mark the goal complete. No proven public vacuity requiring ESCALATE has
yet been identified; uncertain/uncovered statements remain pending, not cleared.

Registration fragment for coordinator review only: the three audit modules
KernelCensus, CreationWitnesses and FailureWitnesses remain in the authorized
tests directory. No area registration or relocation is authorized by this note.
