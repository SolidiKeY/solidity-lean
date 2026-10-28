# Given-heap memory parameter witness

Task branch: codex/next10-memory-parameter-witness.
Published base: f4dee4a29c2e208b36db4a4161a4723c735cd775.
Repository: /workspace/solidity-lean; origin https://github.com/SolidiKeY/solidity-lean.git.
Origin/master was fetched and the base ancestry check succeeded; fetched master equals the base.

## Scope and evidence boundary

The original gapMemParam definition and every original inTarget certificate
are unchanged. Its exact verdict is now refuted, certified by the kernel
theorem gapMemParam_verdict. The witness has one existing uint array [1].
gapMemParam_countermodel proves falsity there; gapMemParam_empty proves truth
at State.init, explaining why an empty countermodel heap is insufficient.

MemoryWitness.values enumerates Option (HRef H R), including unset. bind_exact
proves its exactness at the same heap for both modalities. Nested binders may
select the same reference. The typed primitive-array builder proves exact
object lookup and reference injectivity, independently of contents. No given-heap
quantifier is translated into fresh allocation.

The new decision fallback returns only a proof-carrying concrete countermodel
or unknown. Checked.yes concerns one state and is never promoted to global
validity. The positive repeated-read control is kernel-proved valid and checked
true, but its global decider verdict remains unknown. Finite witness search
does not prove general memory-binder completeness. No change to Covered,
inTarget, exclusions, Waivers, DecisionTheorem, or D1/D2 profiles is made.

The controls preserve full identity, enumeration, before-write, and after-write
observations. They cover same identity through independent references, distinct
identities with equal/different contents, an untouched index, unset, and absent
object types. These are logical/kernel and native Lean fixtures; no new source
admission, solc, or external EVM agreement is claimed. Existing typed heap
read/write laws implement the identity/index distinction in SolKey readOnWrite.

## Validation record

Evidence directory: /workspace/next10-memory-parameter-evidence.
All mandatory assignment gates passed. The original given-heap gap is refuted with a kernel-certified countermodel. Broader memory decision completeness remains open.

- Runtime gate: exit 0, Lean 4.24.0 (797c613), Lake 5.0.0-src+797c613.
  runtime-gate.log records 12 GiB memory.max, zero memory.swap.max, successful
  KeySort build, and 25,939,968-byte cgroup peak before RUNTIME_GATE_PASS.
- Baseline: baseline-memory-fixed.log, exit 0; original DecisionMemory body,
  guards and proofs copied verbatim, with verbatim required helpers and the
  direct calculus import. baseline-source-provenance.json records source hashes.
  All 21 ordered original memory verdicts were printed; gapMemParam was unknown.
  Cgroup peak: 248,369,152 bytes.
- New module: MCP full diagnostics pass, no errors/warnings; witness-build.log
  exit 0, 1.7 s module build, cgroup peak 197,332,992 bytes.
- Decision integration: MCP complete diagnostics pass (the first 45 s poll was
  partial, the second complete); decision-build.log exit 0, 40 s module build,
  cgroup peak 446,029,824 bytes.
- New controls: mcp-minimal-final1.log complete diagnostics pass, no errors or
  warnings; only expected actual axiom-audit information.
- Full native exact-source memory fixture: full-native.log exit 0; all original guards, new kernel certificates, full alias observations and 21 ordered verdicts passed. The only changed old verdict is gapMemParam, unknown to refuted. Docker duration 87.167 s; cgroup peak 256,307,200 bytes.
- Aggregate RSS samples are separate from cgroup-charged memory peaks, in
  *-rss.log and *-memory.csv. Final resource results appear below.

Actual axiom audits: bind_exact and checker kernel/compiled agreement use only
propext, Classical.choice, Quot.sound; heap_get and reference_eq_iff use propext;
Checked.refutes uses no axioms. All audited example headline theorems use only
propext, Classical.choice, Quot.sound. No new axiom or unfinished proof is retained.

## Runtime investigations

The saved activation was not initially on PATH; its Lean toolchain was reused,
with LEAN_NUM_THREADS reset from the setup default 4 to 1. Systemd is offline.
Docker cgroup v2 supplies the hard 12 GiB cap and zero swap. Explicit Lean -j1
is supplied by a private alternate Lake TOML and the LSP invocation; no proof,
fuel, node, heartbeat, or test budget is raised. Caches remain on disk.
The per-VM OS reserve follows coverage-plan; no extra shared-host 12 GiB
reservation is imposed on this 16 GiB executor.

An initial Lake CLI -j1 attempt failed because Lake has no such option; -j1
was moved to weakLeanArgs as documented. Two broad baseline attempts were
intentionally stopped, never counted as passes: first to restore the saved
disk cache setting, then to avoid repeated unrelated hash examples. An exact
source memory-only baseline passed instead. Its first helper extraction also
copied unrelated double_covered; that failed log is retained, and the stray
helper was removed without changing any memory observation.

Opening the owning example in MCP before its example imports were compiled
caused automatic dependency setup to launch an unconfigured build. That
task-owned container was stopped and is not passing evidence. Subsequent MCP
checks use compiled imports. A proof-attempt replay of the entire memory
fixture was likewise stopped and replaced with a control-only exact-source
probe. The final owning-file check subsequently passed after the serialized import build.
No unrelated workers, other VMs, setup files, or user files were changed.

## Review and shared edits

Initial independent read-only finder/skeptic reviews identified unset values,
both modalities' universal meaning, aliasing, successful-evaluation-only
denotation bridges, and the danger of State.noHeap/MxRel.apart. Those findings
are reflected in the implementation. Final independent read-only finder and skeptic reviews covered the complete code, registration, and listed docs. Neither used Lean server, builds, checks, or writes. Both found no semantic defect and confirmed original definitions/certificates and honest scope claims. Both found one reversed prose locator in automation M7; it was corrected from below to above. Final gates subsequently passed.

Shared edits are narrow: Decision.lean import/fallback/two proofs; Solidity.lean
module registration; module-map, automation M7, and the rule correspondence note.
The substantive new code is MemoryWitness.lean and the owning DecisionMemory
controls. The exact-site trust inventory registers the one new compiled override, backed by the kernel/compiled equality theorem; TrustAudit.lean adds its new public headline theorems. No scanner policy, source fixtures, or feature classifications are changed.
The feature inventory was regenerated and checked by its audit script; generated content and classifications are unchanged.

## Final confirmation

- `./run-lean.sh`: exit 0. Main library 686 jobs, TestSuite 259 jobs;
  all 26 timed TestSuite modules satisfy the unchanged 300-second strict gate.
  The actual owning DecisionMemory module built in 63 seconds. SolKey check
  parsed 377 taclets, with all 131 read-bearing taclets covered and annotations matching.
- Final owning-file MCP diagnostics: complete, success, no diagnostic errors or
  warnings. The verification tool's lexical local-instance note refers only to
  the DSL's InContract data instance; it is not a proof hypothesis.
  Minimal-hypothesis inspection reports no explicit hypotheses on the countermodel theorem.
- Final TrustAudit MCP and CLI: success; 544 headline theorems use only the
  standard three axioms. CLI exit 0, 110.503 seconds. The 15 new headline names
  and exact compiled-override registration were independently reviewed.
- Final ordered owning-module observations: exit 0, 27.969 seconds. The original
  21 memory verdicts differ only at gapMemParam (unknown to refuted). The original
  six gaps, in KIntTwoAnchors, QuantLedger, MemInnerNeg, MemParam, MemStruct,
  WrittenMemory order, are unknown, unknown, unknown, refuted, unknown, unknown.
  Both alias controls and complete observations pass; see final-observations.log.
- check-orphans, check-layers, check-automatic --strict, strict full-build timing,
  feature-audit regeneration/check, and diff whitespace checks: exit 0.
  Automatic coverage remains 491 automatic, 61 step-budget, zero manual,
  11 refuted, zero pending. The source trust scan passes: 715 sources,
  241 inventoried sites, zero findings; both existing trust script tests pass.
  The initial trust scan correctly rejected the then-unregistered override;
  the exact site was registered without changing scanner policy or allowed axioms.
- Optional global doc-path scan: exit 1, 20 missing references in unchanged
  Eqns.lean and archived upstream validation files; existing ambiguity messages
  are also retained. These are pre-existing findings, not a mandatory task gate.
  optional-docpath-provenance.json verifies the affected missing-reference files
  are byte-identical to the published base.

The full serialized build sampled 7385.292 seconds. Its exact cgroup-charged
peak reached the unchanged 12 GiB hard cap (including disk cache); maximum
sampled aggregate RSS was 11,484,660 KiB. Minimum sampled VM MemAvailable was
6,205,504 KiB. Cgroup reclaim occurred, with zero OOM events/kills; the container
exited 0. This is measured warm-cache evidence, not a cold-build headroom claim.
No proof or test budgets were raised. full-build-resources.json and the raw
1 Hz CSV distinguish RSS, charged cache, and available VM memory.

original-gap-preservation.json verifies all six original definitions and target
certificates against the base. final-gates.json and static-gates.json record
commands, exits and timings; final successful trust logs supersede the retained
initial failure. container-evidence.json records only selected container state
and resource limits. Private single-thread Lake configuration is preserved in
the evidence directory, excluded from the commit; to reproduce the recorded
wrapper commands, copy that configuration back to the repository root.

No mandatory validation or original gapMemParam blocker remains. Positive
same-read global decision remains unknown, and the other five original gaps
remain open; neither is relabelled as complete. No source/compiler/external EVM
claim is inferred from the Lean kernel and native observations. Commit and patch
identifiers are recorded in the exported workspace handoff after committing.
