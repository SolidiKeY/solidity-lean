# Architectural refactoring progress

## Constraints and baseline

Keep the dependency-free core and source refusals. Preserve unrelated untracked
`Bridge/build.log`, `error.log` and `tests/cloud/`. The shared writer lock is
`/tmp/solidity-lean-feature-groups-20261025/writer.lock`.

Memory: run heavy checks sequentially. Use a systemd scope with `MemoryMax=12G`
and `MemorySwapMax=0`, plus an available-memory guard with a 12 GiB reserve.
Do not terminate unrelated workers; keep at most four LSP files. Use
`LEAN_NUM_THREADS=1` and explicit `-j1` for memory-heavy fresh proof checks.
An environment-only probe had six Lean threads versus five with explicit `-j1`.
A temporary alternate TOML supplied this flag without changing the tracked
lakefile; it was removed after successful verification.

Avoid an 8 GiB virtual-address limit: it prevented an unchanged Lands dependency
from reserving thread stacks. Its retry passed at 1.91 GiB RSS with 32 GiB
virtual address space. The initial 8 GiB RSS guard stopped the existing
`Examples/Tactics/OpenLoops.lean`; its 12 GiB retry passed in 267 s at 9.32 GiB
peak aggregate RSS. Keep private caches on disk under `.lake/refactor-cache`,
not on the RAM-backed `/tmp` filesystem.

Before changes, error diagnostics passed for `Frontend/Source.lean` and
`Frontend/SolcJson/Getters.lean`; the getter fixture identity test passed.
The large `Examples/Tactics/PublicGetters.lean` LSP baseline did not complete
within the initial polling windows; partial diagnostics are not a passing check.

## Ranked opportunities

1. **Getter plans: one record per argument/result, then a nonempty completed
   result.** Five parallel lists implicitly synchronize binding/type, source
   key, ABI spelling and returned expression. Instead, store an input's four
   observations together and a result's binding/type/expression together.
   Separate traversal from a completed plan, which requires a first result.
   This prevents argument/selector/result misalignment and removes a partial
   head read in contract emission. Low migration risk: preserve projected
   parameter lists and every source refusal.
2. **Compiler provenance: one mode, derived observations.** A Boolean legacy
   flag, optional pipeline, settings text and optional effective ABI coder can
   contradict each other. Store legacy versus analysed settings as a sum and
   derive pipeline/coder/flag. In particular, requested v1 under via-IR has
   effective v2; legacy v1 has unknown effective coder. Keep that distinction.
   Moderate migration risk: admission and generated provenance quotations.
3. **Finite dispatch: function signatures as a dedicated type.** Candidates
   currently permit scalar `Ty` signatures and reject them through
   `asExternal`. A function-only signature would remove this impossible case.
   Defer until the two smaller boundaries are verified: nominal erasure and
   unresolved candidates must remain conservative.

No relevant git history indicates that these frontend representations were
introduced for speed. No semantic representation or taclet changes are planned.
Changed frontend modules invalidate their consumers, so measure focused checks
before committing and avoid repeated whole-package rebuilds.

| Boundary | Previously representable | New representation |
|---|---|---|
| Getter input | Two native arguments but one source key or ABI type | Each `GetterInput` carries binding, type, source key and ABI type. |
| Getter result | Empty `rets`/`values`, or differently ordered lists | `first : GetterOutput` and `rest` pair every binding with its expression. |
| Provenance | Modern via-IR with independently stored effective v1 | `.analysed .viaIR settings` derives effective v2. |
| Historical input | A historical flag alongside recorded pipeline/settings | `.historical` derives absent pipeline and empty settings. |
| Future dispatch | A scalar `Ty` where a function signature is required | A function-only signature would expose parameters/results directly. |

## Getter milestone

Commit: `2669fa75` (`Make getter plans intrinsic`).

Implemented: `GetterInput` retains all input metadata; `GetterOutput` retains
binding/type/value. `GetterPath` is incomplete traversal, while `GetterPlan`
requires `first` and carries optional `rest`. The ordinary function interface
uses derived `params`, `sourceParams`, `abiParams` and `rets`; `returnText`
handles scalar versus tuple without a partial operation.

Validation: error diagnostics passed for both changed Lean files. Focused builds
of `Solidity.Frontend.SolcJson` and `Solidity.Frontend.Testing` passed. The existing
getter success/false-assertion and reference-return refusal tests passed (two
tests, 218 seconds with one Lean thread). The large public-getter example's LSP
diagnostics completed without errors. The direct plan regression covers mapping
argument order, scalar/struct return text, omitted members, mixed mapping/array
traversal and omission-only result refusal.

Read-only finder and skeptic reviews found no correctness defects. Their
suggestion to exercise a struct containing only omitted members was incorporated
in the direct regression. Layer checking passed (143 core modules). Orphan
checking reports 33 pre-existing scratch modules; documentation path checking
reports 13 pre-existing missing references plus ambiguous short names. No files
were added by this milestone under the scratch directory.

## Upstream pull

The user requested a pull before further work. Fetched `origin/master` at
`a7a35aa5`; the getter commit required a merge rather than fast-forwarding.
Conflict resolutions retain upstream's primitive UDVT resolution, nominal
elementary-type rejection and enum-key membership guards in the new getter
representation. The docs index retains upstream's organization and this file's
link. Merged getter/contract diagnostics, the frontend build, direct plan
regression and layer check (152 core modules) passed. The uncommitted provenance
increment was preserved in autostash `54ec4911` and automatically restored by
merge commit `dc044e71` (`Merge upstream`). Both read-only reviewers confirmed
the resolution preserved upstream behavior.

## Provenance milestone

Commit: `82f67125` (`Derive provenance modes`).

Implemented: `Compilation.historical` or `Compilation.analysed pipeline settings`
replaces independent fixture/pipeline/settings/effective-coder fields. Existing
dot-notation queries are derived, so admission, scheduling, static compiler-code
checks and report quotations keep their interfaces. Historical v1 continues to
mean unknown effective coder, while via-IR uses v2 even when v1 was requested.

This does not turn arbitrary manually constructed settings text into a
certificate. `Source.read` remains the validation boundary; the sum removes
inconsistent combinations of its observations. No interpreter, taclet or
proof rule changes, dependencies, axioms or heartbeat overrides were added.

The changed module's error diagnostics and the frontend consumer build passed
after the pull (258 jobs). Read-only finder and skeptic reviews found no
correctness defects. The fixture matrix passed: historical v1/v2, analysed
legacy/via-IR, preserved settings and rejected partial/malformed metadata.

Shared-cache fetches initially reported success without restoring
`Tools/Preconditions.olean` and `Tools/SourceCounterexample.olean`. The private
disk-cache rebuild passed (207 jobs, 4.10 GiB peak aggregate RSS), and both
objects are present. The full post-pull library build passed all 684 jobs,
including public-getter proofs (52 s) and source-admission reports (2.4 s).
The frozen sort check passed: 377 taclets, all 131 read-bearing annotations.

The complete TestSuite target subsequently passed all 259 jobs, including
Derived20, refutations and the final report. The successful remaining-work run
peaked at 2.38 GiB aggregate RSS. Earlier reserve-guard stops were caused by
system pressure, including unrelated Java jobs filling RAM and swap; no Lean
error or changed proof budget was involved. Completed module artifacts were
reused rather than repeating passed proofs.

After removing the temporary configuration, the normal `./run-lean.sh` passed
with the private disk cache and frozen `SOLKEY_RULES`: 684 library jobs,
259 TestSuite jobs and the 377-taclet/131-annotation sort check. Its exit status
was zero under the same hard 12 GiB scope, disabled swap and memory guard.
This includes the post-pull public-getter proofs and source-admission report
quotation checks. No verification gate for the two refactors remains pending.

Both source areas received read-only finder and skeptic reviews. A final
progress-document review corrected stale running-status prose and confirmed
that completed checks and resource stops were distinguished. No confirmed
correctness finding remained.

Post-pull static gates: layering passed (152 core modules). The frozen TestSuite
audit passed: 564 functions, 552 derived, 11 refuted, one excluded, no pending.
Use `--solkey tests/migration/solkey/keyext.solidity.examples`; the sibling
checkout has drifted from the imported fixture. Orphan checking still reports
33 scratch modules. Documentation path checking reports 19 missing references
in existing vendor/module prose and ambiguities; none names the new progress
document or the edited source-admission document.

## Resume

Both selected representation increments and their final verification are
complete. All task changes are committed; only the three pre-existing untracked
items listed above remain. The temporary configuration is removed. Reacquire
the shared writer lock and reread status before any future writes or Lean
checks. Rebuild `Solidity.Frontend.Testing` before JavaScript regressions using
`build:false`; sandbox Node child-process EPERM needs a bounded host retry,
not a changed expected verdict.

After these two boundary refactors, the next architectural increment is the
ranked finite-dispatch signature change in `Frontend/SolcJson/Contract.lean`.
Introduce a parameter/result signature for candidates, leaving `Ty` parsing at
the external boundary. Migrate `candidate`, `getterCandidate` and `inspectCall`
together, then remove `asExternal`'s impossible scalar case. Preserve unknown
and reference candidates, source/native distinction and aliased target checks.
Run `scripts/finite-dispatch.test.mjs` and `scripts/getter-dispatch.test.mjs`
against rebuilt frontend artifacts before committing. This is deferred work,
not part of the two completed refactors.
