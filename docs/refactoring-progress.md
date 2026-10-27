# Architectural refactoring progress

## Constraints and baseline

Keep the dependency-free core and source refusals. Preserve unrelated untracked
`Bridge/build.log`, `error.log` and `tests/cloud/`. The shared writer lock is
`/tmp/solidity-lean-feature-groups-20261025/writer.lock`.

Memory: run heavy checks sequentially. Command-line Lean uses
`LEAN_NUM_THREADS=1` and `ulimit -v 8388608` (8 GiB virtual memory per process).
Apply this limit to Lean, not Node's virtual address reservations. Do not start
parallel builds or change other sessions' workers. Use at most four LSP files.

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

## Getter milestone

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

## Resume

Commit the verified getter milestone before editing provenance. Record its hash
here in the following milestone. Re-read
`git status` and acquire the shared writer lock before writes or Lean checks.
Rebuild `Solidity.Frontend.Testing` before running JavaScript regressions that
use `build:false`. Inside this sandbox Node child processes can report EPERM;
rerun the same bounded command on the host rather than changing expected
verdicts.
