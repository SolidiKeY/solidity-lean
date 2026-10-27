# Cloud tasks 01–09 integration

The integration branch combines committed snapshots of cloud tasks 01–09 with
`origin/master` at `bc05798c8e6cc54fdbf8315fca82723f9fc40dae`. Task 10 is not
included. The original checkout and the existing `integ` worktree are unchanged.

| Task | Snapshot | Scope at collection |
|---|---|---|
| 01 | `54239de9f802` | Modifier return fixes and completed validation |
| 02 | `67d0549ee5b5` | 67/67 entrypoint and initialization fixtures |
| 03 | `a2a9da820f06` | 10 passes; three assembly exclusions and one recursion-resource block |
| 04 | `601b2d5943e2` | 11/11 signed numeric fixtures |
| 05 | `f5ad68d70664` | 24/24 function dispatch fixtures |
| 06 | `f106995b5358` | 12/15 fixtures; recursive-storage implementation remains unfinished |
| 07 | `0ee1cfedc529` | 11/11 tuple/reference fixtures |
| 08 | `35d026b12dec` | 23/23 assigned fixtures; broader source validation and false-specification blocker remain |
| 09 | `67d21501a412` | 21/28 fixtures; seven assembly/layout exclusions |

Only committed changes were collected. In particular, task 06 had substantial
uncommitted graph-storage changes; those remain in its cloud executor and are
not part of this integration. Original lane reports retain their original model
hashes and commands: they are evidence for those snapshots, not claims that the
combined model has already passed their full fixture inventories.

## Merge resolutions

- Preserve the current specification reader while adding replay entrypoint,
  pipeline and validated compiler-code arguments to the importer.
- Resolve ABI entries by canonical compiler declaration identity. Retain enum
  input ranges, address canonicality, getter dispatch and resource diagnostics.
- Preserve declaration-indexed library struct reachability, foreign enum bounds,
  enum field carriers, and reverse-C3 pipeline-specific initializer scheduling.
- Keep typed transient regions in both declaration and initializer rendering,
  without relaxing omitted-initializer rejection.
- Retain primitive tuple overlap/write order, per-target reference-width checks,
  mixed-reference conditional capture and all lane replay controls.
- Preserve current documentation cleanup while adding the new lane handoffs.

## Confirmed integration regressions

Read-only finder review caught inherited entry duplication when `testing` and
`entrypoints` are combined. Testing already includes selected inherited entries;
the extra-entry list now excludes that full set rather than only own entries.

Independent skeptic review identified a mismatch between ordinary enum-array
carriers (`uint`) and unconditional `uint8` inline literal casts. The focused
regression reproduced the import gap in both pipelines. Inline literals now
resolve their enum declaration identity and use the same carrier as the type
table. Missing or ambiguous identity remains an explicit refusal.

An identical `unparen` helper introduced independently by two lanes was also
deduplicated. Native replay controls now carry the declaration metadata required
by the stricter combined ABI resolver; their expected outcomes are unchanged.

`tests/upstream/CloudIntegration.lean` checks an inherited entry exactly once
and replays ordinary-enum and struct-associated-enum inline arrays in both
pipelines from the hash-pinned `tests/solc/CloudIntegration.sol` inputs. The
before-fix width failure and after-fix MCP success were observed separately.
Both reviewers confirmed the corrections without opening Lean workers.

## Validation

- Reachability: 699 modules, zero orphans or disallowed modules.
- Core layering: 152 core modules, none reaches the elaborator.
- Strict automation: 491 automatic, 61 budgeted, 11 refuted, zero pending.
- JavaScript-only upstream/compiler-code regressions: 17/17 pass.
- Trust inventory: 713 sources, 239 implementation/recovery sites, zero findings.
- MCP diagnostics: Raw, Body, Contract and the focused combined regression pass.
- Full build, frozen TestSuite/sort/corpus and the complete lane regression set:
  in progress; no combined pass is claimed yet.

The first build was sandbox-blocked on the shared Lake cache. The next attempt
found the duplicate helper and was stopped after that error was fixed; its log
is retained. Compiler subprocess tests initially used the absent default sibling
`/tmp/solkey`; subsequent runs select the configured checkout explicitly.

The documentation-path scanner reports 19 unresolved references, including six
embedded historical log references in task 03 evidence. These are reported as a
failing check, not silently relabeled as a passing gate.

No source input/expectation, proof limit, dependency requirement, axiom or
`sorry` was added to make a failing obligation pass. The known recursion-resource
and `sliceHashed` specification blockers remain explicit. No push or merge to
master was performed.
