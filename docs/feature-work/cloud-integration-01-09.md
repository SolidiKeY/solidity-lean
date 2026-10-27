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

The serial lane sweep exposed two further cross-lane test mismatches. Enum
ABI rejection vectors keep their inputs and failure/return expectations; a
matched decoder rejection is now classified consistently as replay agreement.
Negative controls reject false success and fabricated return data in both
pipelines. This does not establish execution of the source body.

Contract-valued immutable roots are now supported as address roots. Replace the
old refusal assertion with execution checks that their unread initializer's
increment occurs exactly once, plus controls rejecting the former zero-effect
outcome, in both pipelines. Other unsupported forward-initialization guards
remain. MCP diagnostics pass both updated files; finder and skeptic confirmed
the changes independently without Lean calls.

A full-build pin still expected overlapping transient tuple roots to be
rejected. The combined scalar-tuple lowering supports them. Replace that pin
with a kernel-checked `source_tuple_overlap` theorem using distinct right-hand
values: right-to-left stores leave the first captured value at the shared root.
Per-file MCP diagnostics pass; independent review confirmed the assignment order.

## Validation

- Reachability: 699 modules, zero orphans or disallowed modules.
- Core layering: 152 core modules, none reaches the elaborator.
- Strict automation: 491 automatic, 61 budgeted, 11 refuted, zero pending.
- JavaScript-only upstream/compiler-code regressions: 17/17 pass.
- Compiler-backed source-import regressions: 22/22 pass.
- Frozen SolKey sorts: 377 taclets parsed, all 131 read-bearing annotations match.
- Trust inventory: 713 sources, 239 implementation/recovery sites, zero findings.
- MCP diagnostics: Raw, Body, Contract and the focused combined regression pass.
- Modifier-frame proof regression: retry passes after an initial process exit 135.
- Frozen TestSuite static audit: 564 functions, 552 derived, 11 refuted, zero pending.
- Full build, frozen sort/corpus and the complete lane regression set:
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
