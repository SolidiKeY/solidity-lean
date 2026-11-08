# Yul views: one layout-indexed view

Verdict: **no-go for a blanket layout migration on this evidence; go for exact
existing-law reuse.** The 15-file pilot saves only **7 / 1,797 lines (0.39%)**
and adds **8 explicit declarations**. Structural reuse saves 55 lines and
removing proof-search preludes saves 18; the layout kernel and its compatibility
wrapper cost 66. This does not substantiate 75k → 5–10k. It does not rule out
a future layout design that actually replaces complete heap/image proofs.

## Scope and prior work

At base `772806909ec30c93a85a95c01130a70b6bcc83ca`, Views contains
**74,635 physical lines / 882 Lean files**, including **23,271 lines / 286
Controls files**. The assignment's 879-file figure is an older denominator.
The [direction audit](direction.md) and [declaration graph](direction-tools/declgraph/summary.json)
report 17,904 declarations and zero headline-statement uses at their own
`d6fd95f08` base; they verify **zero deletable lines**. Import reachability and
lack of headline uses do not justify deleting any theorem here.

The blocked [generic-view work](../feature-work/h62-4-generic-yul-views.md)
and its [fixtures](../../tests/h62/item4/generic-yul-views/) supply useful
byte-object observations, not a finished production migration. Published t1
heads `e2dd4428d73d94b28a1cb82867d7cf5e8d65aca4` (flow/reads) and
`b2792f6847955307ef6456c80c2f9f76bb79c6a9` (plan/frame) were inspected.
The former shares intrinsic preparation proofs while preserving computational
bodies. It is proof factoring, not an established whole-area reduction. Reuse that
interface work instead of claiming another schema/fixture layer is a migration.
No published `tv-yul` branch was available during inventory. Its assigned
translation-validation experiment remains separate: a generic layout relation
can be the representation invariant consumed by a validator's soundness proof;
validator completeness and exact Source/Yul results must still be proved.

## Ranked ideas

| Rank / mechanism and files | Measured saving (lines) | Whole-area estimate and method | Effort | Strength risk | Go/no-go |
|---|---:|---|---|---|---|
| 1. Existing decoder induction and inventory-support laws: MemberArray, Array/StructWordHeap/Retained | 55 structural; 18 additional search-prelude lines | 55–63 structural lines: retain the measured 55, plus at most 8 for the similar ByteElementStore block (unverified). No multiplication by area size | low | exact typed results and errors preserved | **go**, narrowly |
| 2. One finite layout-indexed read relation; AggregateMemoryWords and ArrayWordStore | **−66** (cost), including wrapper | 0 bankable large saving; 65k–70k desired reduction remains unmeasured | medium–high | packed offsets, intrinsic codecs, aliases, hashes and allocation must be proved | **no-go** for rollout; next test below |
| 3. Controls as instances of existing generic laws; StructWordRetainedControls | 9 structural + 1 prelude, already included above | 0 additional bankable; 23,271 Controls lines is only a ceiling. Fixture data and distinct failures remain | medium | deleting negative checks loses coverage | **go** for exact instances only |
| 4. Dirty-bit policy parameter; CanonicalMemory/Compatibility and pipeline-sensitive Controls | unmeasured | 0 bankable; a conditional 2× saving applies only to actual equivalent pairs, not the whole area | high | cleaning cannot erase dirty observations or change decode failures | **no-go** for blanket replacement |
| 5. Bounded proof-generating tactic/metaprogram; repetitive Controls | unmeasured | 0 bankable; compressed source may retain all generated declarations and check cost | medium | generated terms need kernel checking at unchanged budgets | **no-go** before profiling |
| 6. Reuse Theory and existing byte/word laws; frame/store families | 0 separate from row 1 | 0 additional bankable; prove premise matches before counting any replacement | low | modular/bounded arithmetic premises may differ | **go** for exact matches only |
| 7. Delete declaration-unreached families | 0 | 0 verified by the direction graph; removal builds and theorem accounting required | high | violates this study's every-theorem constraint | **no-go** here |

Rows overlap and must not be summed. The ranking reflects measured saving per
implementation effort for row 1 versus row 2; other rows are design triage,
not measured performance rankings. The extrapolation is a bounded candidate
count, not a uniform line-ratio projection over 74,635 lines.

## Pilot

The [patch](size-tools/yul-views/pilot.patch) changes only an isolated scratch
copy. No production `Solidity/**` change is proposed for merge. The reproducible
slice is 15 files: AggregateMemoryWords, MemberArray and its Controls, plus
ArrayWordStore/Heap/Retained and StructWordStore/Heap/Retained with all six
Controls. Names are relative to the existing Views directory.

`WordLayout` describes finite whole-word cells at explicit offsets. `Reads`
is recursive; frame and store are proved by induction. Store requires equality
with the target or genuine 32-byte separation at each cell, not an assumed final
view. The array word-read theorem instantiates this relation. Existing typed
codecs, struct field-type checks, whole-map equality, reserved bytes, separate
objects and retained allocation snapshots remain in the original theorems.
The existing `heapWrite_inventory_supported` supplies support preservation; no
new support theorem, inverse or final memory agreement is assumed.
One repeated decoder induction uses the existing `of_decodes` theorem.

| Measure | Before | After |
|---|---:|---:|
| Physical lines, including all helpers/wrappers and seven Controls | 1,797 | 1,790 |
| Explicit source declarations | 218 | 226 |
| All old types/universes/axiom sets and definition bodies | 218 | identical |
| Sum of per-file median check times (seconds) | 12.424 | 12.088 |
| Largest child peak RSS (KiB) | 377,592 | 377,684 |

The 218 are explicit source declarations; generated constructors/equations are
excluded, unlike the graph's 17,904 kernel declarations. There are no new
axioms, admissions, `sorry`, `native_decide` or raised proof budgets. The driver
requires byte-identical old type/universe/axiom exports and separately audits
new helpers. Source identity also covers unchanged definitions. Earlier failed
build/axiom comparisons were fixed, not waived.

This is a finite whole-word relation. It does **not** yet replace either complete
heap-read proof, canonical codec family or allocation proof. No
storage/packed/hash/dynamic-allocation theorem is claimed by this experiment;
there is no translation-validator implementation. The next decisive pilot is
to prove both directions of equivalence with the complete old array/struct
`MemoryImage.Reads` relations, replace both heap `reads` bodies by instances,
and remeasure helper plus wrappers on this same slice with all old Controls.
Require positive structural savings and unchanged meaning/budgets before rollout.

## Execution order and preservation obligations

1. Share exact existing decoder/support/frame proofs first, retaining old definitions
   and theorem names. Preserve `decodeArrayMembers_reads`, heap `whole` and
   negative preparation/source-error Controls verbatim in type.
2. Extend the finite relation with intrinsic codec-indexed packed fields and
   struct offsets. Prove old `MemoryFields`/`MemoryImage.Reads` equivalence in
   both directions before changing a consumer; preserve typed `fields_update`.
3. Add storage dynamic arrays and mappings with actual length slot, keccak
   base and existing arithmetic/alias premises. Preserve old read/write/frame
   statements; do not hide hash separation in a typeclass or premise packet.
4. Add allocation only with actual placement separation and provenance;
   preserve `RetainedAllocation` and each `*WordRetained.whole` result. A
   fresh initial snapshot cannot substitute for original allocation history.
5. Specialize Controls and connect the relation to the separate tv-yul
   soundness theorem. Preserve every old positive/negative name, accepted
   fragment and exact success/revert/stuck result. Measure total source and
   complete checking cost before deleting compatibility implementations.

## Reproduce

With the pinned Lean toolchain on PATH, from the repository root:

```sh
python3 docs/audits/size-tools/yul-views/measure.py \
  --repo "$PWD" --worktree /workspace/yul-views-reproduce \
  --out /workspace/yul-views-reproduce-evidence --fetch-cache
python3 scripts/check-doc-navigation.py
bash scripts/check-doc-paths.sh
```

The driver refuses an existing scratch directory and evidence inside the code
checkout. It takes the writer lock, starts at the exact base, applies the patch,
builds the slice closure, then runs three emitted-output samples per file with
`LEAN_NUM_THREADS=1` and `lean -j1`. Imports are warm in both phases; totals are
sums of per-file medians, not end-to-end build times. Linux `wait4` records child
peak RSS (KiB); GNU time is absent. Virtual memory is bounded at 14 GiB, swap
must be zero, and a 2 GiB available-memory guard retains OS headroom.
There is **no systemd scope on the cloud VM (H232)**. Timings are observations,
not fixed expected values; line/declaration counts and type exports must match.
`--static-only` reproduces source counts and declaration/definition identity
without claiming Lean validation. Kernel elaboration proves mathematical model
facts, not real EVM/solc execution, physical reachability or compiler admission.
