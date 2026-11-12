# Prose back-test (pb1, pb2a)

This directory holds two inactive studies. **pb2a** (the additive v2 proposal,
`calibration-v2.json`) is described [first](#pb2a-history-backed-additive-calibration-v2).
The **pb1** sections after it are the original study and its published results,
kept unchanged as historical inputs. `estimate.json` is byte-for-byte unchanged.

## pb2a: history-backed additive calibration (v2)

Inactive H629 calibration study for `pb2a-prose-history-calibration`. No checker,
baseline, workflow or goal reads `calibration-v2.json`, and nothing here discharges
`pb2a-prose-ratio-goal`. The Python tests are not evidence of CI health or of any Lean proof.

### Reproduce (repository root; unshallowed history)

```sh
python3 -m unittest discover -s scripts/prose-backtest -p "test_*.py"
python3 -m unittest discover -s scripts/check-prose-budget-tests
python3 scripts/prose-backtest/backtest.py --help
PINNED=ffbeb4d4a929935bb671eb6169c88b2715a7db55
EVIDENCE_DIR=$(mktemp -d)
# pb1 original mode, unchanged
python3 scripts/prose-backtest/backtest.py --mode replay --repo . --end "$PINNED" --days 21 --estimate scripts/prose-backtest/estimate.json --output "$EVIDENCE_DIR/pb1.json"
# v2 calibration: the only command that writes calibration-v2.json (here to a copy)
python3 scripts/prose-backtest/backtest.py --mode v2-calibrate --repo . --end "$PINNED" --days 21 --lookback-days 7 --exclude docs/audits --output "$EVIDENCE_DIR/calibration-v2.json"
cmp "$EVIDENCE_DIR/calibration-v2.json" scripts/prose-backtest/calibration-v2.json
# v2 replay, twice, beside the legacy and pb1 rules
python3 scripts/prose-backtest/backtest.py --mode v2-replay --repo . --end "$PINNED" --days 21 --policy scripts/prose-backtest/calibration-v2.json --expect-policy-sha256 2688f0889571f568eb7449427b0f94b97be21552d171aa5fe9cf60692ea26f9c --pb1-replay "$EVIDENCE_DIR/pb1.json" --output "$EVIDENCE_DIR/v2-a.json"
python3 scripts/prose-backtest/backtest.py --mode v2-replay --repo . --end "$PINNED" --days 21 --policy scripts/prose-backtest/calibration-v2.json --expect-policy-sha256 2688f0889571f568eb7449427b0f94b97be21552d171aa5fe9cf60692ea26f9c --pb1-replay "$EVIDENCE_DIR/pb1.json" --output "$EVIDENCE_DIR/v2-b.json"
cmp "$EVIDENCE_DIR/v2-a.json" "$EVIDENCE_DIR/v2-b.json"
sha256sum "$EVIDENCE_DIR/v2-a.json" "$EVIDENCE_DIR/v2-b.json"
git log --first-parent --format='%H %ct' "$PINNED" > "$EVIDENCE_DIR/first-parent.txt"
awk '$2>=1792625910 && $2<=1794440310' "$EVIDENCE_DIR/first-parent.txt" | wc -l
git diff "$PINNED" --exit-code -- scripts/prose-backtest/estimate.json
# read-only evaluation of the current head
python3 scripts/prose-backtest/backtest.py --mode v2-evaluate --repo . --commit origin/master --policy scripts/prose-backtest/calibration-v2.json --expect-policy-sha256 2688f0889571f568eb7449427b0f94b97be21552d171aa5fe9cf60692ea26f9c --output "$EVIDENCE_DIR/current-head.json"
```

Each replay takes about 2.5 minutes on 4 cores. Replay and evaluation read the policy
and never write it. Both modes refuse a policy whose specification or coefficient
digest no longer reproduces. That catches hand edits such as a raised margin. An edit
that also recomputes the embedded digests is caught only by `--expect-policy-sha256`,
which pins the SHA-256 published above. The policy's SHA-256 is taken before and after
each run and must match. A replay with the frozen end and day count must reproduce the
frozen window's commit digest. Any other window is reported as
`window_matches_policy: false`.

### Frozen specification

The selection rules use area existence and committer timestamps only. They never look
at counts or failures.

| Item | Value |
|---|---|
| Endpoint | `ffbeb4d4a9…` (tree `3c5d13ea…`, committer ts 1794440310) |
| Universe | 37 endpoint areas plus every area present at any first-parent commit of the 21-day window: 38 areas |
| Coverage anchor | `86c2fd3658…` (ts 1794271069): the earliest first-parent commit that contains every endpoint area. It is where `Solidity/Goals` first appears, and it calibrates 37 areas |
| Late anchor | `84e9aff49c…` (ts 1794239805) for `Solidity/Scratch`. Scratch lived for 8 first-parent commits and was deleted before Goals appeared, so no single commit contains Correctness, Goals and Scratch. The rule for areas missing at the coverage anchor is the latest earlier commit that contains them |
| Lookback | The contiguous first-parent run ending at each anchor and stamped within 7 days before it: 938 and 976 commits. The policy stores each list's SHA-256, and the private evidence holds the full lists |
| Denominators | Solidity areas use their own handwritten code lines (`self`). Docs areas use all `Solidity/` code (`repository-solidity`). This is pb1's mapping, unchanged |
| Classifier | `verified-generated/2`: the verified list is **empty** (see below), so every generation claim counts as handwritten |
| Enforcement exclusion | `docs/audits` only (H548, until r1). It is calibrated, measured and reported on every row |
| Spec digest | `a4e06bc8c69a1cdb…` (spec/2), recorded before the v2 replay. Policy SHA-256: `2688f088…` |

**Revision history (not concealed).** Spec/1 (digest `17119abad7c5…`) used only the
coverage anchor and was replayed first. That replay showed `Solidity/Scratch` on the
zero fallback, because Scratch is absent from the endpoint and from the coverage anchor.
Spec/2 adds only the count-free late-anchor rule. The coefficients, margins and
witnesses of the other 37 areas are identical to spec/1's; each entry only gains an
`anchor` field. Spec/1's policy and replay are kept in the private evidence. The current
code emits only spec/2, so spec/1 cannot be regenerated.

Under spec/1, Scratch failed 16 cells in 8 lookback commits on the zero fallback. Under
spec/2 every Scratch commit lies in its own lookback, so it cannot fail. Scratch's v2
result is therefore post hoc and carries no evidential weight.

The method text says lookback commits are stamped inside the interval. Commits in the
contiguous run stamped after their anchor would also be included, but they are listed
under `stamped_after_anchor`. There are none.

### Rule

For each area and metric (`docs_lines`, `comment_lines`, `docstring_lines`, `process_ids`)
the policy stores a reduced rational ratio `r = a/b` and an additive margin `m = c/e`, both
nonnegative. A count `n` over denominator `d` passes when `n ≤ r·d + m`. The test is the
integer comparison `n·b·e ≤ a·d·e + c·b`, with no floating point and no tolerance. The
stored `allowance_floor` is display only: for an integer `n`, `n ≤ floor(allowance)`
exactly when `n ≤ allowance`.

- `r = n_A/d_A` at the area's anchor. The case is `ratio`.
- `m = max(0, max over lookback commits containing the area of n_c − r·d_c)`, kept as an
  exact rational. It is the smallest additive margin under which every lookback commit
  passes with the anchor ratio. The policy records the witness commit.
- `zero_numerator` (`n_A = 0`, `d_A > 0`): `r = 0`, and `m` comes from the lookback.
- `zero_denominator` (`d_A = 0`): no ratio is invented. `r = 0` and `m` is the largest
  lookback count. Nothing is ever divided.
- **A zero ratio is not a zero denominator.** `r = 0` with `m > 0` is a flat allowance of
  `m` at any denominator, including zero. A zero denominator at evaluation only means that
  `r·d = 0`, so the allowance is `m`.
- **Fallback:** an area outside the policy gets `r = 0, m = 0` for every metric. That
  covers areas first seen after the window and areas with no anchor (none now). Only
  `n = 0` passes, and a new area never trains its own allowance. Areas are never
  silently dropped.

Metric reach is the same as pb1's:
- Docstring lines are a subset of comment lines and are never added to them.
- Process IDs count occurrences and keep the registered-root import exemption.
- A code line needs a non-whitespace character left after the comment spans are removed.
  Blank lines, comment-only lines and whitespace-only lines inside strings never count.

**Generated content.** v2 excludes an item from both numerator and denominator only when
it appears in the policy's `verified_generated` list. Its path, its blob, and its
generator's blob at that commit must all match the entry. A header that names an
existing script is not enough.

Verification would mean running each generator's `--check` on an exported tree. In this
lane that execution was refused, so **no item is verified**. All 40 claims at the coverage
anchor are counted as handwritten (pb1 excluded 28 of them at the endpoint), along with
every claim seen in the replay. pb1's `generated-rule/1` stays available, unchanged, in
the pb1 modes. The tests cover blob-bound exclusion, lapses after an output or generator
edit, and false-header padding.

### Results (21 days ending at the pinned endpoint; 1265 first-parent commits)

Failing commits / failing cells. Introduced, inherited and reintroduced cells are counted
separately. The legacy rule and pb1 come from the original-mode replay of the same commits.

| Position (relative to the coverage anchor) | Commits | Legacy absolute | pb1 ratio (1/20) | v2 additive |
|---|---|---|---|---|
| Before lookback (coefficients from later history) | 275 | unavailable (no checker) | 275 / 6063 | 271 / 4082 (17 introduced, 4052 inherited, 13 reintroduced) |
| Calibration lookback (**in-sample**) | 937 | 164 / 2503 (only 165 evaluable: 772 had no checker) | 803 / 10335 | 0 / 0, by construction of the envelope margin. Scratch is 0 only because of the spec/2 revision |
| Anchor | 1 | 1 / 26 | 1 / 8 | 0 / 0 |
| After anchor (post-calibration, retrospective) | 52 | 52 / 1666 | 52 / 495 | **50 / 211** (7 introduced, 204 inherited) |

The legacy rule is unavailable for 1047 commits that had no checker or baseline. It is
evaluated for 218. Legacy process IDs stay unavailable for the commits that ran checker
semantic version v2, as in pb1. There is no
out-of-sample validation:
- The lookback lies inside the window.
- The anchor was chosen using area existence at the endpoint.
- The margin is an envelope fit to the lookback.

**Residual failures after the anchor (all 7 introduced cells, then inherited):**

| Area / metric | First introduced at | Cause |
|---|---|---|
| `Solidity/Goals` comment, docstring | `f949ed133` | 16→21 over 98→113 code, then growth to 675 over 1471 at the end (allowance 23536/97 ≈ 242.6). Genuine density growth in a 1-commit-old calibration |
| `Solidity/Goals` process IDs | `f949ed133` | 1→3 IDs over 113 code lines (allowance 113/97) |
| `Solidity/Correctness` process IDs | `1bd89144b` | 26→107 over 600→2284 code (allowance 7423/75 ≈ 99) |
| `Solidity/Lowering` process IDs | `e8f63bc2a` | 468→472 over 86016→86251 (allowance ≈ 469.3) |
| `Solidity/Yul` comment, docstring | `903b07f21` | +40 prose lines over +62 code lines, density above the anchor ratio plus its margin |

At the endpoint, v2 fails 5 cells: Goals ×2, Lowering IDs, Yul ×2. Legacy fails 36 and
pb1 fails 10.
- **Correctness:** fails only on process IDs. Its comment and docstring lines pass.
- **Scratch:** passes everywhere, but entirely in-sample. All 8 Scratch commits lie in its
  own lookback, so this proves nothing about the rule.
- **docs/audits:** does not fail. It has 368965 lines at the end against an allowance
  floor of 371812. Its margin is only about 194 lines. Most of the headroom comes from the
  shared denominator: Solidity code grew from 889524 to 896794 lines, and the ratio scales
  with it. It stays outside enforcement.
- **Before the lookback:** the failures (Calculus, Counterexamples, Evm, Examples, Solkey,
  TestSuite, Tools, Typing, `_root`, `docs/_root` …) are earlier states with denser prose
  than the later anchor allowed.
- **Shrinkage:** 21 v2 cells carry `denominator_shrank`; 2 of them are after the anchor.
- **Positions:** commits are labelled relative to the coverage anchor, including Scratch rows.
- **Prior status:** classification uses failures inside the window only. A failure at
  the boundary predecessor alone does not make a later one "reintroduced". The legacy and
  pb1 columns follow the same rule.

Every failure row in the private index carries its numerator, denominator, exact
allowance, prior counts and status, classification, anchor and causes.

**Margin weakness.** The envelope rewards prose cuts made during the lookback. For
example, docs/feature-work has 237809 lines at witness `513b4815`, against 114690 at the
anchor, which gives a margin of about 124971 lines. Backend's margin is about 3128 lines
and docs/benchmarks' about 36167.

Code growth during the lookback inflates margins as well. For 20 of the 38 areas the
witness is the oldest lookback commit, which had about 1486 Solidity files against 6810
at the anchor. docs/_root's margin is about 20061 lines, and Tools, Roadmap, `_root` and
Precompiles are similar.

Such margins make v2 lax. This is a property of the frozen policy, and it is reported
here instead of being tuned.

### Verification

- **Commit set.** An independent `git log --first-parent` plus `awk` filter of the
  inclusive interval [1792625910, 1794440310] gives 1265 hashes, identical in order to
  the replay's list. Boundary predecessor: `83ad39cbd1…` (ts 1792624132), used for deltas
  only. History is unshallowed. There are no non-monotone timestamps, and no older commit
  is stamped inside the window.
- **Determinism.** The two v2 replays are byte-identical (`cmp`; SHA-256 `d57fe5c4…`). The
  policy SHA-256 is equal before and after. The pb1 original-mode replay is byte-identical
  before and after this change, and `estimate.json` has no diff against the pinned commit.
- **Spot checks.** A separate script recomputed counts and arithmetic with `git show`. It
  does not import `backtest.py`. It covered:
  - anchor counts for Correctness, Goals, Scratch, `docs/README.d` and Corpus (Corpus
    includes generated-claimed files): 20 checks;
  - 4 margin witnesses, including Scratch;
  - 6 failing cells: the first introduced failures of Correctness, Goals, `docs/_root`
    and Syntax, plus 2 `denominator_shrank` cells. Scratch has no failing cell to check.

  All 30 checks agree. The script's independence has limits:
  - Comment and code lines come from its own tokenizer. Docstring lines and process IDs
    come from the reference checker's `_Scanner` and `process_ids`, which define the
    measured semantics.
  - The tokenizer first disagreed in two ways. After a per-file comparison it was
    corrected toward the documented rule. First, it skipped blank lines inside block
    comments, which the checker counts. Second, it counted whitespace-only lines inside a
    string, which are not code.
- **Current head.** `origin/master` equals the pinned endpoint (same commit, tree
  `3c5d13ea…`). The read-only evaluation finds 5 failing cells and no area outside the
  policy. It did not alter the calibration.

### pb2-prose-ratio-rule blockers

1. **Generated verification.** No generated item is verified, because generator
   execution was not permitted. An accepted way to verify by reproduction is still needed.
2. **Margin policy.** The envelope margins are lax for areas whose prose fell during the
   lookback (feature-work, benchmarks, Backend). A margin rule that does not reward cuts
   needs a decision before activation.
3. **No out-of-sample evidence.** All calibration inputs overlap the window. Only 52
   commits follow the anchor, and the new areas have 1 (Goals) to about 125 (Correctness)
   lookback commits. A held-out period after freezing is needed.
4. **Unresolved residual failures.** The Goals, Correctness, Lowering and Yul failures at
   the end need explicit allowance decisions. They cannot be erased by raising margins.
5. **Merge-gate path name.** The mandated file name `calibration-v2.json` fails the
   hygiene path rule (a `v2` segment). The fix lies outside this study's write scope.
6. **Inherited provenance.** The pb1 review provenance stays UNVERIFIABLE (H151). Fresh
   runs do not recover it. The docs/audits enforcement exclusion lasts until r1 (H548).

Full rows, failure indexes, selection lists, reconciliation, spot checks and logs are in
the private evidence (H145): see the lane result for the `evidence:` reference.

## pb1 study (original, historical)

Read-only study for pb1-prose-backtest. It replays the per-area prose ratchet
(`scripts/check-prose-budget`) over 21 days of first-parent master history and
compares it with a **proposed, inactive** code-relative rule. Nothing here is
wired into CI. `estimate.json` is a proposal and does not set any budget.

### Reproduce

```sh
python3 -m unittest discover -s scripts/prose-backtest -p 'test_*.py'
python3 scripts/prose-backtest/backtest.py --help
# replay (reads estimate.json, never writes it); run twice and cmp
python3 scripts/prose-backtest/backtest.py --repo . \
  --end 5b78e2313ed50233a7a8373354b0e4586fd75c9e --days 21 \
  --estimate scripts/prose-backtest/estimate.json --output /tmp/pb1-replay-a.json
# separate, explicit calibration (the only operation that writes an estimate)
python3 scripts/prose-backtest/backtest.py --mode calibrate --repo . \
  --calibration 33e91288c226c7055b1dc212d709024d6730b04d --margin 1/20 \
  --sensitivity 0,1/20,1/10 --exclude docs/audits \
  --mapping '{"docs/_root":"repository-solidity", ...}' \
  --baseline-commit 87d3d3c95be4e4cfd6cf41173ea5d7fc4d0f7ca0 \
  --baseline-blob 93a344e0d318319ce78323c98db6f2bbbe3792ed \
  --review 'UNVERIFIABLE: ...' --versions '{...}' --output estimate.json
python3 scripts/prose-backtest/backtest.py --mode audits-inventory --repo . \
  --commit 5b78e2313ed50233a7a8373354b0e4586fd75c9e --output /tmp/audits.json
```

`estimate.json` stores the exact `--mapping`, `--versions` and `--review` values.
The tool reads Git objects only: `ls-tree` and `cat-file --batch`. It caches
results by blob ID. It reuses the scanner in the current `scripts/check-prose-budget`,
and that file's blob must equal the end commit's copy. It never runs historical
scripts and never checks out a tree. One full replay takes about 2 minutes on 4 cores.

### Frozen inputs

| Input | Value |
|---|---|
| End | `5b78e2313ed50233a7a8373354b0e4586fd75c9e`, committer time 1794392178 (2026-11-11T10:16:18Z) |
| Interval | [1792577778, 1794392178]: end minus 21×86400 s, inclusive. Commits are filtered by exact committer timestamp, not the wall clock |
| Commits | 1276 first-parent commits, from `2fc265f74a…` to the end. An independent `git log --first-parent` plus `awk` count also gives 1276 |
| Boundary predecessor | `550cbc015acce743f4e749519bb9de21cc970e8b` (ts 1792577132). Replayed only to supply deltas |
| History | Unshallowed before the run (`shallow=false`). No out-of-order or late-stamped first-parent commits |
| Reviewed baseline | Blob `93a344e0d3…`, set by `87d3d3c9` "Refresh initial prose limits for published master 33e91288" and merged by `dfdfa238b`. The baseline has not changed on first-parent since |
| Calibration tree | `33e91288c2…`, the first-parent commit just before `dfdfa238b` |
| Review provenance | **UNVERIFIABLE.** No review record for `87d3d3c9`/`dfdfa238b` is reachable in this repository's history, and a commit subject is not evidence of review. The calibration is therefore **provisional** |
| Classifier | Checker blob `8c7cdbb954…` (v3) plus `generated-rule/1` |
| Margin | 1/20, fixed before any replay (see below) |

The legacy counts at `33e91288` reproduce the reviewed baseline exactly for
docs, comment and docstring lines in every area. Process IDs match only under the
v1 raw-count semantics (Backend 1242, Lowering 420), which shows the v1 checker
produced the baseline.

### Method

**Metrics.** The four metrics are measured independently for every area. Docstring
lines are a subset of comment lines and are never added to them. Process IDs count
occurrences, not lines, and keep the registered-root import exemption.

**Code lines.** A code line is a physical line that still has a non-whitespace
character after the scanner's comment spans are removed. The removed spans are the
actual comment character ranges, not whole lines. Mixed lines, nested comments,
strings, character literals and `«…»` identifiers are handled; the tests cover each.

**Generated content** (`generated-rule/1`) is excluded from both prose and code.
There are two cases:

- **Header.** A capitalised `Generated by` / `Auto-generated by` must appear in the
  first 15 lines. In Lean it must sit inside a comment; in other files it must start
  a line, optionally after `<!--`, `#` or `//`. A `scripts/…` or `tests/…` generator
  path must follow it, and that path must exist in the same commit.
- **Block.** Lines between matched `BEGIN generated by P` and `END generated by P`
  markers are excluded, again only when `P` exists in the same commit.

A claim whose generator path cannot be resolved is **kept as handwritten** and
listed as unknown. Over the window, 15 distinct paths fall in this group, mostly
`Backend/Passes/*Pins.lean`, which name a `scripts/v09/` generator that is absent.
Excluded files at the end commit: 23 by header (20 Lean, 3 docs) plus
5 blocks. Each commit has its own list; the first and last commits list them in
full, the others carry a digest.

**Denominators.**

| Areas | Denominator | Why |
|---|---|---|
| Solidity areas | The area's own handwritten code lines | Prose belongs to the code it describes |
| All docs areas | Handwritten code lines across all of `Solidity/` (`repository-solidity`, clearly labelled) | Docs folders are organised by document kind, not by code area, so no narrower mapping is defensible |

Prose and data files never count as code.

**Rule** (proposal only). For each area and metric, the calibration supplies a
numerator `cn` and a denominator `cd`. A count `n` over denominator `d` passes when

`n · cd · q ≤ cn · (p + q) · d`, where the margin is `p/q = 1/20`.

The test is exact integer arithmetic with no rounding. Edge cases:

- If `cn = 0`, `cd = 0` or `d = 0`, only `n = 0` passes. Zero code with prose never
  passes and never yields an invented ratio.
- An area absent at calibration (unseen) gets a zero allowance and cannot train its
  own.
- There are no absolute floors.

The calibration has no areas that the baseline lacks, and the baseline has none
that the calibration lacks. Areas created during the window, such as
`Solidity/Correctness`, `Scratch` and `Goals`, appear as unseen.

**Margin.** 1/20 was chosen before any replay. This is the author's statement; the branch history cannot prove the order, because the study was committed after the runs. It is a small headroom for
commit-level noise in the prose/code mix and stays well below the ratio spread
between areas. It was not tuned. Sensitivity at 0 and 1/10 was declared in
advance and is only reported below.

**Calibration position.** The calibration commit lies **inside** the window
(commit 192 of 1276 counted back from the end). The result is therefore a
retrospective calibration, not out-of-sample validation, and results are reported
separately for the 1083 commits before it and the 192 after it.

**Legacy replay.** The legacy replay applies each commit's own committed baseline
and the checker semantics of that commit's version, treated as data:

| Version | Commits | Semantics |
|---|---|---|
| v1 `1dc25b10` | 65 | Raw process-ID regex |
| v2 `38c0263a` | 23 | Process IDs **unavailable** (unsupported semantic version). The other metrics are faithful because the scanner code is unchanged |
| v3 `8c7cdbb9` | 104 | Current semantics |

The other 1084 commits had no checker or baseline, so their legacy result is
**unavailable**, not a pass.

### Results

The counts below are failing commits out of the commits in each range.

| Rule | Before calibration (1083) | After calibration (192) |
|---|---|---|
| (a) Legacy absolute, historical baseline | n/a (no checker) | **191** fail. Only `dfdfa238b` passes. 3261 cells, 49 introduced |
| (b) Normalized absolute (frozen counts at calibration) | 934 | 191. 3471 cells |
| (b) Frozen ratio, margin 1/20 | 985 | 157. 779 cells |
| (b) Ratio, proposed enforcement (docs/audits excluded per H548) | 985 | 157. 734 cells, 12 introduced |
| Sensitivity, margin 0 / 1/10 (enforced) | 1083 / 985 | 191 / 154 |

**Legacy replay is checked against the real checker.** The current checker was run
on `git archive` exports of `5b78e231` (32 failures) and `afe79c9d` (20 failures).
Its failure lines match the replay exactly.

**What the results mean.**

- **Master has failed its own prose ratchet at every commit since the one that
  added it.** The baseline was never lowered or refreshed, and growth accumulated
  unchecked. Among the 3261 legacy failure cells after calibration, 2833 carry the
  `unchanged_counts` label and 527 the `area_absent_from_baseline` label. The labels overlap, so these are not a partition.
- **The ratio rule absorbs proportional growth.** For example, `71175a9a6` added
  32 Lowering comment lines alongside new code: the absolute rules fail, the ratio
  passes, and the cause is `code_rose_with_normal_prose`.
- **The ratio rule still catches real prose increases:**
  - `9f2dcae6b`: Lowering process IDs went from 376 to 440 while code went from
    83877 to 84542 lines, against a limit of 396.
  - `7098bb1fe`: Examples process IDs went from 19 to 20 with no code change. This is one added `(H134)` citation: a correct catch, but a small one.
  - `4e023e56e`: `docs/README.d` went from 19 to 20 lines.
- **Most of the ratio failures after calibration are carried over from new areas.**
  `Solidity/Correctness` was first failed at `d07fc9844` (336 comment lines over
  600 code lines); `Scratch` and `Goals` are similar. Under any rule these need an
  explicit allowance decision. They cannot train their own allowance.
- **docs/audits (H548)** is measured on every row but kept out of proposed
  enforcement. At the end it has 368965 lines, against a legacy limit of 231740 and
  a hypothetical ratio limit of 247124. The ratio rule's first introduced failure
  there was at `84e9aff49`, where the area went from 217570 to 246799 lines with
  no code change.

Each failure carries its cause labels: `prose_rose_without_code`,
`code_rose_with_normal_prose`, `code_and_prose_rose`, `denominator_shrank`,
`unseen_area`, `zero_code`, `absolute_limit_exceeded`, `ratio_exceeded_frozen_allowance`,
`prose_where_calibration_had_none`, `area_absent_from_baseline`, `unchanged_counts`, or
`prose_fell_still_over`. A failure can have more than one cause. Each one is also
marked as introduced or carried over, together with the prior status.

### docs/audits inventory (end commit, read-only)

| Class | Files | Lines |
|---|---|---|
| Handwritten prose (`.md`) | 10 | 2368 |
| Scripts or source (`.py`, `.sh`, `.lean`, `.patch`) | 167 | 18706 |
| Data that a writing script names (regenerability unverified) | 135 | 146030 |
| Data with no generator evidence | 184 | 195132 |
| Unknown (`declgraph/modules.txt`, `proof-coverage-tools/statement-sample.txt`) | 2 | 6729 |

The line counts sum to the measured 368965. The directory is mixed. **No file was
verified as reproducible**, because generators were not run in this read-only
study. For example, `direction-tools/README-results.json` is named by
`README-calibrate.py`, and the census JSON files are named by `census/metrics.py`
and `trend.py`, but neither is proven. The JSON extension alone is never treated
as evidence.

Generated-file normalization (`generated-rule/1`, which matched no docs/audits
file) is separate from H548's temporary enforcement exclusion. No deletion or gate
change is recommended in this step.

### Limitations

- The calibration is provisional because its review provenance is UNVERIFIABLE.
  It is also retrospective, because the calibration commit lies inside the window.
- Legacy process IDs are unavailable for the 23 v2 commits. Legacy results are
  unavailable for the 1084 commits that predate the checker.
- The docs denominator is repository-wide (about 875k code lines). That is an author judgment, not a proof that no narrower mapping exists, and it makes docs ratios behave almost like absolute limits.
- The generated rule trusts a header that names any existing script; it does not check that the script writes the file. A false header could remove a handwritten file from both prose and code. At the end commit the rule removes 28 items, none of them in docs/audits.
- Process IDs inside a generated block that sit on header-import lines are not subtracted, so they cannot be removed twice. Symlinks and undecodable registry roots mark legacy as a checker error (none occurred). A first-parent ancestor stamped before the window start ends the walk; later in-window stamps beyond it would only be listed (none occurred).
- The generated rule keeps 15 claimed-generated paths with no in-tree generator
  as handwritten, which may overstate prose in Backend.
- docs/audits regenerability is unverified.
- No sequential shrink-only simulation was run.

Full outputs are archived privately and are not stored in this branch. They
contain the replay JSON for every row, the complete failure index, the commit
summaries, the audits inventory, the checker spot-check, and run logs. Pushing
them to the private evidence repository was refused (no credentials), so they
remain on the lane VM with a SHA256SUMS manifest cited in the lane result.
