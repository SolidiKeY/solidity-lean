# Deterministic tools audit

Which linters, analyses and checks would have found the problems this repository
actually had, measured on its history (2026-11-16, master `43b7a26ff`). Adopted tools
run in [`checks-fast.sh`](../../scripts/ci/checks-fast.sh) or
[`gate.sh`](../../scripts/coord-tools/gate.sh), so CI, lane gates and the factory's
pre-gate and land (which gate before the model review) all use them.

## Data

| Source | Size |
|---|---|
| Land reviews | 478 (387 merge, 91 blocking rounds on 48 lanes), 116 blocking findings |
| Review tokens | 317k per review on average; blocking rounds 26.9M in total |
| Fix commits since 2026-10-01 touching scripts | 195 commits, 387 before/after file pairs |
| CI regressions | 12 entries, 5 root causes |
| Lean build log of master | 504 distinct warnings |
| Declaration index of master | 116,349 declarations |

Blocking findings by kind: script logic 49, process 26, duplication 24, docs 22,
weakened tests or counts 5, dead code 5, trust 5, correctness 3, scope 3.

## Adopted

| Tool | Evidence | Cost | Where |
|---|---|---|---|
| [Declaration index](../../scripts/decl-index/decl_index.py): statement-hash duplicates and statement changes | 386 groups, 518 redundant theorems on master (12 groups read: 10 real copies); matched all three duplicates reviews had to find by hand, including renamed and requalified copies a token scan misses; 9 blocking rounds were duplication | 6 s incremental per master commit, 4 min and 5 GB for a first full index; seconds per lane | `gate.sh` with `GATE_DECL_INDEX=1`: checkpoint indexes the library into a shared cache and ratchets the duplicate count; touched compares the touched modules with the cached master index and fails on a new restated theorem |
| [`run_changed.py`](../../scripts/hygiene/run_changed.py): the workflow steps, tests and validators a merge adds or changes, run on the merged tree (Lean steps stubbed, failures rerun at base) | 13 blocking rounds failed only because new checks, tests or CI steps failed on the merged head; replayed on 464 lands, workflow steps caught 3 of 3 such cases with no false alarm on 370 merged heads; tests and validators caught 4 more but failed on about 3% of merged heads for host reasons | median 0.7 s, p90 11 s | `gate.sh touched`: blocks on workflow steps; tests and validators are advisory in the gate log |
| [`au.py --diff`](../../scripts/coord-tools/au.py): near-copies (anti-unification) of existing code among the lines a merge adds | at saving 50 it found all 10 duplication blocks, but flags 15% of merged heads (many real copies reviewers missed, some deliberate) | 0.13 s per head | advisory: the land review prompt runs it for the MAINTAINER section |
| `python_errors` count in [`quality.py`](../../scripts/hygiene/quality.py): ruff F821–F823, F63, F7, E9, PLE, B006, B008, B012 | 1 real bug (undefined name) in 195 fix commits; the 11 current findings are `exec`-defined names | 0.2 s with the pinned ruff | `checks-fast` quality ratchet |

A statement change in a touched module is listed by the declaration index;
`GATE_STATEMENT_PRESERVING=1` makes it fail, for plan steps flagged statement-preserving.
Deliberate cases pass with a `Review-Check: duplicates <reason>` or
`Review-Check: statements <reason>` trailer.

## Rejected

| Idea | Finding |
|---|---|
| Broad ruff, mypy, `tsc --checkJs`, shellcheck, eslint | 2,686 / 1,959 / 952 / 127 / 69 findings, 0 real bugs in about 25 spot checks; 0 of 49 findings next to fixed lines were the bug |
| Fail-open and lock-discipline checker for scripts | 9 of 20 review findings, but rules fitted to them; 0 hits on 387 fix pairs; about 20% precision on master (two real orphaned-child bugs, listed in the plan) |
| Gate on new Lean warnings | no warning line on master is newer than 2026-11-08 (3 lines since 2026-11-06); an earlier "doubling" compared a partial build with a full one |
| `--help` against defined flags | 12 of 706 argparse scripts, nearly all flags of other tools named in docstrings |
| lean4checker or lean4lean replay | no past incident it would catch that the axiom audit did not; `implemented_by` twins add no kernel declarations |
| Batteries `#lint` | 137 `@[simp]` attributes, 75 on `rfl` one-liners: little for simpNF |
| `shake` (unused imports) | 112 of 12,438 imports reference nothing in their closure; about 15–25 genuine |
| `autogeneralize` (ITP 2025) | 0 blocking findings, 2 notes; needs Mathlib and Lean 4.31; top clusters differ only in constants |
| Interval abstract interpretation | `omega` and `decide` close these goals; no TestSuite obligation is pending |
| VS Code tests in the gate | 13 of 595 fail without native builds; the one regression is fixed |
| Never skipping the land gate | land skips it only when the pre-gate passed the identical tree on the same master |
