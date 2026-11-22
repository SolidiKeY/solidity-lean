# Token economy audit

Where this repository's agent tokens go and what reduces them, measured on local
Claude Code and Codex transcripts of October–November 2026 (1,674 sessions, 111,666
model calls). Cost is billable-equivalent input tokens: cache read 0.1, cache write
1.25, output 5. Remote Codex lane transcripts are not stored locally and are not
included. Re-run with
[`token_usage.py breakdown|capsim`](token-economy-tools/token_usage.py).

## Where the cost is

| Token type | Share |
|---|---|
| Cache read (re-reading the context each call) | 73% |
| Cache write | 16% |
| Output | 8% |
| Fresh input | 3% |

73% of the cost is in calls whose context is over 200k tokens (sessions on 1M
windows). Calls that only search or read files carry 50% of the cost, mostly as
the context they re-read.

## Rejected (measured, about 1.6% together)

| Idea | Saving |
|---|---|
| Tactic portfolio before a lane writes a proof (9 tactics, kernel-checked, 269 theorems in 5.8 s) | 0.3%: it closes only one-line definitional or `simp` lemmas |
| Automatic fixes of mechanical Lean errors | 0.75–0.98%, mostly `#guard_msgs` updates, which must stay reviewed; only 19 of 1,603 unknown identifiers resolve to one declaration |
| Name lookup through the declaration index | 0.5%: most searches look for uses and text, not declarations |

## Adopted

- **Compaction at 100k tokens**: `CLAUDE_CODE_AUTO_COMPACT_WINDOW` in
  `.claude/settings.json` and `model_auto_compact_token_limit` in
  `.codex/config.toml`. The replay estimates 44–59% fewer tokens (20k–60k of
  context kept after each compaction); lost detail after compaction is not modelled.
- **Context pack**: [`context-pack.py`](../../scripts/coord-tools/context-pack.py)
  prints a task's goal statement, where the names it mentions are defined and used,
  scope outlines, importers and recent commits (about 1 s, 3k tokens), in place
  of the search and read calls that open a task.
- **One call for independent searches and reads**, and subtasks handed to fresh
  sessions with short briefs ([AGENTS.md](../../AGENTS.md)).

Re-measure with `token_usage.py --since 2026-11-22 breakdown` (and `capsim`) to confirm.
