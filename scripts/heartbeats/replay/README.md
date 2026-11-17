# Heartbeat budget for the fresh Derived17 replay

`scripts/check-memory-loop-timing.py` checks the 24 modules of the original
Derived17 workload freshly, in order, each against the previous ones' fresh
outputs. Its speed budget is heartbeats (H1076): the same count on every
machine, unlike wall time. The seconds budget (`--budget`, 300 locally, 600 on
CI) stays as a backstop with its old default.

```
python3 scripts/check-memory-loop-timing.py --output DIR --results FILE [--budget S] [--tolerance PCT] [--baseline FILE]
python3 scripts/check-memory-loop-timing.py --write --output DIR --results FILE   # regenerate baseline.json
```

## Driver

Each module is checked by `Replay.lean`, which does what
`lean --setup SETUP SOURCE -o OLEAN -c C` did before, with `Elab.async=false`
(so kernel checking runs on the counting thread), one thread and a 128 MiB
stack, and reads `IO.getNumHeartbeats` around each command as the shared
collector does (`scripts/heartbeats/README.md`). The script compiles it once
per source and toolchain into `.lake/build/heartbeats-replay/` (about 15 s,
outside the timed workload); its wall time per module matches `lean`.
It writes `DIR/MODULE.heartbeats.json` in the collector's shape.

## Ratchet

`baseline.json` holds every module's total, each command of at least 10 units,
and the workload total as the entry `workload:fresh-original-Derived17`.
The comparison is `scripts/heartbeats/collect.d/ratchet.py check` with
`--tolerance 2`: an entry fails when it exceeds its baseline by more than 2% and
by more than 1 unit; a decrease, a new or a removed entry only prints. A ratchet
failure, like an exceeded seconds budget, makes the exit status and the results'
`exit_code` 1.

Regenerate the baseline with `--write` on the merged head (or the merge base)
and check it in. `--write` replaces the file; it is written only when every
module checked without errors.

## Results

The `--results` JSON keeps every earlier field. New fields: per check
`heartbeats`, `importHeartbeats` and `heartbeatsFile`; at the top `heartbeats`
(workload total), `heartbeatBaseline`, `heartbeatTolerancePercent` and
`heartbeatRatchet` (`mode`, `exit_code`, `failures`, and for `check` the
ratchet's `report` lines). Heartbeats are in `maxHeartbeats` units (raw / 1000).
