# Slow example heartbeat baseline

`baseline.json` holds the hb0 ratchet baseline (format: `../README.md`) for the
H109 slow examples, which `scripts/ci/build-slow-examples.sh` checks (H1076). A module
that is rebuilt is elaborated once, by the collector, and it fails when it or a recorded
declaration grows by more than `SLOW_EXAMPLE_HB_TOLERANCE` percent (default 2) and more
than 1 unit. A module that is already up to date (from the Lake cache) is skipped as
unchanged. A decrease, a new entry or a removed entry only prints. A missing file makes
every module new.

Regenerate on the merged head (or the merge base) and check the file in:

```
lake build Solidity SolidityExamples
scripts/ci/build-slow-examples.sh --write
```
