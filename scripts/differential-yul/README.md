# Differential Yul runner

The runner compiles deterministic small Solidity programs with the pinned solc
loader shared by `scripts/differential`, deploys their bytecode in the reference
EVM, and compares both emitted IR forms with the explicit stateful Lean driver.
It compares exact return/revert bytes, revert status and physical storage slots
0 and 1. The generator owns both storage words; constructors initialize neither.

After the stateful Yul prerequisite lands, compile a driver executable whose main
is `Solidity.Yul.StatefulImport.driver`. The runner requires its path explicitly;
there is no substitute interpreter or fabricated expected-value oracle.

```
node scripts/differential-yul/run.mjs --compiler /absolute/soljson.js \
  --driver /absolute/stateful-yul-driver --output /external/new-run
```

The default is 2,000 distinct programs with seed 1128, both IR forms, serial
execution, 10,000 Lean fuel, a 4,096-byte output bound and a 60-second per-driver
timeout. Optional flags: `--count`, `--seed`, `--fuel`, `--output-limit`, `--timeout`.
`--input FILE` may repeat to fingerprint additional driver/library build inputs.
Recorded hashes cover the listed files, not a complete transitive build proof.
Keep the compiler, driver and libraries immutable while running. Temporary IR
and all outputs must stay outside the checkout; the output parent must exist,
and the run directory must be new.

Exit 0 means every requested program completed both comparisons and agreed.
Exit 1 means completed comparisons include mismatches; exit 2 means a refusal,
process failure, incomplete campaign or harness error. Fuel/resource exhaustion
and unsupported syntax are not counted as agreement or as EVM reverts.
`observations.jsonl` preserves submitted programs and results. `report.json`
marks a completed observation campaign, which may still contain blocked cases.
Mismatches produce external `findings/<sha256>.json` with stage-specific operand
minimization; `complete:false` explicitly records incomplete shrinking. Findings
start untriaged and must be investigated before delivery. Never commit these run
outputs. Archive evidence through the coordinator tooling.

```
node --test scripts/differential-yul/*.test.mjs
```

Adapter and orchestration unit tests use injected processes. They do not establish
Lean/EVM agreement. Actual campaigns are external tests, not kernel proofs or a
proof of the `differentialAgreement` tracking goal.
