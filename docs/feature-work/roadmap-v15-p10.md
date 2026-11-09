# Fetched-byte correspondence

[Authoritative source](../../Bridge/SolidityBridge/RoadmapV15/P10).

A constructed opcode site is not automatically a reachable state of compiled contract code. Site recovery needs the actual code image and PC; fixed-code/session and resource assumptions must refer to that same execution. Individual fetched-step results do not establish complete Source/Osaka/transaction adequacy.

G01 operational linkage for VX1 remains open under H133. The authenticated consumer snapshot `6cff82c7dcde5d21792a9467486f54408cf11f1a` declares `FullScope.Target`, `RunIndexed.TargetRuns` and `V1.Alignment` in the external snapshot files Solidity/Language/EnvironmentFields/Contracts.lean and Solidity/Language/EnvironmentFields/Frozen.lean; those files are not present in this master baseline. Its target requires a concrete execution semantics, artifact loader and query reader. `TargetRuns` additionally requires the ordered query transcript to match the same execution's scalar-read events and reader values. Operational alignment must relate that execution's environment and resource to the admitted Source run.

`Solidity/Roadmap/Evm.lean` supplies abstract pinned semantics and resource contracts, not this concrete adapter. The P10 [frozen interface](../../Bridge/SolidityBridge/RoadmapV15/P10/FrozenInterface.lean) explicitly excludes resource abstraction and transaction/trace adequacy. Per-opcode fetched-step results and self-certificates therefore cannot discharge the G01 consumer contract. Source admission remains an upstream obligation; no Source definition or frozen interface was changed.

The executable-bytecode lane owns this linkage. H275 selects an existing authoritative target/resource implementation and current consumer contract; the adapter must preserve their semantics. The route decision for `Q-G01-OP-BOUNDARY` is closed. Their exact implementation and current-consumer heads, declaration paths and provenance remain required delivery inputs; the decision itself does not identify them. This boundary review supplies no operational certificate, source/runtime correspondence or joint-witness credit; VX1 must retain its G01 wait.

Exact consumer/source hashes and independent review inputs are archived privately:

```text
evidence: 2075831f0e6a38802a55b4af469a7adc0fda9551 evidence/solidity-parallel-20261103/executable-bytecode/g01-boundary-6751cbbe.json
```
