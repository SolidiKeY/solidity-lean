# Editor parity evidence

`constant.sol` and `constant.dfy` are the reduced shared workload: `f0` proves,
and `f1` has a false postcondition. Solidity uses the repository's actual
`@custom:key ensures \result` annotation. Ignoring an unrecognized NatSpec tag
would invalidate the comparison.

The live harness generates repeated true/false variants of this fragment.
Runtime artifacts belong under `.cache/editor-parity/` and include JSON results,
raw protocol traces, process samples and renderer observations. The
[harness guide](../../docs/dafny-editor-parity.md) gives reproduction commands,
methodology and limitations. The checked-in baseline summarizes completed runs;
it is descriptive evidence on the recorded machine, not a universal performance
threshold or claim of full parity.

[baseline.md](baseline.md) is the human summary;
[baseline.json](baseline.json) retains the machine-readable measurements and
per-feature evidence. [audit.json](audit.json) records independent rediscovery,
review findings, repairs and remaining work. Failed pre-fix launcher attempts are
listed separately in the baseline instead of contributing timing estimates.
