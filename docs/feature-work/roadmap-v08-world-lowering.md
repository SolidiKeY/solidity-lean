# Callable/world lowering obligations

[Authoritative source](../../Solidity/Lowering/V08).

Call metadata, ABI bytes, accounts/funds and callback history must all refer to the same source request and reached state. Individual packet and continuation laws do not identify an arbitrary external frame with that request. Keep source-resource/world producer holds and the frozen external-call semantics intact; do not bypass them by narrowing callbacks or assuming the desired execution.
