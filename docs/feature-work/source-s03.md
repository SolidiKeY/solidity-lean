# Source statement semantics

[Authoritative source](../../Solidity/Source).

Statement/modifier/constructor behavior must remain independent of lowering. Repeated modifier placeholders, initialization order and reached failure states are semantic obligations, not optional compiler conveniences. A finite execution witness does not establish unrestricted recursion/termination or full source-language coverage.
