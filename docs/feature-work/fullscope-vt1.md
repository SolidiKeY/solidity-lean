# Solc validation boundary

[Authoritative source](../../Solidity/Frontend).

Translation validation must bind the exact solc version/settings and complete produced artifact to the independently specified source and target observations. Arity-indexed dialect metadata or validator self-consistency is not authenticated execution/layout/gas agreement. The authorized [full-scope target](full-scope.md) remains unchanged.


## T01 C11: hex-string expressions

The parser now imports hex byte literals as intrinsic `LitTok.hex` values,
prints the exact normalized hex token, and checks the existing `Parsed.sound`
token/scoping certificate. Expression decoding uses the existing `stringWord`
left-aligned byte semantics; values longer than32 bytes reject without truncation.
Object-data bytes retain their existing unrestricted length. This removes the
hex-expression refusal; remaining parser/semantic obligations are still open.

`IrHex` proves decoding, token preservation, recognition, equality with ordinary
strings containing the same decoded bytes, >32-byte rejection, and actual
`evalExpr` preservation of arbitrary machine state for a certified literal.
The decoded-value equation is the intrinsic literal constructor's certificate,
not an assumption that a whole program matches its source. No compiler execution,
native EVM/physical memory, full interpreter refinement or T02 matching is claimed.
The six observed standard-axiom sets are checked with guard_msgs. No new axiom,
sorry, native_decide, exclusion, theorem weakening or raised budget.

Kernel controls cover empty and nonempty literals, exact word values and byte
order,32-byte maximum,33-byte refusal,33-byte object-data acceptance, malformed
hex, wrong arity, object labels, token preservation and duplicate hex/string
switch cases. Existing parser regressions pass all four saved real solc fixtures
plus altered-input controls. Those fixtures are T01 parser evidence, not T02
compiler authentication. Initial direct big-word reduction hit default recursion
depth; ordinary kernel decide checks the identical expected values without
raising limits. Separate read-only finder/skeptic reviews found no concrete
issue; the suggested full-parser33-byte boundary was added. Neither used Lean
or its server. Their conclusions and exact commands/timings are external evidence.

Warned before the literal-constructor extension and checked relevant history:
no speed-motivated change is undone. Before:syntax+parser3.939s. After:syntax1.596s,
parser1.905s (later rebuilt1.5/1.7s); no observed slowdown. New proof module0.244s;
first prerequisite closure12.161s (including existing evaluator4.7s). Controls
2.183s; old parser regression9.969s. No focused module above60s. Per-file MCP
initial diagnostics0 errors in syntax/parser/proofs; final checks are sealed.

The local serial Lake config is refreshed from current master with only frontend
-j1 added, retaining H109 slow-library/default-target policy. It changes no root
configuration. Docker hard12GiB/no-swap, CPU1, LEAN_NUM_THREADS1, one observed Lean
frontend, >=4GiB admission/ongoing reserve,180s/file and300s/group remain guarded.
Generated roots/maps/pins stay central: register Solidity.SolcValidation.IrHex
and its six pins through serialized integration. Exact final gates, HEAD,
reviews, cache identity and checksum-bound handoff are archived with coord-evidence.

T02 wait:normal inherited-proxy request to
https://binaries.soliditylang.org/linux-amd64/list.json returned HTTP403 and
curl56 CONNECT tunnel failed on2026-11-08. Per coordinator instruction, T02
remains blocked until this endpoint is reachable; no alternate route/compiler
is used to work around that wait. T01 implementation takes priority over backfill.
