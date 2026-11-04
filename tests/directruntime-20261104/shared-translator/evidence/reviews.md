# Independent read-only reviews

Finder and skeptic ran as separate agents; neither used Lean or the server.

Finder: extraction preserves 252 string literals in sequence, unchanged helper
bodies and intended callback substitutions. Every nested expression/type/statement
uses its callback, including falseBody. No duplicate reader remains in DirectRuntime.
Caveat: an isolated Reader.expression update does not reconnect Reader.statements.
ReaderControls pins both the disconnected case and recursive step composition.

Skeptic: Shared must not import Testing/Import (cycle). The extracted Shared local
closure is 17 modules, neither Import nor Testing. H1 must monitor outer cgroup
reserve actively; outer_guard now does. LeanTeX lacked -j1; alternate config fixed.
Docker-stop failure must not abandon monitoring; bounded cleanup now handles it.
Native/WASM builders use absolute prefix/bin/lake, bypassing PATH: still pending.

Initial finder counts were corrected by a machine comparison against pinned
compiler ASTJsonExporter.cpp: 58 Solidity JSON node kinds, 16 Yul kinds and
42 RawStmt constructors. The full catalog contains 212 feature entries.

These are preparatory reader reviews, not full assignment acceptance. Full
producer migration, fixture parity/refusals, intrinsic bridge, B/C integrations,
compiled closure/native/WASM gates and final independent reviews remain open.

Final preparatory skeptic review: no confirmed blocker to committing a partial packet. Baseline copy, source hashes, 252 strings, 17-module closure and fixture/exporter provenance independently rechecked. Finder independently corrected counts to 58 Solidity kinds and 42 RawStmt constructors. Neither review establishes full checkpoint completion.

Finder inventory correction: initial per-node feature mapping missed helper-produced pragma/builtin/magic-member alternatives. inventory.py now unions those helper branches conservatively and labels the mapping conditional. Raw mappings now include byte-literal call encoding and function-tag RawTy.named. Full per-form semantic/backend validation remains pending.

Finder final raw mapping correction: RevertStatement names custom-error RawStmt.revertErr; bare RawStmt.revert belongs to builtin FunctionCall lowering. The table marks subtype mappings as examples pending full per-form controls.
