# Ordinary calldata alias origins

Integration status (2026-10-26): included in the shared checkout. Current
combined validation is tracked in [integration.md](integration.md).
Worker handoff statuses and isolated validation results below are historical;
they neither report the current combined checks nor establish full source support.

Ordinary `T calldata v = e` declarations no longer become unchecked memory
aliases when `e` is not an explicit slice descriptor. `RawStmt.sliceViews`
accepts an optional list of known calldata roots, empty for standalone raw
programs. `contract!` supplies exactly the function's parsed calldata parameter
names, before parameter expansion discards their source locations.

The preprocessing state retains ordinary alias origins separately from virtual
slice descriptors. An ordinary declaration is accepted only when its initializer
is a stable name/member/index place rooted in a known origin. Index expressions
must be pure; calls, effects and conditional references stay refused. The new
alias retains that origin, so aliases of aliases stay read only. Shadowing clears
origins, and nested lexical scopes restore both origin and descriptor lists.
Writes through an ordinary alias are refused in statements and nested
expressions. Ordinary calldata pointers may be rebound to another admitted stable calldata
place; memory origins cannot be introduced by a bare or nested assignment. An already captured
slice retains its original base. Virtual slice descriptors still cannot be
rebound. The later `calldataCheck` continues checking copies, return
bindings and calls to memory parameters; its empty-root shortcut is unchanged.

Struct and fixed-array aliases of actual calldata parameters keep their typed
memory-alias representation and existing read behavior. This change introduces
no core statement, no external dependency and no new proof assumption. The
additional origin list belongs only to bounded frontend preprocessing; it does
not claim a new source/native simulation theorem.

Explicit slice descriptors retain their existing native model interpretation:
interpreter examples may provide a memory-backed array to a read-only slice.
Memory materialization of a slice still allocates an independent primitive array;
copy barriers and slice bounds/evaluation order are unchanged. This patch does
not broaden the accepted Solidity source origin of an explicit slice.

## Review and validation

Worker handoff (historical): **patch_ready_unvalidated**. Prepared outside the shared checkout; no
Lean server, build or repository mutation was performed. Per-file diagnostics
and final source/library gates belong to the integrating coordinator.

The `SliceCopies` example retains all existing successful copy/hash/storage and
invalid-bounds executions. Its successful struct/fixed-array alias execution now
uses transitive aliases. New negative checks cover standalone memory-array and
memory-struct bindings masquerading as calldata, an invalid memory-parameter
function called through the normal elaborator, transitive writes through array,
struct and fixed-array aliases, lexical scope exit, and effectful ordinary alias
initializers. Existing memory-backed explicit-slice and independent-copy checks
remain unchanged.

After applying, diagnose Context first, then Contract and SliceCopies; build the
changed frontend/example and run the calldata/slice/aggregate source regressions.
Review the source/native boundary separately from proof verdicts. This is a
restricted origin fix: valid effectful/conditional ordinary alias initializers
remain an explicit elaboration limit.

Readonly write-target detection follows assignment results and both branches of
reference conditionals. Neither can hide a write through a calldata origin.
Memory-return alias pruning leaves the recursive memory-argument and nested
assignment checks conservative; identity/forwarding controls stay refused.
