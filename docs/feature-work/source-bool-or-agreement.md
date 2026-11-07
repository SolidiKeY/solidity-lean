# Short-circuit disjunction initialization agreement

`BoolSlotOr` derives the actual left operand from corresponding arbitrary-
prefix locals and follows existing Source boolean-key and model short-circuit
semantics. The right operand is a literal. Its operational helper exposes the
actual lookup; the normal producer and concrete client derive that lookup and
the actual Source run internally. The pushed result is the old left value OR
the literal; original locals and nonlocal fields are retained for this pair.

Source-only assignment controls reverse the conjunction controls: true skips
the right-hand write and false executes it. At horizon three, the skipped arm
still returns normally while selecting the same assignment times out before
writing. The ordinary left-read pair times out at horizon two. A real false OR
true Source trace and a refused false result distinguish disjunction from
conjunction. These are constructed evaluator controls, not native/parsed-source
fixtures or model correspondence for effectful right-hand expressions.

Scope remains normal primitive locals for explicit resolved expression and
statement pairs. Generic Source state/error simulation, elaboration/compiler
selection, installed input and original source/native adequacy remain open.
H16 Source and Core ExtCall are unchanged. Original Revert heap/storage/liveness/
nu-before-rho/call/ABI/catch/rollback/modal/native and full-assignment gates remain
open. Full gates are deferred under H12; focused raw evidence and independent
read-only source/evidence reviews accompany this checkpoint.

Focused validation: two complete-clean owning MCP responses, three per-file
passes, 62-job importing leaf with cached dependencies, eleven standard-only
public axiom reports and six static checks at EXIT0. Exact master/parent/
working fragment comparisons are clean with full commit/checker/diff bindings.
Independent metadata reads were batched through the toolkit Tree cache before
its unchanged generation logic; recorded metadata time is not Lean timing.

Independent read-only finder and skeptic inspected source, doc and actual raw
MCP/build/audit/static/comparison records without Lean or check replay; no
findings. Neither independently rehashed all protected bytes or provenance
hashes. The verifier retained 1,338 records, eight configs and 182 archive
members. No proof attempt failed this phase; older failed commands and resource
stops remain preserved. Cached confirmations and these bounded components do
not establish cold/full-lane timing or original source/native completion.
