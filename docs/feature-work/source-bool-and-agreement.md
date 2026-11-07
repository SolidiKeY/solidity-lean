# Short-circuit conjunction initialization agreement

`BoolSlotAnd` derives the actual left operand from corresponding arbitrary-
prefix local environments and follows the existing Source boolean-key test
and model short-circuit operation. The right operand is a boolean literal.
The operational Source helper exposes the actual lookup; the normal producer
and concrete client derive it internally. Their final new local is the actual
conjunction result, with original locals and nonlocal state retained.

Source-only controls put an assignment on the right. A false left operand
suppresses that write; a true left operand executes it. At horizon three the
skipped arm can still return normally while selecting the same arm times out
before its write. The ordinary left-read literal pair times out at horizon two.
Actual model conjunction/disjunction runs on false/true distinguish operators.
These are constructed evaluator controls, not source/compiler/native fixtures
or model correspondence for effectful right-hand expressions.

The agreement remains normal primitive locals for explicit resolved pairs.
No generic Source state/error simulation, parsing/elaboration/compiler selection,
installed input or original source/native adequacy follows. H16 Source and
Core ExtCall remain unchanged. Original Revert heap/storage/liveness/nu-before-
rho/call/ABI/catch/rollback/modal/native and full-assignment gates remain open.
Full gates are deferred under H12; actual focused evidence and independent
read-only reviews accompany the checkpoint. No old resource failure is retried.

Focused validation: two complete-clean owning diagnostics, three per-file
passes, 62-job importing leaf with cached dependencies, eleven standard-only
public axiom reports and six static checks at EXIT0. Exact master/parent/
working fragment comparisons are clean with full commit/checker/diff bindings.
The metadata comparison completed but its precise wall time was not separately
instrumented; it is not Lean or cold-build timing. A read-only status probe
returned EXIT2 while the comparison file was absent; capped output remains in
the tool transcript, without a standalone raw log. No proof attempt failed.

Independent read-only finder and skeptic reviewed source, doc and actual raw
MCP/build/audit/static/comparison records without Lean/check replay; no findings.
Neither independently rehashed all protected bytes or comparison hashes. The
verifier retained 1,325 records, eight configs and 182 archive members. Two
intervening master-merge commits were authenticated and preserved before work;
no checkout reset or original-goal replacement occurred. Original full-source,
fixture and native obligations are not discharged by these optional producers.
