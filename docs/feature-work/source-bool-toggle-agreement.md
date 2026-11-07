# Computed boolean read-modify-write agreement

`BoolSlotToggle` assigns the negation of the old selected local back to that
same arbitrary-prefix slot. It reuses the newly exposed actual unary evaluation
law `bool_not_eval_source`; the existing negation initializer consumes that same
law without changing its theorem or semantics. The assignment RHS is evaluated
before the write, and the expression returns the new negated value, together
with the exact updated locals and unchanged Source nonlocal state.

The normal-step producer derives the read and write value from the same actual
related initial environments. The importing client derives its initial locals
and positive Source run internally; no operand, desired outcome or reached-state
premise is added. The model likewise reads its old environment before updating
the slot. Old surrounding locals and each interpreter's nonlocal fields remain.
Horizon three is Source timeout; the statement's positive horizon is four.

Concrete false/true expression runs bind the returned new value to the write.
Two actual head-local statements on each interpreter read the intervening update
and restore their original local head and nonlocal state. This is ordinary
local-write restoration, not source rollback/transaction finalization or a
cross-model world correspondence. A raw old-result control rejects returning
the old false value after the actual false-to-true update.

Scope remains explicit resolved normal primitive-local pairs. H16 Source and
Core ExtCall are unchanged. Generic state/error simulation, source/compiler
selection, installed input, heap/storage/liveness/nu-before-rho/call/ABI/catch/
rollback/modal/native and original Revert full gates remain open. Full gates
are deferred under H12. The initial state-record equality failure and draft are
preserved; a bounded rfl/record-case step fixes it without weakening restoration.

Final focused evidence: four complete-clean diagnostics including affected
negation clients, four per-file passes, 63-job importing closure with cached
dependencies, fourteen actual reports (thirteen standard-only, one axiom-free)
and six static EXIT0 checks. Exact master/parent/working fragment views are
clean with full commit/checker/diff bindings; five existing public negation
signatures remain unchanged. The new API exposes an already-proved inner run.

Independent read-only finder and skeptic inspected source, doc and actual raw
MCP/build/audit/static/comparison records without Lean/check replay; no findings.
Neither independently rehashed all protected bytes or provenance/signature
identities. The verifier retained 1,351 records, eight configs and 182 archive
members. The initial failed restoration draft and real EXIT1 remain retained;
the successful record-equality step preserves the full original statement.
Managed-runtime and local-daemon health checks were read-only and made no
configuration changes. Cached checks and metadata timing are not cold/full-lane
or original source/native completion evidence.
