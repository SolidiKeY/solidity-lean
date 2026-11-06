# Existing primitive default-declaration agreement

This increment discharges the earlier `NormalStmtObligation` hypothesis for
existing uninitialized primitive declarations, rather than introducing a
source/default/profile interpretation. Source `RStmt.declVar (sourceTy p)` is
paired explicitly with model `Stmt.declLocal p name none`, for exactly the
already supported `PrimTy` cases: bool, uint256 and int256. H16 Source, Core
ExtCall, compiler producers, semantics, expectations and budgets are unchanged.

`primitive_default` derives equality of the existing Source `Val.default` and
model `PrimTy.dflt`, preserving intrinsic range evidence. `default_source`
derives actual `execS` at horizon n+2, including its complete unchanged Source
state and incoming local tail. `default_model` derives the real `Stmt.runC`
result: the actual model state pushed with its existing default value. Thus
only its local environment changes; no other world/heap/storage/frame field
is replaced or supplied independently.

`default_step` proves the precise prior per-statement contract without any
producer, range, desired result or successful-run premise. Both residual
horizon0 and horizon1 cannot produce a normal declaration. `two_defaults_agree`
instantiates both hypotheses of `normal_two`, including its intermediate
primitive context. It supplies a real normal-result theorem for the two
explicit declaration terms, not a generic program-association certificate.

`two_defaults_client` imports those proofs using the existing total related
locals producer. Its headline derives both actual evaluator results and their
ordered final locals, without a supplied step fact, run or relation. The
second default is innermost, then the first, then the original tail. Arbitrary
existing model/Source initial states and either Source pipeline remain explicit;
this does not equate their worlds with one another.

Controls retain single-declaration horizon1 and two-declaration horizon3
Source timeout versus the sufficient n+4 two-declaration run. These Source
horizons are neither gas nor model divergence. A wrong boolean declaration
producer (false Source default versus true model initializer) is refuted using
an actual positive Source run and total initial relation. Binder-label
independence is proved against the existing model operation, not assumed to
establish source identifier resolution or provenance.

No initializer-expression, assignment, stateful/reference/array declaration,
error/full-state simulation, compiler association, source admission, installed
input, fetched EVM/gas/native or original Revert correctness follows. Those
remaining facts and the broader H16/H25 producer obligations remain open.
The supported defaults are existing definitions, not a changed default model.

## Focused evidence

Two new owning files have complete, clean unfiltered MCP diagnostics. Three
per-file kernel checks pass (including the existing composition consumer),
and fourteen actual new/affected public axiom reports contain only the allowed
standard axioms. The focused 55-job leaf closure includes fetched/cached
inputs and fresh owning-file elaboration; it is not a cold full build.
Trust, layer, registration, module-map and diff checks exit0 on the current
parent; the old checkpoint's trust EXIT1 evidence remains preserved and was
not repaired by this increment. Both read-only finder/skeptic reviews inspected
actual source and raw focused records without running Lean or replaying checks.
Full original lane/source/native gates remain open and were not rerun here.
