# Conditional normal-local Source/model composition

This SS-AGREE increment proves the existing `NormalLocalsObligation` for
sequences from explicit single-statement correspondence facts. It uses the
existing Source and model evaluators, without changing H16 Source files,
Core ExtCall, semantics, admission, profiles, resources, or expectations.

## Premises and producer ownership

`NormalStmtObligation` (module `NormalStep`, namespace
`Solidity.Source.Agreement`) is a typed
proposition about a specific `RStmt` / `Solidity.Stmt` pair. For each related
initial primitive-local environment, a real normal `execS` result must have a
corresponding actual `Stmt.runC` result and related final locals. The Source
initial state and returned journal remain explicit. It is a theorem argument,
not an axiom, opaque constant, default instance or selected execution.

| Consumer | Explicit producer facts | Discharge |
|---|---|---|
| `normal_cons` | `step : NormalStmtObligation ... s S`; already-built `tail : NormalLocalsObligation ... rest P` | This SS-AGREE lane must prove each associated statement fact; the tail is derived recursively from the same consumer and `normal_nil`. VY5 owns finalized H16/H25 Source operation/resource APIs needed by broader producers. |
| `normal_two` | Two `NormalStmtObligation` arguments for its two specific statement pairs | Same per-statement producer obligation; no whole-program execution or result premise. |
| `normal_nil` | None | Proved from existing evaluators here. |
| `two_skips_agree` / `two_skips_client` | No missing producer | Both step facts are supplied by proved `skip_step`; actual Source execution and initial locals relation are constructed. |

These are normal-only local-state contracts. They deliberately do not supply
joint heap/storage/world correspondence. The locals-only initial relation may
be insufficient to inhabit a fact for a stateful statement; this is an explicit
scope limit, not a promised producer or a supported-fragment default. Source
and model statement association is separate and must not be inferred from a
proof parameter or constructor shape. There is no generic compiler selection
or whole Source interpretation here.

## Actual composition

`NormalCuts.source_cons_cut` derives the intermediate Source locals and state
from the actual checked equality of the existing `execItems` run. The head
and tail run at the actual residual horizon `n`; the complete intermediate
and final journal pairs are preserved. Error, break, continue and return arms
cannot be mistaken for a normal result. `Out.up` restoration is handled using
its real expression, not a supplied normal-tail hypothesis.

`NormalComposition.normal_cons` consumes those derived states. Its model
successor is the actual `Stmt.runC` output; the tail runs on that same state,
and the returned heap prefix is the composition of its two real prefix proofs.
It proves the existing `Prog.runC (.cons S P)` equation. No chosen final state,
whole-program result, source journal or successful check is a public producer
premise. Horizon-zero Source execution remains timeout; the theorem only
responds to the existing obligation's explicit normal-result antecedent.

## Nonvacuity and limits

`NormalControls.skip_step` supplies a concrete producer for Source `skip` and
model empty block. The two-step importing client has an actual Source run,
related initial locals from the existing total value producer, and an actual
model result. The pair is an auxiliary no-op control, not a compiled source
fixture or a default association. Separate controls retain Source timeout and
early return. `skip_revert_refused` uses a genuine Source normal run and total
locals to refute the incompatible Source-skip/model-revert producer.

No full-state, error/panic/revert correspondence, termination completeness,
unchecked-block or loop/body simulation, native/physical EVM adequacy, source
installation or original Revert closure follows. The producer hypotheses stay
visible until proved for real associated statements. This increment makes
independent normal-sequence progress while VY5's finalized H16/H25 APIs remain
pending; it neither edits them nor waits for their full branch.

Validation records distinguish fresh owning-file diagnostics and kernel/axiom
checks from cached dependencies. Failed bind-reduction and control-parameter
attempts are retained, including the scratch multiline formatting failure.
Full original lane/source/native gates remain open; no new cold-build result
is claimed from this conditional component.

## This checkpoint's evidence

Four new owning files have complete, clean unfiltered MCP responses and four
separate toolkit per-file kernel passes. Twelve actual public axiom reports
use only `propext`, `Classical.choice`, and `Quot.sound`, including their
private proof dependencies. The focused 54-job leaf build passes; fetched and
cached dependencies are not a cold build. The four new import closures reach
no frontend, Bridge or Mathlib. Layer, generated registration, module-map and
diff checks pass. The root generator also registered 17 modules already
committed on the required parent; their source was not edited here.

Global trust remains **EXIT1**: two `implemented_by` inventory drifts in
`Frontend/QualifiedUnits/References.lean`. An actual exact-parent Git-blob
scan using the unchanged checker also exits1 with the identical two findings;
there are zero new findings. This is not a passed trust gate or a historical
worktree shell run. The inventory and unrelated producer source are untouched.
Full original lane/source/native gates were not replayed or claimed passed.
Read-only finder/skeptic reviews covered actual new source and raw focused
evidence without replaying checks; no remaining source findings were reported.

Existing primitive default-declaration producers and their actual importing
client now discharge a nontrivial family of step hypotheses; see
[source-normal-defaults.md](source-normal-defaults.md). This does not supply
generic statement association, stateful/full-state or error agreement.
