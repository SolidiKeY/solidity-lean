# Declaration certificates and exact counterstates

The exact proof-or-counterstate backend of `#verify` and `sol_exact`, ported
from mini-solkey's declaration certificates, no-information-loss
reductions and countermodel reconstruction.  On a recognized leaf the
result is an equivalence with the original formula; the arithmetic
decision returns either verdict, and both are kernel-checked.  Unsupported
constructs and resource limits fall back to the ordinary strategy and the
heuristic search.  It is not completeness for Solidity or for reachable
states.  The pipeline these stages form, its completeness theorem and the
decision built on it are `docs/automation.md` (M4, M7); `docs/module-map.md`
has a line per module.

## Invariants every stage keeps

* **Both polarities.**  `Fml.toLS` is directional (positive reduction
  suffices to prove, negative follows from the formula; a pending modality
  can become `false` positively), so neither it nor
  `Seq.checkCore = some false` is a refutation.  Exact stages compute both
  directions and accept only structurally equal complete leaves
  (`ExactReduction.holds_iff`, `Calculus/ExactReduction.lean`).
* **Failures are kept.**  A failed read, key or checked operation stays
  failed: guards are true exactly where a path returns, two failed keys do
  not alias, a branch whose condition fails selects neither branch (the box
  accepts that revert, the diamond rejects it), `assert` false is a panic
  under either modality, and exhaustion is never reclassified as ordinary
  failure.  KeY's `=` is reflexive, so two sides that halt alike are equal
  (`Tm.agreeB`, `LFml.optEq`).
* **No sampling.**  Universal binders are covered by every typed instance
  (`argument_cons`, `Parameters.observe_realize`); mapping keys are never
  enumerated: a dependent read follows only the selected continuation
  (`Query.run_realize`).
* **Actual states.**  A counterstate is built by the interpreter's own
  successful saves (`Assignment.realizable_iff`: aliased references must
  agree), at context `[]`, its failing arguments recorded separately.
  Compiled evaluation is never accepted as proof: positive replay checks
  the arithmetic computation, negative replay the finite assignment, and
  the closed original-formula proof term is kernel-checked before a verdict
  is accepted.
* **Bounded recognition.**  Recognizers have depth budgets (paths and
  closed expressions 1024, updates 2048, prefixes 1024); normalization
  shares one node budget across branches and their duplicated
  continuations; exhaustion returns unsupported, never a verdict.

## The stages

* **Declaration facts** (`Calculus/DeclarationFacts.lean`,
  `Calculus/DeclarationReduction.lean`): the ranges `SurfaceSpec.lean`
  generates (scalar roots, fields, mapping entries under any primitive key)
  proved by `sol_decl_facts` from intrinsic typing and total declaration
  paths (`Path.Declared`: fields and keys, no array index).  This proves
  ranges for every typed storage, not canonicity or `wt(storage)`.
  `declaration_reduce[φ]` replaces certified facts by `true` (also under
  hidden `Fml.bind` binders) by an equivalence; user requirements stay.
  `Tools/Counterexample.lean` uses the facts to certify a candidate whose
  three-valued evaluation is inconclusive.
* **Read realization and queries** (`Calculus/ReadRealization.lean`,
  `Calculus/ReadQuery.lean`, `Calculus/QueryReduction.lean`,
  `Calculus/ReadTrace.lean`, `Calculus/QueryReadBounds.lean`,
  `Calculus/TraceReduction.lean`): dependent reads (`balances[balances[3]]`)
  as queries over occurrence streams, alias consistency necessary and
  sufficient for a storage representative (`replay_realizable_iff`), finite
  syntax-derived bounds.  A compiled query may read an unused pure operand.
* **Arithmetic from certificates** (`Calculus/QueryArithmetic.lean`,
  `Tools/QueryArithmetic.lean`): `Query.Arithmetic` with a fixed occurrence
  layout (`Query.HasLayout`: not for queries whose branches change the
  sequence); `query_countermodel[certificate]`.
* **Symbolic path aliases** (`Calculus/SymbolicPaths.lean`,
  `Calculus/AliasConstraints.lean`): the closer's `relSegs` comparison as
  Boolean alias formulas (`SPath.alias_holds`, under `TestsOk`); `n`
  occurrences give `n²` pair conditions.
* **Automatic dependent reads** (`Calculus/PathGuards.lean`,
  `Calculus/FlattenReads.lean`, `Calculus/OccurrenceLayout.lean`,
  `Calculus/ReadFlattening.lean`, `Calculus/ActiveReadConstraints.lean`,
  `Calculus/LeafArithmetic.lean`, `Calculus/DependentReduction.lean`):
  primitive observations replaced by fresh guarded atoms in dependency
  order, alias constraints only between paths that both return, the pair
  count checked before the matrix is built; `FlattenedArithmetic.valid_iff`,
  `DependentReduction.valid_iff`.
* **Linear decision** (`Calculus/LinearDecision.lean`, mini-solkey
  Chapter 19; `Calculus/LinearCountermodel.lean`): Boolean combinations of
  linear (in)equations over naturals by binary derivatives;
  `AFml.decide_iff` total, `AFml.exploration_isSome` (the computed graph
  bound suffices), `AFml.verify` a proof or a counterassignment from one
  traversal.  It enumerates bit combinations of the formula's width, not
  values, but the graph can be exponential: keep explicit resource bounds
  when a tactic calls it (the walk is `docs/automation.md`, M7 "Running
  time").  `linear!{ … }` (`Calculus/LinearSyntax.lean`) is notation only.
* **Typed codes** (`Calculus/ScalarCode.lean`, `Calculus/TypedLinear.lean`,
  `Calculus/ReadLayout.lean`): `bool` as `0`/`1`, `uint` as itself, `int`
  shifted by `2^255`; `decode?` rejects out-of-range codes.
* **Source compilers** (`Calculus/StaticLinear.lean`,
  `Calculus/CheckedScalar.lean`, `Calculus/CheckedBool.lean`,
  `Calculus/CheckedLinear.lean`): static reads and literals, checked
  affine arithmetic with its success guard (`CheckedScalar.Correct`),
  comparisons with offsets removed, Booleans as separate successful-true and
  successful-false predicates (short-circuit order kept; `!` cannot turn
  failure into true).  Every operand must be recognized even where a short
  circuit would skip it.  Closed-constant recognition is retried at
  expression nodes (profile before optimizing).
* **Updates** (`Calculus/ExactUpdates.lean`): push-free updates with no
  memory local in their output context, both directions
  (`updateGuard_iff`, `ExactAt.update`), composed under connectives and
  typed binders by `sourceReduction?`.
* **Parameters and inputs** (`Calculus/ParameterLayout.lean`,
  `Calculus/ParameterReduction.lean`, `Calculus/InputLayout.lean`,
  `Calculus/InputReduction.lean`): the typed universal prefix and the
  observed transaction fields (`msg.sender`, `msg.value`,
  `block.timestamp`, `address(this)`, its balance; their model domains, no
  160-bit or reachability constraint) placed before storage; a key keeps
  its type and position.
* **Programs and calls** (`Calculus/ExactRun.lean`,
  `Calculus/ProgramReduction.lean`, `Calculus/SoundCalls.lean`):
  `ProgramNormalization.ofFormula?` normalizes local and storage
  assignment, deletion, primitive declarations, blocks, branches,
  `require`/`assert`/`revert` and void, scalar and tuple-of-primitive calls
  exactly (`Upd.afterT_run_iff` adds the ending run the ordinary agreement
  lacks).  `ParameterReduction.withLayout` exposes computed layouts by
  checked equalities instead of unfolding a deep recognizer.

## The public tools

`declaration_read_reduce`, `declaration_static_reduce`,
`declaration_checked_reduce`, `declaration_parameter_reduce`,
`declaration_input_reduce`, `declaration_trace_reduce` and
`declaration_dependent_reduce` (`[φ]`) compose declaration normalization
with each stage.  `sol_exact` (`Tools/CompleteVerification.lean`; replay
twin `sol_exact?`) and `#verify` try the static-input route, then the
dependent route.  The dependent route first runs an early search of at most
512 graph rounds for a negative witness (not a node cap: a frontier can
still grow exponentially), then the complete decision; exhaustion never
means validity.  `#verify` restores its Meta state on unsupported input and
falls back to `sol_spec_try` and heuristic refutation; a certified
negative survives a failed rendering as a minimal report (initial storage,
transaction, parameter atoms).  Pins: `Examples/CompleteVerification.lean`,
`Examples/DependentReduction.lean`, `Examples/InputReduction.lean`,
`Examples/ProofTree.lean` (`sol_exact?`).

## Limits

Outside this backend's own fragment: loops, compound assignment,
reference-result calls, memory locals, push-bearing updates (exhaustion)
and memory statements in programs (`ExactStatement.ofStatement?`);
numeric `orElse`/`kite` the arithmetic recognizer rejects; nonlinear
arithmetic; reachable-state reconstruction; general calculus completeness.
The later pipelines of `docs/automation.md` (M4's lift, M7's features)
extend the decided fragment past these stages: interior quantifiers,
arrays, the ledger and fresh memory are theirs, and their open items are
M7's "What is not proved".
