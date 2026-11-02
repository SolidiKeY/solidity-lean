# Checked elaborated call-program progress (S05)

`Solidity/Source/Progress/CheckedPrograms.lean` connects three inputs to the
existing source progress theorem:
- a successful `Source.elaborate`;
- `Glob.prog = Source.progOf res.env`;
- P9's check of the complete function catalogue
  ([p9-checked-callgraphs.md](p9-checked-callgraphs.md)).

`CallsOK` and recursive memory preservation are derived, not premises. The
result holds for the supplied dispatch contract only, and it admits a fragment
conditionally rather than covering all of Solidity.

- `checked_fragments` returns the all-horizon progress record and the joint
  memory record ([source-preservation-allocations.md](source-preservation-allocations.md)).
- `checked_expr` gives non-stuckness, `MemOK` and current-local preservation,
  and validity of result references.
- `checked_call` covers internal calls with valid input references.
- `checked_items` keeps the original `BodyFrame`, fragment and operation-domain
  conditions and returns valid output locals.

Timeout and revert semantics, allocation inputs and named refusals are
unchanged.

`Progress/Controls.lean` uses an actual elaborated contract, its nonempty
complete catalogue and a nonempty heap. It reuses an existing source execution
and keeps the wrong-result rejection and the timeout. An elaborated abstract
declaration fails admission because it has no body. A dangling reference
refutes the memory precondition. That is a premise failure, not a new runtime
check.

Not covered: allocating expressions inside the fragment, compilation,
world/ABI entry points, callbacks, payments, termination, `SourceSpec` and EVM
refinement. All printed axioms are `propext`, `Classical.choice` and
`Quot.sound`.
