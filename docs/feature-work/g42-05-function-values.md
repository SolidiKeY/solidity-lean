# G42.05 external function values

Partial: value operations are certified; external-function call execution is open.

`Backend/FunctionValues/Interface.lean` retains the actual Source external-function
parameter list, return list and mutability. `Representation.lean` reuses the
published `Yul.Views.externalFnCodec`: address followed by four selector bytes.
The backend word uses the low 192 bits. Encoding is injective, decoding recovers
the source value, and nonzero high bits are rejected. This convention is not a
claim about ABI alignment, Source.Val.word, or physical solc storage packing.

`Execution.lean` proves actual Evm.run construction (pushing an encoded value),
SHR address projection, MOD selector projection, equality, and memory/whole-word
storage round trips for every indexed external-function value. Source.cmpVal
agrees with the equality observation through its actual numeric key. The exact
machine updates retain all other fields; packed neighbouring fields require the
existing packing/layout agreement. These are value operations, not a theorem
about evaluating component expressions or refining Source heap/storage writes.

`Inequality.lean` additionally proves actual EQ/ISZERO inequality against
Source.cmpVal.ne, with inhabited true/false controls. No ordering is claimed.

`Controls.lean` inhabits a view-qualified signature with a memory-array argument
and two returns. It checks source and compiled equality/inequality, changed
address/selector identity, successful memory/storage runs, codec round trip,
malformed selector length, high-bit refusal and an actual empty-stack EVM fault.
The latter is not a Source revert or external-call failure theorem.

`Premises.lean` binds one actual declared InvocationFrame to the same receiver,
full signature, mutability and selector prefix. Its DeclaredCallBoundary takes
unchanged WorldCalls.Premises/FetchedPremises. This is a conditional interface,
not a producer or coverage theorem: a reached Fetched run is still required.
Arbitrary external function values need not admit this declared binding.

## Remaining producers

- G42.02, readonly-external: actual recipient execution and returndata, including
  STATICCALL adequacy. The current Evm.Instr has CALL but no STATICCALL; CALL is
  not used as a substitute for static execution.
- G42.04, v13-abi-world: library call execution/binding.
- G40, parallel-20261103/abi-entry: entry decoding and exact decoder failures.
- Dynamic external-function application lowering: the current Source RExpr has
  declared extCall, but no dynamic external-function application constructor.
  No new source semantics or source admission is supplied here.

Consequently all-profile function-value calls, exact external-call failures and
static restrictions are not yet certified by these modules. No coverage is
inferred from the existence of a conditional WorldCalls premise structure.

## Validation and review

The six modules build with Lean 4.24.0, one Lean thread and explicit -j1 under
the managed VM guard. Universal proofs accompany the inhabited observations;
no new axiom, sorry, trust shortcut or increased proof budget is used. Read-only
finder and skeptic reviews found no semantic defect. Positive memory/storage
controls were added following the finder coverage observation. Detailed terminal
logs, resource measurements, failed attempts and checksums accompany the worker
handoff; the original full gate remains dependent on VA1's H6 TypeExamples split.

The per-theorem axiom audit reports only `propext`, `Quot.sound` and, for
Evm.run theorems, `Classical.choice`; several observations are axiom-free. These
are whole-operation measurements, not per-proof timing claims. Registration,
layering, trust and whitespace checks passed. Full cumulative build/TestSuite
gates are not claimed by this partial checkpoint.

The inequality extension received separate read-only finder and skeptic review;
both found no defect. The earlier five-module measurements above remain the
original checkpoint measurements; final six-module logs are in the handoff.
