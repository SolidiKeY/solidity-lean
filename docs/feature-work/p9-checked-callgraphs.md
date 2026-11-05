# P9: checked finite call graphs

Modules: `Solidity/Lowering/P9/`. `ElaboratedCalls` and `CallControls` hold
scoped call admission derived from actual Source elaboration. The rest is a
whole-program checker that derives `Source.CallsOK`.

## Checker

`WholeProgram.check` takes a resolution, the actual `Glob`, a contract `c`
and a finite list of allowed declarations. It checks:
- environment/unit declaration coherence and allowed membership;
- that the selected body is present, with the right return signature;
- empty modifiers and available return defaults;
- `ValFragC` closure over the same list.

Its decisions prove the predicates the source interpreter already uses, so no
approximate fragment is introduced. `FragmentDecidable` gives the `Decidable`
instances for the fragment predicates. `DeclarationIdentity` derives
`DecidableEq` for intrinsic syntax and declarations (global instances; none
existed before) without changing the representation.

- `WholeProgram.check_sound` derives `Source.CallsOK` instead of taking it as
  a premise.
- `WholeProgram.from_elaborate` recovers the exact resolution and dependent
  program identity from a successful elaboration.
- `WholeProgram.call_ns` and `expr_ns` expose the existing progress consumers.
- `WholeProgram.functions` lists every function declaration of the actual unit.
  With it, `checkFunctions` and `functions_from_elaborate` check the complete
  function catalogue, so consumers need no hand-chosen allowlist.

These are conditional admission and progress results for the existing value
fragment. They do not prove that every elaborated program satisfies `CallsOK`.
Recursion needs closed calls, not acyclicity. `NS` excludes only stuck
outcomes: returns, reverts and timeouts remain. Modifiers, unsupported
expressions and memory operations, and unavailable return defaults are still
refused. No `SourceSpec`, compiler-lowering, ABI/EVM or termination result
follows. Admission is relative to the supplied dispatch contract, not to every
contract at once. `checkFunctions` checks the body that dispatch from the
contract selects for every function of the unit, so a function whose selected
implementation has no body (an interface function, or an abstract function
with no implementation along that contract's hierarchy, including one in an
unrelated contract) refuses the whole unit. An abstract base declaration is accepted when dispatch selects a concrete
derived implementation; `AbstractOverrideControls` supplies a positive control.

## Controls

- `ProgramControls` derives a certificate for a nonempty elaborated allowlist
  through `from_elaborate` and feeds it to source progress. The checker refuses
  an abstract declaration with no body and an incoherent environment.
- `AdmissionControls` admits the `ElaboratedCalls` fixture. A Boolean body
  with an integer return type is refused earlier, by the elaborator
  (`wrong_return_type_rejected`).
- `RecursiveControls` admits an elaborated self-call graph, proves
  non-stuckness at every horizon and keeps the exact horizon-12 timeout.
- `GraphControls` admits two inferred functions and runs entry through leaf
  to `true` at horizon 12, preserving the caller local and the source state.
  Omitting the leaf is refused.
- `ReturnControls` checks the selected-return guard. It uses two declarations
  with the same parameters and different returns, an invalid overload that the
  source elaborator still accepts (recorded in
  [solc-alignment.md](../solc-alignment.md)). Both the local and whole-program checks
  refuse it. This is a negative control, not a new override policy.
- `OverrideControls` elaborates a virtual Boolean function in Base and its
  override in Derived. The complete catalogue is admitted for Derived,
  dispatch of the base declaration selects the distinct derived declaration,
  and the call returns true rather than the base body's false. The resolution
  uses the legacy pipeline; execution is observed in both pipelines. The base
  is virtual with a body, not abstract, and the call node is built directly
  on the base declaration rather than elaborated from a call site. This is
  Source elaboration and execution, not a WellFormed/static-checker result.
- `AbstractOverrideControls` (in `OverrideControls.lean`) has a bodyless virtual
  base function and a concrete override. Actual elaboration and complete-catalogue
  admission select the derived body. The base body is proved absent, dispatch
  differs from the called declaration, and the call returns true in both
  evaluator pipelines. Resolution is legacy and the intrinsic call is built
  directly, as in the concrete-base control.
- `CatalogControls` runs `checkFunctions` on the complete catalogues of the
  two-function and recursive programs.

All printed axioms are `propext`, `Classical.choice` and `Quot.sound`.
