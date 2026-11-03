# P8: G15 admission and S05 failure resources

Partial checkpoint. P8a (G15 admission, S05 `SourceSpec` and S03 failures) is
not complete: no `P8a.Producer`, operational reference, `SourceSpec` instance,
failure-aware source semantics or EVM adequacy result exists. The modules below
prove component stages and boundaries; each section lists what stays open.
The consumer side is in [P8b frozen consumer interface](p8b-frozen-interface.md).

## Frozen interface

`Lowering/P8/FrozenInterface.lean` (namespace `Solidity.Lowering.P8.P8a`)
declares the producer obligations; every proof field is unimplemented and no
value of any structure is exported.

- `Spec` is `Roadmap.SourceSpec` (an `abbrev`); `SourceProgram` is the actual
  environment-indexed `Source.SrcProg`.
- `OperationalReference` (resource type, `points` into G06
  `Evm.FailurePoints`, an `Executes` relation), `SourceOrigins` and
  `RootModel` (execution/observation roots, `featureAt`, a combination- and
  settings-aware `classify`) are external parameters, not chosen by the
  producer.
- `Extraction`/`Extractor`: exact root and feature lists and
  `classify … = true ↔ S.InProfile r`.
- `FailureProjection S`: `points`, `ofPoints`, `points_ofPoints` and the
  request/frame consequences of `S.NoFail`.
- `SourceRealization`: exact agreement with `reference.Executes` and with
  `origins.meaning`, and preservation of the resource's failure points.
- `Producer S reference origins roots`: the above plus `CheckedFrontend`,
  `Admission`, `frontend_agrees`, `Unambiguous`, `Approved`, `AllPipelines`
  and `NonVacuous`.

### Failure projection conflict

Contract issue P8-SPEC-LAW1 (carrier direction decided by H16). `points_ofPoints` asks for a retraction of
`S.Failures` onto all of `Evm.FailurePoints`. `SourceSpec.failures_with`
(`Roadmap/Contracts.lean`) already makes `S.failures` a retraction of
`S.lang.Res` onto `S.Failures`. Composed, they give a resource-indexed
extract/replace pair for the whole failure plan, and
`Source.FailureResources.no_horizon_retraction` proves that no `Nat`-indexed
pair of that kind exists. So for any `S` whose resources have an encoding/decoding roundtrip through
`Nat`, `FailureProjection S`, and with it `Producer S …`, is uninhabited
(proved: `ResourceContractLaw1.nat_encodable_resource_impossible`). That covers
the current `Nat`-only Source resource. The same argument suggests countable
inhabited failures (such as the toy `toySource`, `Failures := Bool`) also
suffice; no theorem states that case. `ProducerAssembly.AssemblyType` and `PendingGlue` would
then be inhabited only vacuously.

This is not a kernel inconsistency. A resource that carries the failure plan,
such as `FailureResources.Bound = Nat × FailurePoints`, can satisfy the law:
use `Failures = FailurePoints`, resource extraction `snd`, replacement
`(horizon, newPlan)`, and failure projection `points = ofPoints = id`. The module docstring's "Retraction
is already required by SourceSpec.failures_with" is inaccurate:
`points_ofPoints` is a second retraction. The frozen file is unchanged; a
V2 explanation is in `Lowering/P8/FailureContractV2.lean`.

V2 separates `Projection` (points and NoFail consequences) from
`FullPlanCoverage` (a section onto every complete EVM failure plan).
`CompleteProjection` and V2 `Producer` require both. The `toV1`/`ofV1`
adapters and both roundtrip laws preserve every field, including the dependent
realization. V2 does not weaken coverage to realizable samples or finite
prefixes. `nat_encodable_resource_impossible` therefore still applies.
The corrected attribution is explicit: `failures_with` provides the first
retraction; `FullPlanCoverage` is the independent second retraction.

This is a lossless interface clarification, not a Nat-compatible semantic
repair. Neither V1 nor V2 can be inhabited over the current Nat resource.
Human decision H16 authorizes VY5, as single writer, to extend the source
semantic carrier to `FailureResources.Bound`.
This interface implements no extension: VY5's published carrier interface,
operational failure wiring, rollback/order and resource-consistency proofs
remain prerequisites for concrete realization. Generic consumers can retain V1
via `toV1`; concrete Nat consumers remain blocked. A source carrier extension
requires revalidating resource order, realization and all resource-based
semantics.

Open: VY5's published H16 carrier interface and operational realization; any inhabitant; adequacy of the reference, origins and
root parameters against the actual source machine.

## Admission, profile and root observations

- `Frontend/Admission/Profile.lean`: `ScopeScan.certify_features` keeps the
  whole ordered feature list, even after a diagnostic. `certify_iff` and
  `certify_rejected_iff` classify exactly the supplied uses by the existing
  model/abstract policy. `append_features` and `append_iff` keep both root
  groups and their failures.
- `Frontend/Admission/RootObservations.lean`: `observations`,
  `stmtObservations` and `itemsObservations` walk every `RExpr`, `RArgs`,
  `RConvArgs`, `RLVal`, `RStmt` and `RItems` constructor, keeping builtin and
  member names and call declarations. `root_observation_iff` and
  `accepted_roots` cover every supplied root. `ObservationSite.allowed_iff`
  requires an admitted S01 status naming a real feature with model or abstract
  scope.
- `Frontend/Admission/Controls.lean`: kernel controls for two roots, local
  shadowing, branch and loop-post sites, `block.number` and unknown-member
  refusal, a rejection that keeps later uses, the `NoFail` resource laws and a
  false root-list expectation.

Open: callee closure (local call admission does not certify a callee body);
extraction of types, all features and specification observations; coverage
against an independent source relation; solc-JSON importer agreement.

## Checked syntax

`Lowering/P8/CheckedSyntax.lean` validates raw input and parsing.

- `Parsed` carries all unit trees, the input settings and the main selection.
  `units_only_resolver_obstruction` shows that any actual parse and resolution
  of the existing units-only `FrontendSpec.ofParse` contradicts
  `SettingsRespected`; `units_only_settings_refuted` instantiates it.
- `checkUnit_sound`, `checkUnits_sound` and `check_sound` establish the
  existing grammar relation from byte, piece and layout certificates.
  `validate_accepted` and `produce_accepted` recheck every candidate of the
  existing lexer/parser; `settings_recorded` and `main_recorded` keep the tags.
- `settingsB_iff` and `rawB_iff` decide exactly `Settings.Ok` and `Input.Ok`.
  Raw admission needs both `rawB = true` and a checked parse.
- Controls: both pipelines accept `contract C {}`; wrong pipeline, main or
  bytes, a missing certificate, duplicate units, a nonpipeline order and a
  historical compiler are refused.

Open: parser completeness and uniqueness (`Checked.produceOpt_accepted` gives
soundness only); a complete multi-unit `FrontendSpec`.

## Schemas

- `Lowering/V07/Scalar.lean`: integer value transport (`integer_range`,
  `integer_observe`, `integer_related`, `integer_injective`).
  `Lowering/V07/DeclarationGraph.lean`: the `DeclarationGraph` relation between
  Source types and schemas (`identity_reflection`, `field_count`,
  `field_names`, `memory_layout`).
- `Lowering/P8/ScalarSchema.lean`, `Lowering/P8/ShapeSchema.lean` and
  `Lowering/P8/GraphSchema.lean`: `scalarStruct`, `shapeStruct` and
  `graphStruct` build a singleton `Schema` with its `DeclarationGraph` from an
  actual struct declaration's fields, checking nonempty and distinct fields
  and, for graphs, guardedness at the computed rank. No target certificate is
  an input.
- `Lowering/P8/FieldAdmission.lean`: `fields_lookup_none`,
  `fields_distinct_iff` and `graph_source_fields_distinct` carry lookup and
  distinctness through `GraphFieldsRel`; `duplicate_cannot_be_graph_fields`
  records a limit of current well-formedness, not a profile exclusion.
- Controls: dynamic recursive nodes and guarded fixed wrappers are accepted in
  memory and storage; inline and fixed-inline self recursion, wrong scope or
  identity, unresolved nodes, duplicate fields, zero-length and word-limit
  fixed arrays and memory mappings are refused. Arrays in `scalarStruct` and
  nodes in `encodeShape` are refused as still open.

Open: multi-node extraction, the remaining field shapes, general declarations,
value/heap execution and G01 lowering correctness.

## Program observations

`Frontend/Admission/ProgramObservations.lean` scans every expression-bearing
container of a `Source.Program`.

- `programObservations` covers every `E.decls` body (with modifier arguments)
  and constant initializer, and every contract's constructor body, state
  initializers and base-constructor arguments, in order and without unfolding
  calls. `program_observation_iff` equates it with the container relation
  `ProgramSite`; six `*_in_program` lemmas cover the containers;
  `accepted_program_iff` transfers admission.
- `target_body_covered` needs both `d ∈ E.decls` and a `P.body` lookup; it does
  not infer a callee from local call acceptance.
- `elaborated_constructor_in_declarations` uses `Elaborated.ctor_typed` to place
  each constructor body in the declaration scan.
- `programModifierTargets`/`modifier_target_iff` and
  `programBaseTargets`/`base_target_iff` list modifier declarations and
  written base names; base names are not resolved.
- Controls (`ProgramObservationControls.lean`): seven ordered sites across all
  containers; body-only, roster-omission and missing-body expectations are
  refuted. The invoking body belongs to a `.function` declaration and targets
  a `.modifier` with one `uint256` parameter. Declaration-derived parameter
  frames match the carried bodies; invocation parameter types match the
  modifier body. The carrier is not an `Elaborated` witness.

Open: proof that every executed dispatch, modifier, constant and construction
target is in these rosters.

## Dispatch coverage

`Lowering/P8/DispatchCoverage.lean` consumes P9's
`WholeProgram.dispatch_mem`.

- `dispatchMod_mem`: modifier dispatch selects a member of `E.decls`.
- `checkFunctionTarget`/`checkModifierTarget` with `function_target_sound` and
  `modifier_target_sound`: roster membership and a selected body.
- `check` tests every contract against every call site and modifier target.
  `internal_body_covered`, `external_body_covered` and `modifier_body_covered`
  derive a selected body whose observations are in the program scan.
- Controls (`DispatchCoverageControls.lean`): the published P9 elaborated
  function (`actual_target_checked`, `inherited_source_execution`), a recursive
  internal call, a genuine `.modifier` declaration with a timestamp body,
  refused missing function and modifier bodies with the caller kept, and
  refused foreign and abstract-interface targets.

Limits: `check` passes on an empty roster; the conclusions need actual contract
and site membership. Checking every contract can be stronger than
receiver-specific reachability; the external theorem concerns dispatch at the
given contract, not the external receiver. Modifier override selection is not
exercised.

Open: completeness (`InProfile` implies `check`); kind, parameter, return and
frame agreement; base-name resolution; receiver closure.

## Source resolutions

`Lowering/P8/SourceResolutions.lean` checks per-unit `Source.Resolves'`.

- `Packet` holds settings, main and one `Source.Resolution` per unit.
  `Resolves` requires equal tags and, per position, the original name and
  `Source.Resolves'`; `check_iff` decides it, `produce_resolves` and
  `produce_checked` construct it, and `unique` makes it unique per parsed
  input.
- `names_preserved`, `resolved_entry` and `checked_tags` keep names, judgments,
  settings and main.
- `order_agrees` (under `Settings.Ok`) and `coder_agrees` bridge the frontend
  and Roadmap pipeline and coder types: the pragma coder under legacy, v2 under
  viaIR.
- `checkInput` composes `rawB`, `CheckedSyntax.check` and `check`;
  `input_sound` gives all three stages and `checked_input_links` empty
  original links.
- Controls: both pipelines and a two-unit `A.sol`/`B.sol` input pass;
  corrupted pipeline or coder, wrong settings, main or name, missing, reordered
  or duplicated units, a missing parse certificate and nonempty links are
  refused.

Open: well-formedness of the produced environments; global imported-name
typing.

## Source metadata and obligations

`Lowering/P8/SourceMetadata.lean` composes existing component judgments.

- `UnitOK` is the existing `(WellFormed ∧ InProfileSyntax) ∧ StaticOK ∧
  InheritanceOK`; `unitCheck` runs `strictMetadataChecker` and
  `inheritanceChecker` (`strict_iff`, `unitCheck_iff`).
- `ComponentOK` adds `Settings.Ok`, main membership, `UnitsOK` at empty
  remappings and `UnitOK` for every unit; `metadata_iff` and
  `metadata_complete` are exact for this conjunction only.
- `parsed_units_preserved` ties the metadata roster to the checked parse;
  `input_sound` composes all four stages; `every_unit_checked` projects
  `UnitOK`.
- Controls: both pipelines and the two-unit input pass; a timestamp constant
  (well formed, refused by the stricter constant judgment), a missing import,
  duplicate names and an absent main are refused.
- `Lowering/P8/SourceMetadataObligations.lean`: `nontrivial_positive`,
  `strict_before_refusal` and `override_refused` check the unchanged
  `InheritanceExamples` fixtures. `checked_controls` supplies all three
  `PendingControls` fields: the valid override passes, the missing-virtual
  fixture passes strict metadata alone, and the combined check refuses it.

Open: any theorem that G00 `InProfile` implies this component check.

## All settings and producer assembly

- `Lowering/P8/SourceAllSettings.lean`: `metadata_settings` shows component
  metadata is unchanged between two admitted settings values; `input_settings`
  shows an accepted `SourceMetadata.checkInput` chain stays accepted under
  every admitted settings value, keeping bytes, trees, names, main and
  certificates and rebuilding the packet via `unique`. This is acceptance
  closure, not execution equality or `S.AllPipelines`.
- `Lowering/P8/ProducerAssembly.lean`: `component_pipeline_closure`
  specializes that result to every pipeline. `assemble` constructs a
  `Producer` from the unchanged eight-field `AdmissionHalf`, failure
  projection and dependent source realization; `checked_glue` packages
  these two conditional operations in `PendingGlue`.

These constructions supply neither an actual `AdmissionHalf` nor a concrete
source `Producer`. The actual source extraction, exact classification,
frontend agreement and nonvacuity obligations remain; VY5 supplies the
approved SourceSpec/reference/origins/failure/realization boundary under H16.
The component controls and conditional assembler use only the standard
`propext`, `Classical.choice` and `Quot.sound` axioms, pinned in their modules.

## Failure resources

- `Source/FailureResources.lean`: `Bound = Nat × FailurePoints`, ordered by
  horizon at fixed failure points (`Bound.le_refl`, `Bound.le_trans`,
  `Bound.failures_with`, `Bound.horizon_with`, `Bound.withFailures_mono`,
  `Bound.not_le_of_points_ne`). `noFail_iff` characterises `NoFail` as
  `noFailures balances`, keeping arbitrary post-fee balances;
  `dropped_not_noFail` and `frame_not_noFail` refuse failures.
  `no_horizon_retraction` (axiom-free) refutes every `Nat`-indexed
  extract/replace pair that is a right inverse on `FailurePoints`.
- `Lowering/P8/ResourceBoundary.lean`: `FailureResource` aliases `Bound`;
  `unmodified_forward_obstruction` shows the published Source language, whose
  `Forward` is `True`, cannot be packaged unchanged with a failure setter and
  the clear-frame consequence of `Forward`.

Open: thread request balances and frame failure schedules through source
execution with rollback, depth and stipend behaviour; extend resource
consistency; record hash and slot preimages; construct `SourceSpec`. The
evaluator still uses a `Nat` horizon and does not consult these points; a
constant or ignored schedule is not a solution.

## Open across P8a

Resolved execution roots (bodies, modifiers, constants, constructor and base
arguments, initializers) with recursive closure; complete feature extraction
and exact classification; solc-JSON importer agreement or routing the public
compiler through the checked frontend; the operational failure work above;
any `Producer` inhabitant.

## Provenance

The P8a modules and the P8b consumer interface are on master; their generator
scripts are not. Read-only finder and skeptic reviews found no Lean defect.
They found the failure-projection conflict above and the synthetic modifier
fixture. The fixture now uses a function host and
one-parameter modifier, with declaration/carried-frame parameter equalities
checked by the kernel; other fixture coherence is not an `Elaborated` claim.

## Certified syntax inventory; semantic extraction open

`Frontend/Admission/SyntaxOccurrences.lean` structurally enumerates the actual
intrinsic syntax with its category and payload (all 112 constructors,
maintained by hand when `Syn` changes). The root cons is outside the structurally recursive descendant
walk, so `syntaxOccurrences_root` proves that each actual typed root occurs
without unfolding that walk. It does not alter the source evaluator.

`SyntaxOccurrenceLaws.lean` exports `syntaxDescendants_children`, the outer
recursion equation for all 112 constructors. `syntaxOccurrences_sound` and
`syntaxOccurrences_complete` identify enumeration membership exactly with
the existing independent `Source.Syn.Sub` relation; `syntaxOccurrences_iff`
combines them. Categories and full syntax payloads are preserved. The
structural proof uses no fuel, finite sample or added premise.

`SyntaxOccurrenceControls` checks two branches with distinct payloads in
exact preorder, repeated payloads without deduplication, and rejection of
an omitted child. These list equalities additionally check concrete order
and multiplicity, which do not follow from membership equivalence alone.

The syntactic theorem does not identify execution/observation roots in a
resolved program and supplies no `Extractor` or profile-completeness witness.
Complete semantic-root extraction, exact profile classification and frontend
agreement remain open.

## Typed carried-program roots

`Frontend/Admission/ProgramRoots.lean` enumerates declaration bodies,
constants, constructors, state initializers and base-constructor arguments
from actual `Source.Program` fields and their finite declaration/contract
rosters. `ProgramRoot` retains the actual declaration/contract and carried
value; base arguments retain the locals indexed by their constructor. Body
roots include their modifier arguments. Modifier bodies are separate
registered declaration roots.

`programRoots_exact` proves membership iff the independent `Occurs`
roster-and-lookup relation holds. `programRoots_observations` proves that
flattening these roots gives the existing `programObservations` list exactly,
including order and repetitions. Both report standard axioms only
(`propext`, `Classical.choice`, `Quot.sound`). These are not proofs that every
runtime query or dynamic dispatch target lies in the rosters.

`ProgramRootControls.lean` checks an inhabited exact six-root inventory,
body/constant tag distinction, and refusal of a constructor removed from the
roster even though its body lookup remains populated. The fixture is
synthetic; function/modifier parameter agreement is checked, but it is not
an `Elaborated` or full execution-coherence witness. Removing a contract changes the root count from six to three.

`root_admission_equivalence` proves `RootAdmissionEquivalence` (A01).
It classifies observations alone, not every source feature or combination.

Open: prove actual source entry and call/modifier/dispatch queries remain in
the enumerated rosters, connect written syntax to resolved roots, and complete
exact feature/profile extraction plus checked-frontend agreement. The
on-demand `Source.progOf` body lookup does not itself restrict arbitrary
queries to the finite declaration roster; no such premise is silently added.

## Dispatch reuse and proof pins

`P9.WholeProgram.dispatch_mem` and `P8.DispatchCoverage.dispatchMod_mem`
already prove that dispatch stays in the declaration roster for an initially
registered target. These published results are reused; no duplicate theorem
is introduced. Connecting actual runtime queries to their initial membership
and to the typed roots remains open.

The V2 contract, subtree inventory, carried roots and control modules guard
their reported axiom sets with `#guard_msgs`. The frozen V1 module and source
evaluator are unchanged. These pins detect changes in proof dependencies;
they do not establish any missing semantic adequacy result.

## Initial name-selected target registration

`Frontend/Admission/NameResolutionRoots.lean` proves `lookup_registered`
for every actual `Env.lookup` result, including inherited visible scopes and
file-level fallback. `resolved_registered` consumes the independent source
`Resolves` relation through `Env.resolve_sound`; `functions_registered`
then shows that every declaration in `Ctx.functions` belongs to the same
environment's roster. No manually supplied target-membership premise is
accepted in place of the source resolution/selection evidence. All three
reports are pinned to `propext`.

`NameResolutionControls.lean` checks populated function lookup, local
shadowing/precedence, refusal of an unknown name and refusal of a constant as
a function. The roster is synthetic, not an `Elaborated` or SourceSpec
witness. These controls do not replace the universal resolver proofs.

`selected_function_membership` proves the singleton-overload proposition
`SelectedFunctionMembership` (A02). Connecting source-derived selected targets
to the complete resolved-tree visitor, modifier/external-call selections,
actual execution roots and exact profile remains open. Published P9/P8
dispatch results provide the later dispatch-membership step; they are not
reproved here.

## Initial modifier and qualified-path targets

`NameResolutionRoots.path_registered` covers actual unqualified and
single-qualified `Env.lookupPath` results, preserving the current deeper-path
refusal. Its axiom report is pinned to `propext`.

`Frontend/Admission/ModifierRoots.lean` proves `modifier_registered`: every
successful actual `Env.modifierAt` result belongs to the environment roster.
The proof consumes the singleton path result and both parameter forms;
failed kind/type selections are not treated as successful. No caller-supplied
initial roster-membership premise or body-availability assumption is added.
Its exact report is guarded to the standard axioms.

`ModifierRootControls.lean` exercises unqualified and qualified selection
with a primitive parameter, omitted parameters, wrong-kind refusal and
unchanged deeper-path refusal. These are populated selector controls, not
full `Elaborated`, execution-root or profile witnesses.

`derived_modifier_membership` and `external_overload_membership` prove
`DerivedModifierMembership` and `ExternalOverloadMembership` (A03–A04).
The source-selector soundness arguments stay in this lane. Wiring all derived
callee occurrences and actual execution queries to these initial-target
facts and published dispatch closure remains open.

Published VY5 modules `P8/FailureProjection.lean` and
`P8/SourceRealization.lean` now provide `SpecFailures` Bound operations and
`SpecExecution.run`/`Executes` anchored to actual Source execution. They do
not provide a concrete SourceSpec, failure-aware OperationalReference,
SourceOrigins or SourceRealization inhabitant. The runner still accepts a
Nat horizon. Their publication is consumed; it is not treated as completion
of H16 carrier-aware execution or the final Producer prerequisites.

## Checked frontend to actual unit programs

`Lowering/P8/SourcePrograms.lean` adds `accept`: existing original-byte parse,
resolution and component-metadata checks, followed by the actual
`Source.elaborate` on every resolved unit in order. No failed unit is dropped.
`elaborateUnits_sound` proves the independent per-position graph of the
upstream elaborator; `accept_sound` returns `Input.Ok`, the checked parse and
resolution judgments, existing `ComponentOK`, and that full-list graph.
`elaborateUnits_tail_failure` proves that a failed later unit forces the
whole result to fail, independently of the first program's proof data.
All three axiom reports are guarded to the standard axioms.

The candidate `produce` wrapper uses `CheckedSyntax.produce` and rechecks
through `accept`. It does not reroute the existing public solc-JSON compiler.
`produce_input_sound` proves `ProduceInputSound` (A06), and
`units_program_identity` proves `UnitsProgramIdentity` (A05). The latter uses
`P9.elaborate_program` theorem through the positional `UnitsRealize` relation.

`SourceProgramControls.lean` kernel-checks a separate minimal empty-unit
input returning one actual elaborated unit, an invalid-body refusal, and
retention of a failure in the second unit. This is not a SourceSpec
`NonVacuous` witness or a replacement for contract controls. The original direct
`ContractControls` attempts encountered the unchanged heartbeat/recursion
limits and a dependent rewrite-motive error; those failures remain failed.
The acceptance-projection control proof below now kernel-checks the four
original component observations, and the original conjunction is exported by `packed_controls`.
Earlier native evaluator observations remain separate historical evidence;
no limit or expected observation was changed.

This is a checked component-stage soundness result, not approved-profile
completeness, whole imported-name execution, public compiler/frontend
agreement, failure-aware SourceSpec or Source/EVM correspondence. The
remaining runtime-root and exact admission obligations above remain open.

## Actual entry-selector registration

`Lowering/P8/EntryRoots.lean` proves `function_entry`: an actual
`Glob.pickFn` hit yields initial environment membership, a present body after
virtual dispatch, and dispatched declaration membership. The published
`P9.WholeProgram.dispatch_mem` is reused. `special_entry` proves environment
membership and exact declaration kind from the actual inherited
receive/fallback lookup. That lookup does not check body availability; the
body premise remains explicit in `special_entry_body_coverage`.

These are selector facts, not executed-entry or receiver-reachability
proofs. Nonempty calldata, payment and argument-decoding checks, getters,
contract/account coherence, exact feature combinations and full admission
remain separate. `SelectedEntryRootCoverage` and `SpecialEntryBodyCoverage`
are proved by `selected_entry_root_coverage` and `special_entry_body_coverage`
(A07–A08), preserving the actual selector and successful body lookup.
No Source evaluator, interface or policy is replaced.

`EntryRootControls.lean` kernel-checks eight inhabited selector observations:
a public-function hit, wrong selector, missing body, absent contract,
receive and fallback identity, missing receive contract and wrong special
kind. The selected body contains a timestamp observation. This fixture
supplies an intrinsic `Program` and a deliberately constant hash; it is not
an elaboration, cryptographic, Source execution or EVM witness. Exact axiom
reports are guarded. Complete semantic admission and the original remaining
Producer obligations are still open.

## Whole-output observation admission

`Lowering/P8/SourceObservationAdmission.lean` composes the checked original-byte
frontend and actual all-unit elaboration with an executable observation guard.
Every returned elaborated unit is checked; order, names and intrinsic program
values are returned unchanged. `sound` proves the original input/parse,
resolution and component judgments, the full upstream elaboration graph,
`Allowed` for every independent `ProgramSite` in every output, and the exact
upstream admission equation. No caller chooses a smaller program subset.

This guard uses the existing local observation policy; it does not establish
complete feature extraction, feature-combination classification, runtime
receiver/getter closure, imported-name execution or full approved-profile
admission. `exact_observation_guard` proves `ExactObservationGuard` (A09)
for this guard; it does not replace those broader obligations.

`SourceObservationControls.lean` kernel-checks the minimal original-byte
empty-unit path, refusal after its bytes change, and the existing supplied
Program's seven populated observations. The byte refusal tests frontend
certificate checking, not a post-elaboration out-of-profile witness. The
populated fixture is not claimed to be canonical elaboration or execution.
These controls are separate from the nonempty contract component controls
below and do not instantiate SourceSpec nonvacuity. Full semantic admission/Producer obligations remain.

The observation-rejection question is now settled by proof, not a fabricated
negative fixture. `program_allowed` proves `WholeProgramPolicy` for every
intrinsic Program, and `check_all` applies it to every elaborated output.
`accept_eq_upstream` proves exact equality of the guarded and upstream results,
including dependent program values. The current local observation guard adds
no restriction after typing. Raw/frontend refusal controls remain valid, but
cannot be presented as exercising an impossible post-elaboration observation
rejection branch. This redundancy does not establish full-profile admission.

## Intrinsic observation-policy closure

`TypedObservationPolicy.lean` proves actual builtin/member typing implies
local allowance, with no axioms. `TypedExpressionPolicy.lean` proves
`expression_allowed` using the existing mutual recursor, including argument,
conversion and lvalue motives. The four container corollaries A10–A13 are
implemented. `TypedStatementPolicy.lean` supplies unconditional
`statement_allowed`, `program_allowed` and `closed_policies` (A14) by applying
the retained conditional builders to actual checked container proofs.
Every statement/item position, modifier argument, constant, constructor body,
initializer and base argument is covered. No finite sample, fuel bound,
runtime lookup premise or replacement program field is introduced.

Older recursive-function drafts remain failed/unvalidated; they are not the
proof used here. Current kernel closure excludes rejected observations from
the typed visitor, not out-of-profile source syntax, runtime stuckness or
unsupported feature combinations. It is not SourceSpec nonvacuity, universal
source execution or Source/EVM adequacy.

## Acceptance projection and nonempty contract controls

`SourcePrograms.elaborateUnits_complete` supplies the converse of the existing
all-unit graph soundness theorem. `elaborateUnits_iff` characterizes the exact
ordered list of names and dependent elaborated outputs. `accept_iff` adds the
unchanged original-byte/resolution/component guard: acceptance is equivalent
to that guard succeeding and `UnitsElaborate` holding. No failed unit is
removed, output replaced, parser completeness assumed or profile premise
weakened. These are exact component algorithm laws, not a proof that every
approved-profile input passes the guard or elaborates. Their axiom sets are
pinned to the standard three axioms in the module.


`Lowering/P8/SourceProgramAcceptance.lean` proves `elaborate_acceptance`
and `units_acceptance` for the actual algorithms: their success bits equal
the existing elaboration flag and its all-unit conjunction. These laws do
not replace returned program values, weaken graph/identity judgments or
assert source/profile completeness. `acceptance_projection` proves
`AdmitAcceptance`, the exact composition with the existing frontend guard (A15).

`SourceProgramAcceptanceControls.lean` reuses the original nonempty contract
input, parse certificates and component checks. Case analysis on the actual
optional elaboration result keeps successful proof payloads opaque. The
published P9 base-argument acceptance proof pattern establishes the actual
contract flag without the failed dependent-payload normalization.
`single_control` kernel-checks the unchanged `C.sol` output for both pipelines;
`two_control` preserves both original names and their order, and
`corrupted_control` kernel-checks the original changed-byte refusal.
`packed_controls : PackedControls` supplies the full original conjunction
(A16), using the existing component proofs. The original `ContractControls`
proposition is unchanged.

These are checked original-byte/per-unit Source stage observations. Duplicate
contract syntax across the two named files does not certify global imported
name typing. No source execution, SourceSpec `NonVacuous`, bytecode/world or
full admission claim follows. All prior failures and native observations are
retained separately; the new proofs add no premise or changed expectation.

## Current admission boundary

The local A01–A16 proof obligations are complete.
Lookup/derived-modifier/external-overload membership comes from actual source
selectors and derivations. Source output identity and candidate-wrapper
soundness preserve checked byte parsing, resolutions, component metadata and
all-unit elaboration. The public solc-JSON compiler has not been rerouted, and
its universal agreement with this checked path is not proved.

Concrete extraction/classification and full frontend/Producer agreement must
use the approved SourceSpec's Resolved/InProfile/meaning and independently
supplied source origins/realization. That contract and the H16 resource
extension belong to P8a-SPEC, which is not yet complete. Those fields remain
typed premises. No unapproved profile, root model,
countable-resource replacement or extra semantic premise is chosen here.
