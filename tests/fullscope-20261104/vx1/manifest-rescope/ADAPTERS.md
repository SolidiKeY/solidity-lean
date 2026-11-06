# H70 all-30 generator adapter inventory

This staged proposal specifies withdrawal of all30 language exclusions as open model work; the active catalog is not yet changed. It does not change active generated files while the generator owner adapter is absent. current=missing is conservative and does not erase preserved localEvidence or claim partial admission. Existing G00 Q1 provenance is preserved verbatim in before; it must not remain an active approvedExclusion decision after withdrawal.

Required generator-owner changes in scripts/solidity-feature-audit.py:

- render_lean: decouple structured unsupported diagnostic constructors from scope=exclude, retaining all existing constructor identities and inhabited BlockField. outsideScope must describe active scope, not unsupported implementation status.
- render_lean_info: replace Unmodelled.excluded and Feature.exclusion_complete with truthful unsupported-diagnostic coverage; do not prove unsupported features outside full-language scope. Coordinate theorem API consumers before removal.
- validate_decision/DECISION_OUTCOMES: record H37/H70 withdrawal provenance separately from old approvedExclusion; validate model/missing without asserting production support.
- render_report: display open whole-language work and preserved local evidence, not notApplicable or proved/model-complete.
- ledger: preserve all783 upstream symbol identities and mappings; describe formerly excluded references as open model obligations. Proposal enumerates every affected family/symbol.

Textual consumer census (Unmodelled, BlockField, outsideScope, exclusion_complete and unmodelled?; not a semantic dependency proof):

## Solidity/Frontend/Source.lean

- 306: outsideDiagnostic matches use.feature.unmodelled? and emits .excluded. VY5 must preserve unsupported rejection without treating full-language obligations as exclusions. Audit ScopeScan.certify and its WithinProfile certificate together; changing catalog scope must not silently admit unimplemented constructs. ScopeScan.requireCompilerCode also retains its independent validated-artifact check.


## Solidity/Frontend/Admission/Profile.lean

- 34-48: `ScopeScan.certify_iff` proves `certify` accepts exactly `WithinProfile`; it moves together with the `inProfile` change above.

## Solidity/Backend/Environment/Frames.lean

- 110: /-- Every excluded BlockField and the raw msg/tx fields remain absent from the

## Solidity/Semantics/Nondeterminism/Fork.lean

- 22: (`osaka_precompiles`). The Yul view and `Language.BlockField` agreements are

## Solidity/Semantics/Nondeterminism/ForkAgreement.lean

- 14: - `ForkSpec.ofBlockField` maps a `block.*` member (`Language.BlockField`,
- 24: def ForkSpec.ofBlockField (F : ForkSpec) : Language.BlockField → EnvField
- 36: def BlockEnv.blockField? {F : ForkSpec} (e : BlockEnv F) (b : Language.BlockField) : Option Word :=
- 37: e.field? (F.ofBlockField b)
- 39: theorem osaka_difficulty : ForkSpec.osaka.ofBlockField .difficulty = .prevrandao := rfl
- 41: theorem control_difficulty : ForkSpec.difficultyControl.ofBlockField .difficulty = .difficulty := rfl

Producer ownership: Source stays VY5; other frontend producers retain owners; generator path owner must be assigned/confirmed by coordinator. VX1 will regenerate its catalog outputs after adapter arrives. H38 Source/EVM reviews remain required before freeze; H67 pins remain coordinator-owned. No producer file edit is authorized by H70 routing.

## Generator adapter (VX1 G01, 2026-11-06)

`generator-adapter.patch` is the adapter against `scripts/solidity-feature-audit.py`
(generator-owned; VX1 does not edit it). `adapter.py` applies it in memory and:

- **Identity:** on the active manifest the patched generator's `--check` passes,
  so applying the patch changes no generated file.
- **Decoupling:** a structured `Unmodelled` diagnostic is rendered for
  `scope = exclude` *or* `diagnostic = unsupported`; constructor identities and
  `BlockField` are unchanged. With withdrawn rows present, `Unmodelled.excluded`
  becomes `Unmodelled.diagnosed` (excluded, or model work still `missing`);
  `Feature.exclusion_complete` is unchanged and still proved.
- **Provenance:** a withdrawn row carries `diagnostic: unsupported` and
  `withdrawal {question: H37/H70, date, record, prior}`; the old G00 Q1
  decision moves to `prior` and is validated against its record, never left
  active; the record's file and heading anchor are checked. Eight mutations
  (decision kept, either marker alone, `present`, re-excluded, wrong prior
  outcome, missing record, missing anchor) are rejected; `adapter.py` refuses
  to run under `python -O`.
- **Report:** withdrawn rows show "open, unsupported diagnostic until admitted".
- **Staging:** `--stage DIR` renders the 30-row transition (`staged/`, ignored;
  hashes in `staged.SHA256SUMS`, H44) and `Check.lean`, which kernel-checks
  (MCP diagnostics, no errors).

The staged outputs are evidence, not activatable: with the patch alone the
generated `Feature.inProfile`/`WithinProfile`/`ProfileSyntax` still test scope
only, and `outsideScope := Unmodelled.all` lists the 30 withdrawn features.
Before activation the generator must also render `Feature.inProfile` as
`(scope = model ∨ abstract) ∧ unmodelled? = none` and split `outsideScope`
(excluded) from the unsupported diagnostics.

Activation (writing the staged manifest and outputs) is also blocked on VY5:
`ScopeScan.certify` tests `scope = model ∨ abstract` before
`Feature.unmodelled?`, so the 30 withdrawn features would be silently admitted.
`adapter.py` prints that impact list. The Source fix is to reject on
`unmodelled? = some _` first (keeping `ScopeScan.certify_iff` with
`WithinProfile` strengthened by `unmodelled? = none`); then the generator owner
applies the patch and VX1 regenerates the catalog.
