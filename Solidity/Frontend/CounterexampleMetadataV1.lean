import Solidity.Frontend.SpecOriginsV1
import Solidity.Frontend.Testing
import Solidity.Tools.VerifierMetadata

/-!
# Retained-certificate metadata ingress, V1

Guards the editor regression where a second counterexample search is attached
to the first report. This new consumer reads the actual imported report row and
its already-retained theorem, checks the exact goal and standard axiom boundary,
and recovers that proof's candidate. It never searches. Source origins retain
snapshot/owner context but are not yet associated with transformed canonical
postconditions: no failing source location is emitted by this foundation.
-/

namespace Solidity.Frontend
open Lean Elab Command Meta

/-- Opt-in importer companion. It invokes the unchanged testing importer and
records the exact parsed fixture identity for new consumers only. The original
FNV pin is still checked; a readback rejects changed final bytes. Callers must
keep the owned fixture stable under their writer lock throughout the call;
readback alone cannot detect an A-to-B-to-A concurrent replacement.
This is an elaborator input binding, not a theorem of compiler correctness. -/
syntax "solc_import_origins_v1 " str " hash " num " as " ident : command

/-- The original row is retained verbatim beside independently derived origins. -/
structure ImportRowOriginsV1 where
  legacy : ImportRow
  origins : AdmittedSpecOriginsV1

/-- No renamed parameters, tags, statuses or reasons are replaced. -/
def importRowOriginsV1? (fixture : Json) (sourceName : String) (bytes : ByteArray)
    (row : ImportRow) : Option ImportRowOriginsV1 := do
  guard row.admissionChecked
  let origins ← admittedSpecOriginsV1? fixture sourceName bytes row.sourceId
  pure ⟨row, origins⟩

theorem importRowOriginsV1_forget (row : ImportRow) (origins : AdmittedSpecOriginsV1) :
    (ImportRowOriginsV1.mk row origins).legacy = row := rfl

/-- This retains the proof candidate and source ownership separately. No source
span is reported as a failed postcondition before canonical correspondence. -/
structure RetainedCounterexampleMetadataV1 where
  row : ImportRowOriginsV1
  certificateDeclaration : Lean.Name
  candidate : Tools.SourceCounterexampleCandidateV1

/-- Forgetting ingress metadata keeps the original proof and JSON verbatim. -/
def RetainedCounterexampleMetadataV1.forget (metadata : RetainedCounterexampleMetadataV1) :
    Tools.SourceCounterexample := metadata.candidate.original

theorem retainedCounterexampleMetadataV1_forget (metadata : RetainedCounterexampleMetadataV1) :
    metadata.forget = metadata.candidate.original := rfl

/-- Load the row by its actual table index, then inspect the existing theorem's
body. Missing/nonstandard/other-goal certificates fail closed. Supplied JSON
is presentation, not evidence of current service state or verification policy.
The caller still audits the companion argument equality before publication. -/
def retainedCounterexampleMetadataV1? (N : Lean.Name) (rowIndex : Nat)
    (fixture : Json) (sourceName : String) (bytes : ByteArray)
    (report : Json) : CommandElabM (Option RetainedCounterexampleMetadataV1) := do
  let rows ← reportRows N
  let some row := rows[rowIndex]? | return none
  let some originRow := importRowOriginsV1? fixture sourceName bytes row | return none
  liftTermElabM do
    let fixtureDeclaration := N ++ `report ++ `fixtureSha256V1
    unless (← getEnv).contains fixtureDeclaration do return none
    let digest := Hashes.sha256Nat (fixture.compress.toUTF8.data.toList.map UInt8.toNat)
    unless ← isDefEq (mkConst fixtureDeclaration) (toExpr digest) do return none
    unless (report.getObjValAs? Bool "certified").toOption == some true &&
        (report.getObjValAs? String "goalKind").toOption == some "fmlValid" do return none
    unless ← isDefEq (mkConst (N ++ `report ++ `provenance)) (toExpr originRow.origins.provenance) do
      return none
    let name := row.declName N ++ `refuted
    unless (report.getObjValAs? String "certificateDeclaration").toOption == some name.toString do
      return none
    let some (.thmInfo certificate) := (← getEnv).find? name | return none
    let formula ← testFormula N row
    let goal ← mkAppM ``Solidity.Fml.Valid #[formula]
    unless ← isDefEq certificate.type (mkNot goal) do return none
    let axioms ← collectAxioms name
    unless axioms.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do return none
    let original : Tools.SourceCounterexample := ⟨certificate.value, report⟩
    let some candidate ← Tools.sourceCounterexampleCandidateV1? goal original | return none
    pure (some ⟨originRow, name, candidate⟩)


/-- Full context for the exact H126 reader. This is an input carrier, not a
certificate that a caller supplied the importer environment or current source. -/
structure CanonicalImportInputV1 where
  ast : Json
  name : String
  ren : List (String × String)
  testing : Bool
  entrypoints : Bool
  env : Environment
  sourceNames : List String
  provenance : Source.Provenance
  compilerCode : List (Int × (String × String))
  namedErrorSourceOrder : Bool
  compilationUnits : List Json := []

/-- Reuse the entire admitted computation; no normalization callback is copied. -/
def CanonicalImportInputV1.read (input : CanonicalImportInputV1) :
    Except String SolcContract :=
  readImportedContractV1 input.ast input.name input.ren input.testing input.entrypoints
    input.env input.sourceNames input.provenance input.compilerCode
    input.namedErrorSourceOrder input.compilationUnits

/-- Preserve every actual admission argument; no public reader default is used. -/
def CanonicalImportInputV1.ofAdmission (context : ImportNormalizationContextV1) : CanonicalImportInputV1 :=
  ⟨context.ast, context.name, context.ren, context.testing, context.entrypoints,
    context.env, context.sourceNames, context.provenance, context.compilerCode,
    context.namedErrorSourceOrder, context.compilationUnits⟩

theorem CanonicalImportInputV1.ofAdmission_read (context : ImportNormalizationContextV1) :
    (ofAdmission context).read = context.read.map Prod.fst := rfl

/-- Guards the regression where a clause from another normalizer, function or
ordinal is attached to a retained row. These equations identify the exact reader
result and canonical clause. They do not bind the input to a live importer or
prove that this clause failed, and deliberately contain no source span. -/
structure CanonicalClauseV1 (input : CanonicalImportInputV1) (row : ImportRow) where
  contract : SolcContract
  contractEquation : input.read = .ok contract
  functionIndex : Nat
  functionData : SolcFun
  functionEquation : (contract.funs ++ contract.ctor.toList)[functionIndex]? = some functionData
  sourceIdEquation : functionData.sourceId = row.sourceId
  nameEquation : functionData.name = row.name
  signatureEquation : functionData.sourceSignature = row.sourceSignature
  clauseIndex : Nat
  clause : String × String
  clauseEquation : functionData.specClauses[clauseIndex]? = some clause

/-- Exact indexed lookup, preserving reader errors. Unadmitted/synthetic/foreign
rows and absent ordinals yield no metadata; no text matching or index fallback.
The producer must separately bind this context to its actual importer/candidate
and prove source-origin and failed-clause correspondence before publication. -/
private def canonicalClauseInResultV1? (input : CanonicalImportInputV1) (row : ImportRow)
    (functionIndex clauseIndex : Nat) (contract : SolcContract)
    (h : input.read = .ok contract) : Except String (Option (CanonicalClauseV1 input row)) :=
  if !row.admissionChecked || input.provenance.legacyFixture || row.sourceId < 0 then .ok none
  else match hf : (contract.funs ++ contract.ctor.toList)[functionIndex]? with
  | none => .ok none
  | some f =>
    if hi : f.sourceId = row.sourceId then
      if hn : f.name = row.name then
        if hs : f.sourceSignature = row.sourceSignature then
          match hc : f.specClauses[clauseIndex]? with
          | none => .ok none
          | some clause => .ok (some ⟨contract, h, functionIndex, f, hf, hi, hn, hs,
              clauseIndex, clause, hc⟩)
        else .ok none
      else .ok none
    else .ok none


def canonicalClauseV1? (input : CanonicalImportInputV1) (row : ImportRow)
    (functionIndex clauseIndex : Nat) : Except String (Option (CanonicalClauseV1 input row)) :=
  match h : input.read with
  | .error reason => .error reason
  | .ok contract => canonicalClauseInResultV1? input row functionIndex clauseIndex contract h

/-- Dropping the clause ledger returns the exact original reader result. -/
def CanonicalClauseV1.forget {input : CanonicalImportInputV1} {row : ImportRow}
    (_clause : CanonicalClauseV1 input row) : Except String SolcContract := input.read

theorem canonicalClauseV1_forget {input : CanonicalImportInputV1} {row : ImportRow}
    (clause : CanonicalClauseV1 input row) : clause.forget = .ok clause.contract :=
  clause.contractEquation


/-- The pre-import context exists only in the elaborating process. Imported
modules cannot silently reconstruct it using a later environment. -/
private structure CapturedCanonicalImportV1 where
  fixture : Json
  admission : ImportedNormalizationCaptureV1

private initialize capturedCanonicalImportsV1 :
    EnvExtension (NameMap CapturedCanonicalImportV1) ←
  registerEnvExtension (pure {}) (asyncMode := .local)

/-- A clause read through the actual opt-in importer capture and table row.
It is not a source-span or failed-clause certificate. -/
structure ImportedCanonicalClauseV1 where
  input : CanonicalImportInputV1
  row : ImportRow
  clause : CanonicalClauseV1 input row

/-- No caller-supplied reader context is accepted. A missing process-local
capture, foreign fixture or missing table row is unavailable, not reconstructed. -/
def importedCanonicalClauseV1? (N : Lean.Name) (rowIndex functionIndex clauseIndex : Nat)
    (fixture : Json) : CommandElabM (Option ImportedCanonicalClauseV1) := do
  let some captured := (capturedCanonicalImportsV1.getState (← getEnv)).find? N
    | return none
  unless captured.fixture.compress == fixture.compress do return none
  let rows ← reportRows N
  let some row := rows[rowIndex]? | return none
  let input := CanonicalImportInputV1.ofAdmission captured.admission.context
  have h : input.read = .ok captured.admission.result.1 :=
    (CanonicalImportInputV1.ofAdmission_read captured.admission.context).trans
      (congrArg (Except.map Prod.fst) captured.admission.equation)
  let some clause ← ofExcept (canonicalClauseInResultV1? input row functionIndex clauseIndex
      captured.admission.result.1 h) | return none
  pure (some ⟨input, row, clause⟩)

/-- The exact retained candidate beside a clause from its actual captured
import context. This still does not establish that the selected clause failed. -/
structure RetainedCanonicalClauseV1 where
  input : CanonicalImportInputV1
  retained : RetainedCounterexampleMetadataV1
  clause : CanonicalClauseV1 input retained.row.legacy

/-- Joining the existing candidate ingress does not perform another search.
Source bytes, proof goal and namespace continue through their original checks. -/
def retainedCanonicalClauseV1? (N : Lean.Name) (rowIndex functionIndex clauseIndex : Nat)
    (fixture : Json) (sourceName : String) (bytes : ByteArray) (report : Json) :
    CommandElabM (Option RetainedCanonicalClauseV1) := do
  let some captured := (capturedCanonicalImportsV1.getState (← getEnv)).find? N
    | return none
  unless captured.fixture.compress == fixture.compress do return none
  let some retained ← retainedCounterexampleMetadataV1? N rowIndex fixture sourceName bytes report
    | return none
  let input := CanonicalImportInputV1.ofAdmission captured.admission.context
  have h : input.read = .ok captured.admission.result.1 :=
    (CanonicalImportInputV1.ofAdmission_read captured.admission.context).trans
      (congrArg (Except.map Prod.fst) captured.admission.equation)
  let some clause ← ofExcept (canonicalClauseInResultV1? input retained.row.legacy
      functionIndex clauseIndex captured.admission.result.1 h) | return none
  pure (some ⟨input, retained, clause⟩)

theorem retainedCanonicalClauseV1_forget (metadata : RetainedCanonicalClauseV1) :
    metadata.retained.forget = metadata.retained.candidate.original := rfl

/-- Ordered canonical projection with original clause ordinals. A failed
normalization drops the whole specification, exactly as the legacy reader does.
This consumes the admission ledger; it does not parse or normalize again. -/
def FunctionNormalizationRowV1.canonicalOrdinals (row : FunctionNormalizationRowV1) :
    List ((String × String) × Nat) :=
  ((row.normalization.results.mapM id).toOption.getD []).zipIdx.filterMap fun (clause, ordinal) =>
    if ["requires", "ensures", "invariant", "assignable"].contains clause.kind then
      some ((clause.kind, clause.text), ordinal) else none

/-- Source correspondence from the actual captured computation. The full
ordered canonical table and raw parser fields must agree, before selecting an
ordinal. A duplicate clause's text is never used to choose a source location.
This certifies correspondence only, not failure of the selected clause. -/
structure ImportedCanonicalSourceClauseV1 where
  admission : ImportedNormalizationCaptureV1
  row : ImportRow
  canonical : CanonicalClauseV1 (CanonicalImportInputV1.ofAdmission admission.context) row
  contractEquation : canonical.contract = admission.result.1
  ledgerIndex : Nat
  ledger : FunctionNormalizationRowV1
  ledgerEquation : admission.result.2[ledgerIndex]? = some ledger
  origins : AdmittedSpecOriginsV1
  ownerIdEquation : J.id? ledger.entry = some row.sourceId
  ownerEquation : ledger.entry.compress = origins.owner.compress
  rawEquation : origins.result.legacy.toOption.map (List.map specClauseFieldsV1) =
    some (ledger.rawSpec.map specClauseFieldsV1)
  canonicalEquation : canonical.functionData.specClauses =
    ledger.canonicalOrdinals.map Prod.fst
  rawOrdinal : Nat
  ordinalEquation : ledger.canonicalOrdinals[canonical.clauseIndex]? =
    some (canonical.clause, rawOrdinal)
  source : SpecClauseOriginV1
  sourceEquation : origins.result.origins.bind (·[rawOrdinal]?) = some source

/-- The source selector takes a namespace, actual report row and canonical
index, never an arbitrary input context or claimed clause text. A requested
span must equal the retained raw source extent; unsupported layouts refuse. -/
def importedCanonicalSourceClauseV1? (N : Lean.Name) (rowIndex functionIndex clauseIndex : Nat)
    (fixture : Json) (sourceName : String) (bytes : ByteArray)
    (span : YulJson.SourceSpan) : CommandElabM (Option ImportedCanonicalSourceClauseV1) := do
  let some captured := (capturedCanonicalImportsV1.getState (← getEnv)).find? N | return none
  unless captured.fixture.compress == fixture.compress do return none
  let rows ← reportRows N
  let some row := rows[rowIndex]? | return none
  let input := CanonicalImportInputV1.ofAdmission captured.admission.context
  have h : input.read = .ok captured.admission.result.1 :=
    (CanonicalImportInputV1.ofAdmission_read captured.admission.context).trans
      (congrArg (Except.map Prod.fst) captured.admission.equation)
  let some canonical ← ofExcept (canonicalClauseInResultV1? input row functionIndex clauseIndex
      captured.admission.result.1 h) | return none
  have contractEquation : canonical.contract = captured.admission.result.1 :=
    Except.ok.inj (canonical.contractEquation.symm.trans h)
  let some origins := admittedSpecOriginsV1? fixture sourceName bytes row.sourceId
    | return none
  -- Require one source-ID match, rather than choosing a first duplicate.
  let candidates := captured.admission.result.2.zipIdx.filter fun (entry, _) =>
    J.id? entry.entry == some row.sourceId
  let [(_, ledgerIndex)] := candidates | return none
  match hl : captured.admission.result.2[ledgerIndex]? with
  | none => return none
  | some ledger =>
    if hid : J.id? ledger.entry = some row.sourceId then
     if ho : ledger.entry.compress = origins.owner.compress then
       if hr : origins.result.legacy.toOption.map (List.map specClauseFieldsV1) =
           some (ledger.rawSpec.map specClauseFieldsV1) then
         if hc : canonical.functionData.specClauses = ledger.canonicalOrdinals.map Prod.fst then
           match hi : ledger.canonicalOrdinals[clauseIndex]? with
           | none => return none
           | some (clause, ordinal) =>
             if he : clause = canonical.clause then
               match hs : origins.result.origins.bind (·[ordinal]?) with
               | none => return none
               | some source =>
                 if source.span != span || source.ordinal != ordinal then return none
                 -- The canonical lookup preserves its requested index.
                 if hci : canonical.clauseIndex = clauseIndex then
                   have ordinalEquation : ledger.canonicalOrdinals[canonical.clauseIndex]? =
                       some (canonical.clause, ordinal) := by
                     rw [hci, hi, he]
                   return some ⟨captured.admission, row, canonical, contractEquation, ledgerIndex, ledger, hl,
                     origins, hid, ho, hr, hc, ordinal, ordinalEquation, source, hs⟩
                 else return none
             else return none
         else return none
       else return none
     else return none
    else return none

/-- Forgetting source correspondence preserves the actual imported clause. -/
theorem importedCanonicalSourceClauseV1_forget (metadata : ImportedCanonicalSourceClauseV1) :
    metadata.canonical.forget = .ok metadata.canonical.contract :=
  metadata.canonical.contractEquation

/-- The typed ensures table used by the existing specification elaborator.
Constructors are not accepted by SpecProblem.of and remain unavailable below. -/
def importedEnsuresTableV1? (C : Contract) (name : String) : Option (List SpecExpr) := do
  let declaration ← Semantics.lookupBy name C.funs
  pure declaration.spec.ensures

/-- Check one actual ensures ordinal at the supplied (already retained) inputs.
The original typed formula, premise, update, call, framing and loop fuel are
those of SpecProblem.of/Fml.postFails. A halt, unknown shape or non-failing
selected clause returns false. This performs no candidate search. -/
def selectedEnsuresFailsV1 (C : Contract) (name : String) (ensuresOrdinal : Nat)
    (domain : TDom) (values : List (Var × Semantics.CallValue))
    (state : State C []) : Bool :=
  match Tools.SpecProblem.of C name with
  | .error _ => false
  | .ok problem =>
    if ensuresOrdinal >= problem.decl.spec.ensures.length then false else
    let ⟨_, current, body⟩ := Fml.peel values state problem.fml
    Fml.enteredPostFailsV1 domain problem.posts.length (C.inv.length + ensuresOrdinal) current body

/-- Semantic failure at the same retained inputs: the entry is true and the
existing typed update/call reaches a concrete post-state with an exact false
slot. The index is the actual invariant prefix plus the selected ensures ordinal. -/
def IndexedSpecPostFailureV1 (C : Contract) (name : String) (ensuresOrdinal : Nat)
    (_domain : TDom) (values : List (Var × Semantics.CallValue)) (state : State C []) : Prop :=
  ∃ problem : Tools.SpecProblem C,
    Tools.SpecProblem.of C name = .ok problem ∧
    ensuresOrdinal < problem.decl.spec.ensures.length ∧
    let ⟨_, current, body⟩ := Fml.peel values state problem.fml
    Fml.EnteredFailedPostSlotV1 problem.posts.length (C.inv.length + ensuresOrdinal) current body

/-- Convert a checked actual failure computation to the semantic false-slot
witness. This theorem uses no premise about any other postcondition failing. -/
theorem indexedSpecPostFailureV1_of_true (C : Contract) (name : String) (ensuresOrdinal : Nat)
    (domain : TDom) (values : List (Var × Semantics.CallValue)) (state : State C [])
    (checked : selectedEnsuresFailsV1 C name ensuresOrdinal domain values state = true) :
    IndexedSpecPostFailureV1 C name ensuresOrdinal domain values state := by
  cases problemResult : Tools.SpecProblem.of C name with
  | error reason =>
    simp only [selectedEnsuresFailsV1, problemResult] at checked
    cases checked
  | ok problem =>
    by_cases bound : ensuresOrdinal < problem.decl.spec.ensures.length
    · refine ⟨problem, problemResult, bound, ?_⟩
      have selected : (let ⟨_, current, body⟩ := Fml.peel values state problem.fml
          Fml.enteredPostFailsV1 domain problem.posts.length (C.inv.length + ensuresOrdinal) current body) = true := by
        simpa only [selectedEnsuresFailsV1, problemResult, if_neg (Nat.not_le_of_gt bound)] using checked
      exact Fml.enteredFailedPostSlotV1_of_true domain problem.posts.length (C.inv.length + ensuresOrdinal)
        (Fml.peel values state problem.fml).2.1 (Fml.peel values state problem.fml).2.2 selected
    · have outside : ensuresOrdinal >= problem.decl.spec.ensures.length := Nat.le_of_not_gt bound
      simp only [selectedEnsuresFailsV1, problemResult, if_pos outside] at checked
      cases checked

/-- A concrete terminal-slot equality to the clause interpreted in the actual
compiler-produced named context. No source string selects a terminal clause. -/
def IndexedSpecPostMatchesV1 (C : Contract) (name : String) (ordinal : Nat)
    (values : List (Var × Semantics.CallValue)) (state : State C []) (family : TypedPostFamilyV1 C) : Prop :=
  match Tools.SpecProblem.of C name with
  | .error _ => False
  | .ok problem =>
    let ⟨_, _, body⟩ := Fml.peel values state problem.fml
    Fml.EnteredSlotMatchesV1 problem.posts.length (C.inv.length + ordinal) family body

/-- Successful typed execution refutes the particular compiled named clause
in its actual output context, at the original retained inputs. -/
def NamedSpecPostFailureV1 (C : Contract) (name : String) (ordinal : Nat)
    (_domain : TDom) (values : List (Var × Semantics.CallValue)) (state : State C [])
    (family : TypedPostFamilyV1 C) : Prop :=
  ∃ problem : Tools.SpecProblem C, Tools.SpecProblem.of C name = .ok problem ∧
    ordinal < problem.decl.spec.ensures.length ∧
    let ⟨_, current, body⟩ := Fml.peel values state problem.fml
    Fml.EnteredNamedPostFailureV1 family current body

theorem namedSpecPostFailureV1_of_indexed (C : Contract) (name : String) (ordinal : Nat)
    (domain : TDom) (values : List (Var × Semantics.CallValue)) (state : State C [])
    (family : TypedPostFamilyV1 C)
    (failed : IndexedSpecPostFailureV1 C name ordinal domain values state)
    (matched : IndexedSpecPostMatchesV1 C name ordinal values state family) :
    NamedSpecPostFailureV1 C name ordinal domain values state family := by
  rcases failed with ⟨problem, equation, bound, entered⟩
  refine ⟨problem, equation, bound, ?_⟩
  have slot : (let ⟨_, _, body⟩ := Fml.peel values state problem.fml
      Fml.EnteredSlotMatchesV1 problem.posts.length (C.inv.length + ordinal) family body) := by
    simpa only [IndexedSpecPostMatchesV1, equation] using matched
  exact Fml.enteredNamedPostFailureV1_of_slot problem.posts.length (C.inv.length + ordinal) family
    (Fml.peel values state problem.fml).2.1 (Fml.peel values state problem.fml).2.2 entered slot

private def successfulPayloadV1? (expression : Expr) : TermElabM (Option Expr) := do
  let value ← withTransparency .all (whnf expression)
  let (head, arguments) := value.getAppFnArgs
  if head == ``Except.ok || head == ``Option.some then return arguments.back?
  else return none

initialize registerTraceClass `Solidity.Frontend.selectedPostconditionV1

/-- Retain a closed theorem only after the existing kernel/trust ceiling checks.
The caller never supplies a proof to the public metadata publisher. -/
private def retainSelectedCertificateV1? (namePrefix : Lean.Name) (type proof : Expr) :
    TermElabM (Option Lean.Name) := do
  let type ← instantiateMVars type
  let proof ← instantiateMVars proof
  if [type, proof].any (fun e => e.hasMVar || e.hasFVar || e.hasSorry || e.hasLevelMVar) then return none
  unless ← isProp type do return none
  let options ← getOptions
  let current := maxHeartbeats.get options
  let limit := if current == 0 then 100000 else min current 100000
  let name ← mkFreshUserName namePrefix
  let declaration := Declaration.thmDecl { name, levelParams := [], type, value := proof }
  try
    withOptions (fun _ => debug.skipKernelTC.set (maxHeartbeats.set options limit) false) (addDecl declaration)
    let axioms ← collectAxioms name
    unless axioms.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do return none
    pure (some name)
  catch _ => pure none

/-- Experimental diagnostic evidence, not failed-source publication. Exact
retained inputs, typed execution and named-clause matching are all mandatory.
Opaque partial source compilers can prevent the required kernel equalities;
that case remains unavailable. No source span or certified-failed-clause flag
is emitted and no second search is used. -/
def checkedRetainedPostSlotV1? (N : Lean.Name) (rowIndex functionIndex clauseIndex : Nat)
    (fixture : Json) (sourceName : String) (bytes : ByteArray)
    (span : YulJson.SourceSpan) (report : Json) : CommandElabM (Option Json) :=
  withScope (fun scope => { scope with opts := debug.skipKernelTC.set scope.opts false }) do
    let some source ← importedCanonicalSourceClauseV1? N rowIndex functionIndex clauseIndex
        fixture sourceName bytes span | return none
    unless source.canonical.clause.1 == "ensures" do return none
    let some retained ← retainedCounterexampleMetadataV1? N rowIndex fixture sourceName bytes report
      | return none
    -- The same source ID/signature is necessary but never replaces exact-goal checking.
    unless retained.row.legacy.sourceId == source.row.sourceId &&
        retained.row.legacy.name == source.row.name &&
        retained.row.legacy.sourceSignature == source.row.sourceSignature do return none
    liftTermElabM do
      let saved ← Term.saveState
      let messages ← Core.getMessageLog
      let phase ← IO.mkRef "entry"
      let result ← tryCatchRuntimeEx (do
        let candidate := retained.candidate
        unless candidate.contract.isConstOf N do return none
        let ensures := source.canonical.functionData.specClauses.filter (·.1 == "ensures")
        let ordinal := (source.canonical.functionData.specClauses.take clauseIndex).filter (·.1 == "ensures") |>.length
        let mut expanded : List Expr := []
        for (_, text) in ensures do
          let parsed ← ofExcept (Parser.runParserCategory source.admission.context.env `spec_expr text)
          let expression ← Term.withoutErrToSorry <| Term.elabTerm (← `(spec!($(⟨parsed⟩):spec_expr)))
            (some (mkConst ``SpecExpr))
          Term.synthesizeSyntheticMVarsNoPostponing
          expanded := expanded ++ [← instantiateMVars expression]
        phase.set "typed-table"
        let table ← mkListLit (mkConst ``SpecExpr) expanded
        let actual ← mkAppM ``importedEnsuresTableV1? #[candidate.contract, toExpr source.row.name]
        let expected ← mkAppM ``Option.some #[table]
        unless ← isDefEq actual expected do return none
        let some tableCertificate ← retainSelectedCertificateV1? (N ++ `selectedEnsuresTableV1)
            (← mkEq actual expected) (← mkEqRefl expected) | return none
        phase.set "typed-formula"
        let problem ← withTransparency .all (whnf (← mkAppM ``Tools.SpecProblem.of #[candidate.contract, toExpr source.row.name]))
        let (``Except.ok, args) := problem.getAppFnArgs | do
          phase.set ("typed-formula reader: " ++ (← ppExpr problem).pretty)
          return none
        let some problem := args.back? | return none
        let formula ← mkAppM ``Tools.SpecProblem.fml #[problem]
        unless ← isDefEq formula candidate.formula do
          phase.set ("typed-formula mismatch: " ++ (← ppExpr formula).pretty ++ " <> " ++ (← ppExpr candidate.formula).pretty)
          return none
        let some formulaCertificate ← retainSelectedCertificateV1? (N ++ `selectedFormulaV1)
            (← mkEq formula candidate.formula) (← mkEqRefl candidate.formula) | return none
        let some valuesCertificate ← retainSelectedCertificateV1? (N ++ `selectedValuesV1)
            (← inferType candidate.valuesEquation) candidate.valuesEquation | return none
        phase.set "selected-computation"
        let evaluated ← mkAppM ``selectedEnsuresFailsV1 #[candidate.contract, toExpr source.row.name,
          toExpr ordinal, candidate.domain, candidate.values, candidate.state]
        let failureType ← mkEq evaluated (mkConst ``Bool.true)
        let failure ← mkDecideProof failureType
        let some failureCertificate ← retainSelectedCertificateV1? (N ++ `selectedPostFailureV1)
            failureType failure | return none
        phase.set "semantic-witness"
        let semanticType ← mkAppM ``IndexedSpecPostFailureV1 #[candidate.contract, toExpr source.row.name,
          toExpr ordinal, candidate.domain, candidate.values, candidate.state]
        let semanticProof ← mkAppM ``indexedSpecPostFailureV1_of_true #[candidate.contract,
          toExpr source.row.name, toExpr ordinal, candidate.domain, candidate.values, candidate.state,
          mkConst failureCertificate]
        let some semanticCertificate ← retainSelectedCertificateV1? (N ++ `selectedPostSemanticV1)
            semanticType semanticProof | return none
        phase.set "actual-typed-context"
        let some compilation ← successfulPayloadV1? (← mkAppM ``specObligationWithContextV1
            #[candidate.contract, toExpr source.row.name]) | return none
        let compiledFormula ← mkAppM ``SpecObligationContextV1.formula #[compilation]
        unless ← isDefEq compiledFormula candidate.formula do return none
        let some contextFormulaCertificate ← retainSelectedCertificateV1? (N ++ `selectedContextFormulaV1)
            (← mkEq compiledFormula candidate.formula) (← mkEqRefl candidate.formula) | return none
        let pieces ← mkAppM ``SpecObligationContextV1.pieces #[compilation]
        let postContext ← mkAppM ``SpecPiecesContextV1.postContext #[pieces]
        let compiledEnsures ← mkAppM ``SpecPiecesContextV1.ensures #[pieces]
        let some selectedRead ← successfulPayloadV1? (← mkAppM ``List.get?
            #[compiledEnsures, toExpr ordinal]) | return none
        let some selectedExpression := expanded[ordinal]? | return none
        phase.set "selected-typed-compilation"
        let actualRead ← mkAppM ``SpecExpr.fml #[candidate.contract, postContext, selectedExpression]
        let expectedRead ← mkAppM ``Except.ok #[selectedRead]
        unless ← isDefEq actualRead expectedRead do return none
        let some compilationCertificate ← retainSelectedCertificateV1? (N ++ `selectedCompilationV1)
            (← mkEq actualRead expectedRead) (← mkEqRefl expectedRead) | return none
        let modal ← mkAppM ``SpecObligationContextV1.modal #[compilation]
        let names ← mkAppM ``SpecModalContextV1.names #[modal]
        let interpreted := mkApp selectedRead names
        let some selectedClause ← successfulPayloadV1? interpreted | return none
        let expectedInterpretation ← mkAppM ``Except.ok #[selectedClause]
        let some interpretationCertificate ← retainSelectedCertificateV1? (N ++ `selectedInterpretationV1)
            (← mkEq interpreted expectedInterpretation) (← mkEqRefl expectedInterpretation) | return none
        let contextEquation ← mkAppM ``SpecModalContextV1.contextEquation #[modal]
        let terminalClause ← mkEqNDRec (mkApp (mkConst ``Fml) candidate.contract) selectedClause contextEquation
        let family ← mkAppM ``typedPostFamilyV1 #[terminalClause]
        phase.set "exact-terminal-slot"
        let matchesType ← mkAppM ``IndexedSpecPostMatchesV1 #[candidate.contract, toExpr source.row.name,
          toExpr ordinal, candidate.values, candidate.state, family]
        let matchesProof ← Term.withoutErrToSorry <| Term.elabTerm (← `(by exact ⟨_, rfl, rfl⟩)) (some matchesType)
        Term.synthesizeSyntheticMVarsNoPostponing
        let some matchesCertificate ← retainSelectedCertificateV1? (N ++ `selectedSlotMatchesV1)
            matchesType (← instantiateMVars matchesProof) | return none
        phase.set "named-semantic-witness"
        let namedType ← mkAppM ``NamedSpecPostFailureV1 #[candidate.contract, toExpr source.row.name,
          toExpr ordinal, candidate.domain, candidate.values, candidate.state, family]
        let namedProof ← mkAppM ``namedSpecPostFailureV1_of_indexed #[candidate.contract,
          toExpr source.row.name, toExpr ordinal, candidate.domain, candidate.values, candidate.state,
          family, mkConst semanticCertificate, mkConst matchesCertificate]
        let some namedCertificate ← retainSelectedCertificateV1? (N ++ `selectedNamedFailureV1)
            namedType namedProof | return none
        let certificates := [retained.certificateDeclaration, tableCertificate, formulaCertificate,
          valuesCertificate, failureCertificate, semanticCertificate, contextFormulaCertificate,
          compilationCertificate, interpretationCertificate, matchesCertificate, namedCertificate]
        let audited ← certificates.mapM fun name => do
          let axioms ← collectAxioms name
          pure (Json.mkObj [("declaration", toJson name.toString),
            ("axioms", toJson (axioms.map Name.toString))])
        pure (some (Json.mkObj [
          ("schemaVersion", toJson (1 : Nat)), ("certifiedSlot", toJson true),
          ("kind", toJson "retained-numeric-post-slot-v1"),
          ("sourceAttribution", toJson "unavailable: kernel-checkable source compiler correspondence pending"),
          ("source", toJson sourceName), ("sourceSha256", toJson source.origins.sourceSha256),
          ("sourceId", toJson source.row.sourceId), ("signature", toJson source.row.sourceSignature),
          ("canonicalClauseIndex", toJson clauseIndex), ("rawClauseOrdinal", toJson source.rawOrdinal),
          ("ensuresOrdinal", toJson ordinal),
          ("certificates", toJson audited)])))
        fun error => do
          phase.set ("exception: " ++ (← error.toMessageData.toString))
          pure none
      if result.isNone then
        saved.restore
        trace[Solidity.Frontend.selectedPostconditionV1] "unavailable at {(← phase.get)}"
      else Core.setMessageLog messages
      return result

elab_rules : command
  | `(solc_import_origins_v1 $path:str hash $expected:num as $N:ident) => do
    let file := System.FilePath.mk (← getFileName)
    let input := (file.parent.getD ".") / path.getString
    let before ← IO.FS.readBinFile input
    unless (fnv1a64 before).toNat == expected.getNat do throwError "fixture input hash mismatch"
    let some text := String.fromUTF8? before | throwError "fixture is not UTF-8"
    let fixture ← ofExcept (Json.parse text)
    let declaration := N.getId ++ `report ++ `fixtureSha256V1
    if (← getEnv).contains N.getId || (← getEnv).contains declaration then
      throwError "origin companion requires a new import namespace"
    requestImportNormalizationV1 N.getId
    elabCommand (← `(solc_import $path hash $expected as $N testing))
    unless before == (← IO.FS.readBinFile input) do throwError "fixture changed during import"
    let some admission ← importedNormalizationCaptureV1? N.getId
      | throwError "actual importer normalization capture unavailable"
    unless admission.bytes == before && admission.fixture.compress == fixture.compress do
      throwError "actual importer normalization snapshot differs"
    let digest := Hashes.sha256Nat (fixture.compress.toUTF8.data.toList.map UInt8.toNat)
    liftCoreM <| addAndCompile <| .defnDecl {
      name := declaration, levelParams := [], type := mkConst ``Nat,
      value := toExpr digest, hints := .abbrev, safety := .safe }
    modifyEnv fun env => capturedCanonicalImportsV1.modifyState env
      (·.insert N.getId ⟨fixture, admission⟩)

end Solidity.Frontend
