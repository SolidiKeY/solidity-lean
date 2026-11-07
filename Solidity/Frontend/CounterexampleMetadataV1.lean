import Solidity.Frontend.SpecOriginsV1
import Solidity.Frontend.Testing

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
