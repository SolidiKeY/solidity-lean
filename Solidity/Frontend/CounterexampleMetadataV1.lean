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
def canonicalClauseV1? (input : CanonicalImportInputV1) (row : ImportRow)
    (functionIndex clauseIndex : Nat) : Except String (Option (CanonicalClauseV1 input row)) :=
  match h : input.read with
  | .error reason => .error reason
  | .ok contract =>
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
  input : CanonicalImportInputV1

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
  let some clause ← ofExcept (canonicalClauseV1? captured.input row functionIndex clauseIndex)
    | return none
  pure (some ⟨captured.input, row, clause⟩)

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
  let some clause ← ofExcept (canonicalClauseV1? captured.input retained.row.legacy
      functionIndex clauseIndex) | return none
  pure (some ⟨captured.input, retained, clause⟩)

theorem retainedCanonicalClauseV1_forget (metadata : RetainedCanonicalClauseV1) :
    metadata.retained.forget = metadata.retained.candidate.original := rfl

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
    let compilation ← ofExcept (Source.readCompilationUnit fixture)
    let compilerCode ← ofExcept (Source.readCompilerCode fixture compilation.primary compilation.provenance)
    let env ← getEnv
    let sourceNames := (J.nodes (.arr compilation.asts.toArray)).filterMap (J.str? · "name")
      |>.flatMap (·.splitOn ".") |>.eraseDups
    let context : CanonicalImportInputV1 := {
      ast := compilation.primary, name := N.getId.getString!, ren := [], testing := true,
      entrypoints := false, env := env, sourceNames := sourceNames,
      provenance := compilation.provenance, compilerCode := compilerCode,
      namedErrorSourceOrder := compilation.provenance.pipeline == some .viaIR,
      compilationUnits := if compilation.provenance.sources.isEmpty then [] else compilation.asts }
    elabCommand (← `(solc_import $path hash $expected as $N testing))
    unless before == (← IO.FS.readBinFile input) do throwError "fixture changed during import"
    let digest := Hashes.sha256Nat (fixture.compress.toUTF8.data.toList.map UInt8.toNat)
    liftCoreM <| addAndCompile <| .defnDecl {
      name := declaration, levelParams := [], type := mkConst ``Nat,
      value := toExpr digest, hints := .abbrev, safety := .safe }
    modifyEnv fun env => capturedCanonicalImportsV1.modifyState env
      (·.insert N.getId ⟨fixture, context⟩)

end Solidity.Frontend
