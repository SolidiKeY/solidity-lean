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
    elabCommand (← `(solc_import $path hash $expected as $N testing))
    unless before == (← IO.FS.readBinFile input) do throwError "fixture changed during import"
    let digest := Hashes.sha256Nat (fixture.compress.toUTF8.data.toList.map UInt8.toNat)
    liftCoreM <| addAndCompile <| .defnDecl {
      name := declaration, levelParams := [], type := mkConst ``Nat,
      value := toExpr digest, hints := .abbrev, safety := .safe }

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

end Solidity.Frontend
