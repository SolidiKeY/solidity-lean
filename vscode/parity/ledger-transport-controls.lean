import Solidity.Frontend.CounterexampleMetadataV1

/-!
# Admission-ledger transport controls

Guards reconstruction with public defaults, duplicate-text source selection,
and stale snapshot/ordinal substitution. Run after an actual opt-in compiler
import and retained counterexample in the same process. Source correspondence
and retained full-goal failure are checked separately: this does not assert
that the selected postcondition fails at the candidate.
-/
open Lean Elab Command Solidity.Frontend

private def ledgerCoverageV1 (checked expected : Nat) (exercised refused names refusals : List String) :
    Except String Unit :=
  if checked == expected && exercised == names && refused == refusals then .ok ()
  else .error s!"required control coverage missing: links={checked}, exercised={exercised}, refused={refused}"

syntax "#ledger_transport_controls " ident str str str " expecting " num str str : command

elab_rules : command
  | `(#ledger_transport_controls $N:ident $astPath:str $sourcePath:str $reportPath:str expecting $expected:num $expectedNames:str $expectedRefusals:str) => do
    let fixture ← ofExcept (Json.parse (← IO.FS.readFile astPath.getString))
    let bytes ← IO.FS.readBinFile sourcePath.getString
    let some capture ← importedNormalizationCaptureV1? N.getId
      | throwError "missing actual admission capture"
    unless capture.bytes == (← IO.FS.readBinFile astPath.getString) &&
        capture.fixture.compress == fixture.compress && !capture.context.env.contains N.getId do
      throwError "not the actual pre-import snapshot/context"
    let rows ← reportRows N.getId
    let functions := capture.result.1.funs ++ capture.result.1.ctor.toList
    let mut checked := 0
    let mut exercised : List String := []
    let mut refused : List String := []
    for (row, rowIndex) in rows.zipIdx do
      let some fi := functions.findIdx? (fun f => f.sourceId == row.sourceId &&
          f.name == row.name && f.sourceSignature == row.sourceSignature) | continue
      let some origins := admittedSpecOriginsV1? fixture sourcePath.getString bytes row.sourceId
        | continue
      let some locations := origins.result.origins | do
        let some ownerSrc := J.str? origins.owner "src" | throwError "missing owner extent"
        let .ok ownerSpan := YulJson.sourceSpan ownerSrc | throwError "invalid owner span"
        if (← importedCanonicalSourceClauseV1? N.getId rowIndex fi 0 fixture
            sourcePath.getString bytes ownerSpan).isSome then
          throwError "unsupported origin layout accepted"
        logInfo m!"UNSUPPORTED_ORIGIN_REFUSED {row.sourceSignature}"
        refused := refused ++ [row.sourceSignature]
        continue
      let some ledger := capture.result.2.find? (fun r => J.id? r.entry == some row.sourceId)
        | continue
      if ["renamed", "bound"].contains row.sourceName then
        let some raw := ledger.rawSpec[0]? | throwError "missing normalization control raw clause"
        let some normalizedResult := ledger.normalization.results[0]?
          | throwError "missing normalization control result"
        let Except.ok normalized := normalizedResult | throwError "normalization control refused"
        unless raw.text != normalized.text do throwError "normalization control did not change binding/constant"
        logInfo m!"NORMALIZED {row.sourceName}: {raw.text} => {normalized.text}"
      for ((_, ordinal), ci) in ledger.canonicalOrdinals.zipIdx do
        let some location := locations[ordinal]? | throwError "missing actual raw ordinal"
        let some result ← importedCanonicalSourceClauseV1? N.getId rowIndex fi ci fixture
            sourcePath.getString bytes location.span | throwError "actual source linkage refused: {row.name}/{ci}"
        unless result.rawOrdinal == ordinal && result.source.span == location.span do
          throwError "wrong source ordinal/span"
        if (← importedCanonicalSourceClauseV1? N.getId rowIndex fi ci fixture
            sourcePath.getString bytes {location.span with start := location.span.start + 1}).isSome then
          throwError "wrong span accepted"
        if (← importedCanonicalSourceClauseV1? N.getId rowIndex fi ci fixture
            (sourcePath.getString ++ ".wrong") bytes location.span).isSome then
          throwError "wrong source accepted"
        if (← importedCanonicalSourceClauseV1? N.getId rowIndex fi ci fixture
            sourcePath.getString (bytes.push 32) location.span).isSome then
          throwError "stale source accepted"
        if (← importedCanonicalSourceClauseV1? N.getId rowIndex fi ledger.canonicalOrdinals.length fixture
            sourcePath.getString bytes location.span).isSome then
          throwError "wrong canonical ordinal accepted"
        for other in locations do
          if other.ordinal != ordinal && (← importedCanonicalSourceClauseV1? N.getId rowIndex fi ci fixture
              sourcePath.getString bytes other.span).isSome then
            throwError "duplicate/other ordinal span accepted"
        checked := checked + 1
        exercised := exercised ++ [row.sourceSignature]
        logInfo m!"SOURCE_LINK {row.sourceSignature} canonical={ci} raw={ordinal} span={repr location.span}"
    let names := expectedNames.getString.splitOn "|"
    let refusals := expectedRefusals.getString.splitOn "|"
    let _ ← ofExcept (ledgerCoverageV1 checked expected.getNat exercised refused names refusals)
    if (ledgerCoverageV1 checked expected.getNat exercised.eraseDups refused names refusals).isOk then
      throwError "missing multiplicity control accepted"
    if (ledgerCoverageV1 (checked - 1) expected.getNat exercised.dropLast refused names refusals).isOk then
      throwError "missing required link accepted"
    if (ledgerCoverageV1 checked expected.getNat exercised [] names refusals).isOk then
      throwError "missing refusal control accepted"
    logInfo "COVERAGE_MULTIPLICITY_LINK_AND_REFUSAL_NEGATIVES_PASS"
    let some badIndex := rows.findIdx? (·.sourceName == "bad") | throwError "missing actual failing row"
    let some bad := rows[badIndex]? | throwError "failing row index"
    let report ← ofExcept (Json.parse (← IO.FS.readFile reportPath.getString))
    let results ← ofExcept report.getArr?
    let some actual := results.toList.find? (fun r => (r.getObjValAs? Int "sourceId").toOption == some bad.sourceId)
      | throwError "missing actual result"
    let witness ← ofExcept (actual.getObjVal? "counterexample")
    let some retained ← retainedCounterexampleMetadataV1? N.getId badIndex fixture sourcePath.getString bytes witness
      | throwError "missing actual retained candidate"
    unless retained.certificateDeclaration == bad.declName N.getId ++ `refuted do
      throwError "wrong retained theorem"
    let badInput := { capture.context with ast := Json.null }
    match badInput.read with
    | .error reason => logInfo m!"READER_REFUSAL {reason}"
    | .ok _ => throwError "malformed AST admitted"
    logInfo m!"LEDGER_TRANSPORT_CONTROLS_PASS links={checked}; retained same-goal candidate; selected-clause failure remains unproved"
