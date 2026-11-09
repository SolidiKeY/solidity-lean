import Solidity.Frontend.CounterexampleMetadataV1

/-!
# Same-candidate selected-postcondition controls

Guards the regression where a whole-goal refutation is attached to an arbitrary
numeric post slot. Span publication remains unavailable until the actual partial source compiler
correspondence is kernel checked. These controls require genuine compiler/import rows and retained
proofs. They check the exact failure certificate inputs, mixed true/false clauses,
duplicate ordinal identities, normalization and source/namespace refusals.
-/
open Lean Elab Command Meta Solidity.Frontend

syntax "#retained_post_slot_controls " ident ident str str str str str : command

elab_rules : command
  | `(#retained_post_slot_controls $N:ident $foreignN:ident $astPath:str $sourcePath:str $reportPath:str $foreignReportPath:str $output:str) => do
    let fixture ← Lean.ofExcept (Json.parse (← IO.FS.readFile astPath.getString))
    let bytes ← IO.FS.readBinFile sourcePath.getString
    let report ← Lean.ofExcept (Json.parse (← IO.FS.readFile reportPath.getString))
    let results ← ofExcept report.getArr?
    let foreignReport ← Lean.ofExcept (Json.parse (← IO.FS.readFile foreignReportPath.getString))
    let foreignResults ← ofExcept foreignReport.getArr?
    let some foreignResult := foreignResults.toList.find? (fun r =>
      (r.getObjValAs? String "status").toOption == some "refuted")
      | throwError "missing genuine foreign refutation"
    let foreignWitness ← Lean.ofExcept (foreignResult.getObjVal? "counterexample")
    let some capture ← importedNormalizationCaptureV1? N.getId | throwError "no actual capture"
    let rows ← reportRows N.getId
    let functions := capture.result.1.funs ++ capture.result.1.ctor.toList
    unless N.getId == `SelectedCases || N.getId == `FrameCases do
      throwError "unsupported fixed control fixture"
    let cases : List (String × List Bool) := if N.getId == `SelectedCases then [
      ("mixed", [false, true, false]), ("duplicate", [true, true]),
      ("renamed", [true]), ("bound", [true]), ("panics", [false])]
      else [("oldWrong", [true]), ("frameOnly", [false])]
    let requiredPositive := if N.getId == `SelectedCases then 5 else 1
    let requiredTotal := if N.getId == `SelectedCases then 8 else 2
    let mut ordered : List Json := []
    let mut positive := 0
    for (name, expected) in cases do
      let some ri := rows.findIdx? (·.sourceName == name) | throwError "missing required {name} row"
      let some row := rows[ri]? | throwError "missing row index"
      let some fi := functions.findIdx? (fun f => f.sourceId == row.sourceId &&
          f.name == row.name && f.sourceSignature == row.sourceSignature)
        | throwError "missing required {name} function"
      let some f := functions[fi]? | throwError "function index"
      let some ledger := capture.result.2.find? (fun r => J.id? r.entry == some row.sourceId)
        | throwError "missing actual {name} ledger"
      let some origins := admittedSpecOriginsV1? fixture sourcePath.getString bytes row.sourceId
        | throwError "source admission refused"
      let some locations := origins.result.origins | throwError "required source layout unavailable"
      let slots := f.specClauses.zipIdx.filter (·.1.1 == "ensures")
      unless slots.length == expected.length do throwError "required clause multiplicities changed"
      let some actual := results.toList.find? (fun r =>
        (r.getObjValAs? Int "sourceId").toOption == some row.sourceId &&
        (r.getObjValAs? String "status").toOption == some "refuted")
        | throwError "missing actual {name} full-goal refutation"
      let witness ← Lean.ofExcept (actual.getObjVal? "counterexample")
      let some retained ← retainedCounterexampleMetadataV1? N.getId ri fixture sourcePath.getString bytes witness
        | throwError "missing same-candidate ingress"
      for (((_, ci), shouldFail), ensuresOrdinal) in (slots.zip expected).zipIdx do
        let some (_, rawOrdinal) := ledger.canonicalOrdinals[ci]? | throwError "canonical mapping missing"
        let some location := locations[rawOrdinal]? | throwError "source mapping missing"
        let before := SMap.foldStage2 (fun (count : Nat) _ _ => count + 1) 0 (← getEnv).constants
        let metadata ← checkedRetainedPostSlotV1? N.getId ri fi ci fixture sourcePath.getString bytes location.span witness
        ordered := ordered ++ [Json.mkObj [("function", toJson name), ("ensuresOrdinal", toJson ensuresOrdinal),
          ("rawOrdinal", toJson rawOrdinal), ("expectedFailure", toJson shouldFail),
          ("sourceSha256", toJson origins.sourceSha256),
          ("certificateDeclaration", toJson retained.certificateDeclaration.toString),
          ("metadata", metadata.getD Json.null)]]
        IO.FS.writeFile output.getString (Json.pretty (toJson ordered))
        if metadata.isNone then
          let after := SMap.foldStage2 (fun (count : Nat) _ _ => count + 1) 0 (← getEnv).constants
          unless before == after do throwError "rejected publication retained auxiliary declarations"
        unless metadata.isSome == shouldFail do throwError "selected clause mismatch {name}/{ensuresOrdinal}: expected failure={shouldFail}"
        if let some metadata := metadata then
          positive := positive + 1
          let emittedOrdinal ← Lean.ofExcept (metadata.getObjValAs? Nat "ensuresOrdinal")
          let emittedRaw ← Lean.ofExcept (metadata.getObjValAs? Nat "rawClauseOrdinal")
          unless emittedOrdinal == ensuresOrdinal && emittedRaw == rawOrdinal do throwError "wrong emitted identity"
          let certificates ← Lean.ofExcept (metadata.getObjValAs? (Array Json) "certificates")
          if (metadata.getObjVal? "span").isOk || (metadata.getObjVal? "certified").isOk then
            throwError "numeric-only evidence published a certified source location"
          unless certificates.size == 11 do throwError "missing actual certificates"
          let some failure := certificates[4]? | throwError "missing failure certificate"
          let declaration ← Lean.ofExcept ((failure.getObjValAs? String "declaration").mapError (fun e => m!"{e}"))
          liftTermElabM do
            let info ← getConstInfo declaration.toName
            let (``Eq, eqArgs) := info.type.getAppFnArgs | throwError "failure is not an equality"
            unless eqArgs.size == 3 && eqArgs[2]! == mkConst ``Bool.true do throwError "wrong failure equality"
            let (``selectedEnsuresFailsV1, inputs) := eqArgs[1]!.getAppFnArgs
              | throwError "wrong selected typed predicate"
            unless inputs.size == 6 && inputs[0]! == retained.candidate.contract &&
                inputs[1]! == toExpr row.name && inputs[2]! == toExpr ensuresOrdinal && inputs[3]! == retained.candidate.domain && inputs[4]! == retained.candidate.values &&
                inputs[5]! == retained.candidate.state do throwError "certificate changed retained inputs"
          let some semantic := certificates[5]? | throwError "missing semantic witness certificate"
          let semanticName ← Lean.ofExcept ((semantic.getObjValAs? String "declaration").mapError (fun e => m!"{e}"))
          liftTermElabM do
            let info ← getConstInfo semanticName.toName
            let (``IndexedSpecPostFailureV1, inputs) := info.type.getAppFnArgs
              | throwError "missing actual semantic typed path witness"
            unless inputs.size == 6 && inputs[0]! == retained.candidate.contract &&
                inputs[1]! == toExpr row.name && inputs[2]! == toExpr ensuresOrdinal &&
                inputs[3]! == retained.candidate.domain && inputs[4]! == retained.candidate.values &&
                inputs[5]! == retained.candidate.state do throwError "semantic witness changed retained inputs"
          let some named := certificates[10]? | throwError "missing named-clause semantic certificate"
          let namedName ← Lean.ofExcept ((named.getObjValAs? String "declaration").mapError (fun e => m!"{e}"))
          liftTermElabM do
            let info ← getConstInfo namedName.toName
            let (``NamedSpecPostFailureV1, inputs) := info.type.getAppFnArgs
              | throwError "missing named-clause false-state witness"
            unless inputs.size == 7 && inputs[0]! == retained.candidate.contract &&
                inputs[1]! == toExpr row.name && inputs[2]! == toExpr ensuresOrdinal &&
                inputs[3]! == retained.candidate.domain && inputs[4]! == retained.candidate.values &&
                inputs[5]! == retained.candidate.state do throwError "named witness changed original inputs"
          let some matched := certificates[9]? | throwError "missing exact slot-match certificate"
          let matchedName ← Lean.ofExcept ((matched.getObjValAs? String "declaration").mapError (fun e => m!"{e}"))
          liftTermElabM do
            let (``NamedSpecPostFailureV1, namedInputs) := (← getConstInfo namedName.toName).type.getAppFnArgs
              | throwError "wrong named witness"
            let (``IndexedSpecPostMatchesV1, matchedInputs) := (← getConstInfo matchedName.toName).type.getAppFnArgs
              | throwError "wrong slot-match witness"
            unless matchedInputs.size == 6 && namedInputs.size == 7 &&
                matchedInputs[0]! == namedInputs[0]! && matchedInputs[1]! == namedInputs[1]! &&
                matchedInputs[2]! == namedInputs[2]! && matchedInputs[3]! == namedInputs[4]! &&
                matchedInputs[4]! == namedInputs[5]! && matchedInputs[5]! == namedInputs[6]! do
              throwError "named witness changed the exact matched typed clause family"
          for certificate in certificates.toList do
            let name ← Lean.ofExcept (certificate.getObjValAs? String "declaration")
            let actualAxioms ← liftTermElabM (collectAxioms name.toName)
            unless actualAxioms.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
              throwError "nonstandard actual certificate axiom"
          for badSpan in [ {location.span with start := location.span.start + 1} ] do
            if (← checkedRetainedPostSlotV1? N.getId ri fi ci fixture sourcePath.getString bytes badSpan witness).isSome then
              throwError "wrong span published"
          if (← checkedRetainedPostSlotV1? N.getId ri fi ci fixture sourcePath.getString (bytes.push 32) location.span witness).isSome then
            throwError "stale source published"
          if (← checkedRetainedPostSlotV1? N.getId ri fi ci fixture (sourcePath.getString ++ ".other") bytes location.span witness).isSome then
            throwError "foreign source published"
          if (← checkedRetainedPostSlotV1? N.getId ri fi ci fixture sourcePath.getString bytes location.span foreignWitness).isSome then
            throwError "foreign certificate published"
          if (← checkedRetainedPostSlotV1? foreignN.getId ri fi ci fixture sourcePath.getString bytes location.span witness).isSome then
            throwError "foreign namespace published"
          if (← checkedRetainedPostSlotV1? N.getId ri fi ci Json.null sourcePath.getString bytes location.span witness).isSome then
            throwError "malformed fixture published"
          for other in locations do
            if other.ordinal != rawOrdinal && (← checkedRetainedPostSlotV1? N.getId ri fi ci fixture
                sourcePath.getString bytes other.span witness).isSome then throwError "wrong ordinal span published"
        logInfo m!"POST_SLOT {name} ensures={ensuresOrdinal} raw={rawOrdinal} certified={metadata.isSome}"
    unless positive == requiredPositive && ordered.length == requiredTotal do throwError "missing required selected post cases"
    IO.FS.writeFile output.getString (Json.pretty (toJson ordered))
    logInfo "POST_SLOT_CONTROLS_PASS:fixed required multiplicities;original inputs;typed named-clause equality and semantic failure;publication withheld during validation"

/-- Guards arbitrary-slot attribution independently of the unresolved partial
source compiler. These four slots belong to the actual retained mixed formula;
the split count is explicit and is not a certified source-clause count. -/
syntax "#retained_formula_slot_controls " ident str str str str : command

elab_rules : command
  | `(#retained_formula_slot_controls $N:ident $astPath:str $sourcePath:str $reportPath:str $output:str) => do
    unless N.getId == `SelectedCases do throwError "unsupported fixed retained-formula fixture"
    let fixture ← Lean.ofExcept (Json.parse (← IO.FS.readFile astPath.getString))
    let bytes ← IO.FS.readBinFile sourcePath.getString
    let report ← Lean.ofExcept (Json.parse (← IO.FS.readFile reportPath.getString))
    let results ← ofExcept report.getArr?
    let rows ← reportRows N.getId
    let some ri := rows.findIdx? (·.sourceName == "mixed") | throwError "missing mixed source row"
    let some row := rows[ri]? | throwError "missing row"
    let some result := results.toList.find? (fun r =>
      (r.getObjValAs? Int "sourceId").toOption == some row.sourceId &&
      (r.getObjValAs? String "status").toOption == some "refuted")
      | throwError "missing actual retained mixed refutation"
    let witness ← Lean.ofExcept (result.getObjVal? "counterexample")
    let some retained ← retainedCounterexampleMetadataV1? N.getId ri fixture sourcePath.getString bytes witness
      | throwError "retained candidate unavailable"
    let mut records : List Json := []
    for (expected, slot) in [false, false, true, false].zipIdx do
      records := records ++ [Json.mkObj [("slot", toJson slot), ("expectedFailure", toJson expected),
        ("status", toJson "checking"), ("sourceAttribution", toJson "unavailable")]]
      IO.FS.writeFile output.getString (Json.pretty (toJson records))
      let certificates ← liftTermElabM do
        let candidate := retained.candidate
        let predicate ← mkAppM ``Solidity.Fml.retainedPostFailsV1 #[candidate.domain, toExpr (4 : Nat),
          toExpr slot, candidate.values, candidate.state, candidate.formula]
        let checkedType ← mkEq predicate (toExpr expected)
        let checked ← mkDecideProof checkedType
        let checkedName ← mkFreshUserName (N.getId ++ `retainedSlotCheckV1)
        let options ← getOptions
        let limit := maxHeartbeats.get options
        let limit := if limit == 0 then 100000 else min limit 100000
        withOptions (fun _ => debug.skipKernelTC.set (maxHeartbeats.set options limit) false) do
          addDecl (.thmDecl { name := checkedName, levelParams := [], type := checkedType, value := checked })
          let mut names := [checkedName]
          if expected then
            let semantic ← mkAppM ``Solidity.Fml.retainedFailedPostSlotV1_of_true #[candidate.domain,
              toExpr (4 : Nat), toExpr slot, candidate.values, candidate.state, candidate.formula, mkConst checkedName]
            let name ← mkFreshUserName (N.getId ++ `retainedSlotSemanticV1)
            addDecl (.thmDecl { name, levelParams := [], type := ← inferType semantic, value := semantic })
            names := names ++ [name]
          names.mapM fun name => do
            let axioms ← collectAxioms name
            unless axioms.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
              throwError "nonstandard retained-slot certificate axiom"
            pure (Json.mkObj [("declaration", toJson name.toString),
              ("axioms", toJson (axioms.map Name.toString))])
      records := records.dropLast ++ [Json.mkObj [("slot", toJson slot), ("expectedFailure", toJson expected),
        ("status", toJson "kernel-checked"), ("sourceAttribution", toJson "unavailable"),
        ("sameRetainedCertificate", toJson retained.certificateDeclaration.toString),
        ("certificates", toJson certificates)]]
      IO.FS.writeFile output.getString (Json.pretty (toJson records))
    unless records.length == 4 do throwError "missing fixed retained-formula observations"
    logInfo "RETAINED_FORMULA_SLOTS_PASS:four checked slots;one actual false slot;three other slots did not certify failure;source attribution unavailable"
