import Solidity.Frontend.CounterexampleMetadataV1

/-!
# Source-origin and retained-certificate controls

Guards duplicate-clause wrong-span/ordinal attribution and second-search
metadata substitution. The command is run after a genuine pinned-compiler
import and the existing counterexample command in the same Lean process.
It checks source metadata computation and kernel-retained proof ownership
separately; it does not claim canonical failed-postcondition correspondence.
-/

open Lean Elab Command
open Solidity.Frontend

syntax "#spec_origins_controls " ident str str str : command

elab_rules : command
  | `(#spec_origins_controls $N:ident $astPath:str $sourcePath:str $reportPath:str) => do
    let fixtureText ← IO.FS.readFile astPath.getString
    let .ok fixture := Json.parse fixtureText | throwError "invalid native fixture"
    let bytes ← IO.FS.readBinFile sourcePath.getString
    let .ok report := Json.parse (← IO.FS.readFile reportPath.getString)
      | throwError "invalid native verification output"
    let .ok results := report.getArr? | throwError "expected actual result rows"
    let rows ← reportRows N.getId
    let some index := rows.findIdx? (·.sourceName == "bad") | throwError "missing actual bad row"
    let some row := rows[index]? | throwError "bad row index"
    let some origin := admittedSpecOriginsV1? fixture sourcePath.getString bytes row.sourceId
      | throwError "actual admitted snapshot rejected"
    let some [first] := origin.result.origins | throwError "expected one actual source clause"
    unless first.clause.kind == "ensures" && first.clause.text == "false" do
      throwError "wrong actual source clause"
    let some actualSlice := String.fromUTF8? (bytes.extract first.span.start
        (first.span.start + first.span.length)) | throwError "invalid actual UTF8 span"
    unless actualSlice == "@custom:key ensures false" && first.span.file == 0 do
      throwError "actual byte span points at wrong native source text"
    unless origin.result.accepts 0 first.span do throwError "actual span refused"
    if origin.result.accepts 1 first.span then throwError "wrong ordinal accepted"
    if origin.result.accepts 0 {first.span with start := first.span.start + 1} then
      throwError "wrong span accepted"
    if (admittedSpecOriginsV1? fixture (sourcePath.getString ++ ".other") bytes row.sourceId).isSome then
      throwError "foreign source accepted"
    if (admittedSpecOriginsV1? fixture sourcePath.getString bytes (-999)).isSome then
      throwError "wrong declaration accepted"
    let changed := bytes.push 32
    if (admittedSpecOriginsV1? fixture sourcePath.getString changed row.sourceId).isSome then
      throwError "stale bytes accepted"
    for name in ["duplicate", "multiline", "terminated", "block"] do
      let some other := rows.find? (·.sourceName == name) | throwError "missing native control {name}"
      let some derived := admittedSpecOriginsV1? fixture sourcePath.getString bytes other.sourceId
        | throwError "native control admission failed {name}"
      if name == "block" then
        if derived.result.origins.isSome then throwError "unsupported block layout guessed"
      else
        let some locations := derived.result.origins | throwError "missing native origins {name}"
        if name == "duplicate" then
          let [a, b] := locations | throwError "duplicate count"
          unless a.clause.text == b.clause.text && a.span.start < b.span.start do
            throwError "duplicate identities collapsed"
          if derived.result.accepts 0 b.span || derived.result.accepts 1 a.span then
            throwError "duplicate span/ordinal substitution accepted"
        if name == "multiline" then
          let [a] := locations | throwError "multiline count"
          unless a.clause.text == "(true && false)" do throwError "multiline normalization differs"
          let some raw := String.fromUTF8? (bytes.extract a.span.start (a.span.start + a.span.length))
            | throwError "multiline UTF8 range"
          unless raw == "@custom:key ensures (true &&\r\n    /// false)" do
            throwError "multiline CRLF byte extent differs"
        if name == "terminated" && locations.length != 2 then throwError "non-key tag termination differs"
    let some result := results.toList.find? (fun r =>
      (r.getObjValAs? Int "sourceId").toOption == some row.sourceId)
      | throwError "missing actual verification result"
    let .ok witness := result.getObjVal? "counterexample" | throwError "no actual certificate"
    let some metadata ← retainedCounterexampleMetadataV1? N.getId index fixture
        sourcePath.getString bytes witness | throwError "retained candidate unavailable"
    unless metadata.row.legacy.sourceId == row.sourceId do throwError "wrong actual row"
    if (← retainedCounterexampleMetadataV1? N.getId index fixture sourcePath.getString changed witness).isSome then
      throwError "stale snapshot reached metadata"
    let wrongCertificate := witness.setObjVal! "certificateDeclaration" (toJson "unrelated.refuted")
    if (← retainedCounterexampleMetadataV1? N.getId index fixture sourcePath.getString bytes wrongCertificate).isSome then
      throwError "foreign certificate accepted"
    let uncertified := witness.setObjVal! "certified" (toJson false)
    if (← retainedCounterexampleMetadataV1? N.getId index fixture sourcePath.getString bytes uncertified).isSome then
      throwError "uncertified presentation accepted"
    -- Explicit adversarial fixture mutation, not a second compiler observation.
    let .ok ast := fixture.getObjVal? "ast" | throwError "primary AST"
    let .ok units := ast.getObjValAs? (Array Json) "nodes" | throwError "AST nodes"
    let some ci := units.toList.findIdx? (fun n => J.kind n == "ContractDefinition")
      | throwError "contract node"
    let contract := units[ci]!
    let .ok members := contract.getObjValAs? (Array Json) "nodes" | throwError "members"
    let some bi := members.toList.findIdx? (fun n => J.str? n "name" == some "bad")
      | throwError "bad AST owner"
    let some di := members.toList.findIdx? (fun n => J.str? n "name" == some "duplicate")
      | throwError "duplicate AST owner"
    let .ok otherDoc := members[di]!.getObjVal? "documentation" | throwError "other documentation"
    let changedMembers := members.set! bi (members[bi]!.setObjVal! "documentation" otherDoc)
    let changedContract := contract.setObjVal! "nodes" (toJson changedMembers)
    let changedAst := ast.setObjVal! "nodes" (toJson (units.set! ci changedContract))
    let changedFixture := fixture.setObjVal! "ast" changedAst
    unless (admittedSpecOriginsV1? changedFixture sourcePath.getString bytes row.sourceId).isSome do
      throwError "mutation did not exercise same-provenance admission boundary"
    if (← retainedCounterexampleMetadataV1? N.getId index changedFixture sourcePath.getString bytes witness).isSome then
      throwError "SAME_PROVENANCE_WRONG_AST_ACCEPTED"
    logInfo "SOURCE_ORIGIN_AND_RETAINED_CANDIDATE_ONLY: real clause/span; wrong span/ordinal/hash/owner/source/certificate refused; canonical attribution remains unproved"
