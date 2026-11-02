import Solidity.Frontend.SolcJson

/-! Paired compiler-source admission controls in both required pipelines.
Both address receiver types are valid Solidity. New handler registration is
bounded to source-payable receivers; the historical own-receive path is kept.
These are importer observations, not compiler/EVM equivalence proofs. -/
open Lean Solidity.Frontend

private def put (j : Json) (key : String) (value : Json) : Json :=
  Json.mkObj ((key, value) :: ((j.getObj?.toOption.map (·.toList)).getD []).filter (·.1 != key))

private partial def changePayableMetadata (f : Json → Json) : Json → Json
  | .obj fields =>
    let node := Json.mkObj (fields.toList.map fun (k, v) => (k, changePayableMetadata f v))
    if J.tyStr node == "address payable" then f node else node
  | .arr values => .arr (values.map (changePayableMetadata f))
  | other => other

#eval do
  for file in ["tests/solc/EntryPointsReceiverProfile.ast.json",
      "tests/solc/EntryPointsReceiverProfile.viaIR.ast.json"] do
    let fixture ← IO.ofExcept (Json.parse (← IO.FS.readFile file))
    let ast ← IO.ofExcept (fixture.getObjVal? "ast")
    let provenance ← IO.ofExcept (Source.read fixture ast)
    for modern in [false, true] do
      let scanner : Source.AdmissionRequest → Source.ScopeScan :=
        if modern then Admission.scan ast provenance else fun _ => default
      for name in ["ReceiverProfileInherited", "ReceiverProfileFallback", "ReceiverProfileOwn"] do
        let c : SolcContract ← IO.ofExcept (readContract ast name [] true (scanSource := scanner))
        for method in ["payableReceiver", "bareReceiver"] do
          let some f := c.funs.find? (fun (f : SolcFun) => f.sourceName == method)
            | throw (IO.userError s!"missing {name}.{method}")
          let refused := method == "bareReceiver" && name != "ReceiverProfileOwn"
          if refused then
            unless (f.sourceScope.diagnostic?.map (fun (issue : Source.Diagnostic) => issue.name)) == some `solidity.selfPayment do
              throw (IO.userError s!"lost named receiver refusal: {file}/{modern}/{name}.{method}")
          else
            unless f.sourceScope.diagnostic?.isNone && f.body.isOk do
              throw (IO.userError s!"supported receiver profile refused: {file}/{modern}/{name}.{method}")
      -- Contradictory and missing receiver metadata must not gain admission.
      for alter in [fun node => put node "typeDescriptions" .null,
          fun node => put node "typeDescriptions" (Json.mkObj [
            ("typeString", .str "address payable"), ("typeIdentifier", .str "t_address")]),
          fun node => put node "typeDescriptions" (Json.mkObj [
            ("typeString", .str "address payable"), ("typeIdentifier", toJson (1 : Nat))]),
          fun node => put node "typeDescriptions" (Json.mkObj [
            ("typeString", .str "address payable"), ("typeIdentifier", .null)])] do
        let changed := changePayableMetadata alter ast
        let scanner : Source.AdmissionRequest → Source.ScopeScan :=
          if modern then Admission.scan changed provenance else fun _ => default
        for name in ["ReceiverProfileInherited", "ReceiverProfileFallback"] do
          let c : SolcContract ← IO.ofExcept (readContract changed name [] true (scanSource := scanner))
          let some f := c.funs.find? (fun (f : SolcFun) => f.sourceName == "payableReceiver")
            | throw (IO.userError "missing altered receiver")
          unless (f.sourceScope.diagnostic?.map (fun (issue : Source.Diagnostic) => issue.name)) == some `solidity.selfPayment do
            throw (IO.userError "malformed receiver metadata bypassed the named refusal")
  IO.println "paired payable/bare/own receivers and malformed metadata passed in both pipelines and scanner modes"
