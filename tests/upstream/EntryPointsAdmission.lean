import Solidity.Frontend.SolcJson

/-! Malformed compiler-boundary controls. These deliberately alter metadata;
they are refusal tests, not alternative compiler observations. -/
open Lean Solidity.Frontend

private def put (j : Json) (key : String) (value : Json) : Json :=
  Json.mkObj ((key, value) :: ((j.getObj?.toOption.map (·.toList)).getD []).filter (·.1 != key))

private partial def modifyTree (f : Json → Json) : Json → Json
  | .obj fields => f (Json.mkObj (fields.toList.map fun (k, v) => (k, modifyTree f v)))
  | .arr values => .arr (values.map (modifyTree f))
  | other => f other

#eval do
  let fixture ← IO.ofExcept (Json.parse (← IO.FS.readFile "tests/solc/EntryPointsLeft.ast.json"))
  let ast ← IO.ofExcept (fixture.getObjVal? "ast")
  let provenance ← IO.ofExcept (Source.read fixture ast)
  let declarations := J.nodes ast
  let owner (name : String) : IO Json := do
    let some node := declarations.find? fun node => J.kind node == "ContractDefinition" && J.str? node "name" == some name
      | throw (IO.userError "missing owner")
    pure node
  let member (o : Json) (name : String) : IO Json := do
    let some node := (J.arrD o "nodes").find? (J.str? · "name" == some name)
      | throw (IO.userError "missing member")
    pure node
  let nominal ← owner "NominalGetters"
  let enum ← member nominal "Shade"
  let declarationNode ← member nominal "shade"
  let some id := J.id? enum | throw (IO.userError "missing enum identity")
  unless (publicGetterPlan [] declarations [] declarationNode "root" [(id, "E")]).isOk do
    throw (IO.userError "valid enum getter refused")
  for members in [#[], #[Json.mkObj [("name", .str "same")], Json.mkObj [("name", .str "same")]],
      Array.replicate 257 (Json.mkObj [("name", .str "oversized")])] do
    let invalid := declarations.map fun node => if J.id? node == some id then put node "members" (.arr members) else node
    unless !(publicGetterPlan [] invalid [] declarationNode "root" [(id, "E")]).isOk do
      throw (IO.userError "malformed enum getter admitted")
  unless !(publicGetterPlan [] declarations [] declarationNode "root").isOk do
    throw (IO.userError "missing native enum identity was guessed")
  let key ← member (← owner "NominalKeyDispatchRefusal") "values"
  let keyType ← IO.ofExcept ((J.get key "typeName").mapError Gap.msg)
  unless getterNominalSignature declarations (declarations.length + 1) keyType do
    throw (IO.userError "nominal contract key was erased")
  let base ← owner "ExternalBase"
  let target ← member base "target"
  let targetId := J.id? target
  let modified := modifyTree (fun node => if J.id? node == targetId then put node "functionSelector" (.str "fffffffff") else node) ast
  let c : SolcContract ← IO.ofExcept (readContract modified "RenamedExternal" [] true (scanSource := Admission.scan modified provenance))
  let some caller := c.funs.find? (fun (f : SolcFun) => f.sourceName == "positive")
    | throw (IO.userError "missing caller")
  match caller.body with
  | .error gap => unless gap.msg == s!"malformed functionSelector on declaration #{targetId.getD 0}" do
      throw (IO.userError s!"malformed selector refusal lost its cause: {gap.msg}")
  | .ok _ => throw (IO.userError "malformed inherited selector was admitted")
  let fallback := (J.arrD (← owner "FallbackBase") "nodes").find? fun node =>
    J.kind node == "FunctionDefinition" && J.str? node "kind" == some "fallback"
  let some fallbackId := fallback.bind J.id? | throw (IO.userError "missing fallback identity")
  let missing := modifyTree (fun node => if J.id? node == some fallbackId then put node "id" .null else node) ast
  for name in ["FallbackBase", "InheritedFallback"] do
    for modern in [false, true] do
      let scanner : Source.AdmissionRequest → Source.ScopeScan :=
        if modern then Admission.scan missing provenance else fun _ => default
      match readContract missing name [] true (scanSource := scanner) with
      | .error reason => unless reason == "solidity.selfPayment: selected payment entry has no declaration identity" do
          throw (IO.userError s!"wrong missing-handler refusal: {reason}")
      | .ok _ => throw (IO.userError "missing handler identity fell through to the oracle")
  IO.println "enum metadata, nominal key and inherited selector refusal controls passed"
