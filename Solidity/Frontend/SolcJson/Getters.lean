import Solidity.Frontend.SolcJson.Body
import Solidity.Keccak

/-!
# Source ABI identities and public getter plans

The compiler JSON is an input format. A getter plan prints ordinary source
members, then the existing elaborator checks their intrinsic types and
inlines them through the ordinary self-call path. It introduces no alternate
statement, state or return-value representation. Reference-valued results
are refused until the external return interface supports them.
-/

namespace Solidity.Frontend
open Lean (Json)

/-- Bounded freshness for generated callable and local names. Every rejected
candidate belongs to `taken`; one more candidate than its length suffices. -/
def freshSourceName (taken : List String) (base : String) : String := Id.run do
  let mut name := base
  for _ in [:taken.length + 1] do
    if !taken.contains name then return name
    name := name ++ "_"
  return name

/-- ABI type spelling before the importer erases nominal source types.
Recursive or unresolved shapes return `none`; no generated alias is hashed. -/
def sourceAbiType (declarations : List Json) : Nat → Json → Option String
  | 0, _ => none
  | fuel + 1, node => do
    match J.kind node with
    | "ElementaryTypeName" =>
      let name ← J.str? node "name"
      if name == "uint" || name == "uint256" then pure "uint256"
      else if name == "int" || name == "int256" then pure "int256"
      else if ["address", "address payable"].contains name then pure "address"
      else if ["bool", "bytes", "string"].contains name ||
          (narrowTy? name).isSome || (bytesTy? name).isSome then pure name
      else none
    | "ArrayTypeName" =>
      let base ← sourceAbiType declarations fuel (← J.opt node "baseType")
      match J.opt node "length" with
      | none => pure (base ++ "[]")
      | some n =>
        let length ← (solcArrayLength? node).orElse fun _ =>
          (constVal n).bind fun q => do
            let value ← q.int?
            guard (0 ≤ value)
            pure value.toNat
        pure s!"{base}[{length}]"
    | "UserDefinedTypeName" =>
      let id ← (J.ref? node).orElse fun _ => (J.opt node "pathNode").bind J.ref?
      let declaration ← declarations.find? (J.id? · == some id)
      match J.kind declaration with
      | "ContractDefinition" => pure "address"
      | "EnumDefinition" => pure "uint8"
      | "UserDefinedValueTypeDefinition" =>
        sourceAbiType declarations fuel (← J.opt declaration "underlyingType")
      | "StructDefinition" =>
        let members ← (J.arrD declaration "members").toList.mapM fun member => do
          sourceAbiType declarations fuel (← J.opt member "typeName")
        pure s!"({",".intercalate members})"
      | _ => none
    | "FunctionTypeName" =>
      if J.str? node "visibility" == some "external" then pure "function" else none
    | _ => none

/-- Canonical ordinary function identity, resolved from declaration types. -/
def sourceAbiSignature (declarations : List Json) (node : Json) : Option String := do
  let name ← J.str? node "name"
  let parameters ← (J.opt node "parameters").bind (J.arr? · "parameters")
  let types ← parameters.toList.mapM fun p => do
    sourceAbiType declarations (declarations.length + (J.nodes node).length + 1)
      (← J.opt p "typeName")
  pure s!"{name}({",".intercalate types})"

/-- Imported ordinary/special functions retain their role even when a legacy
fixture omits a selector. An exact canonical signature is the only fallback. -/
def sourceFunction (declarations : List Json) (node : Json)
    (selection : SourceSelection) (helper : Bool) : Except Gap SourceFunction := do
  let selector ← if (J.opt node "functionSelector").isSome then
      pure (some (← declarationSelector node "functionSelector" 4))
    else pure none
  let visibility := (J.str? node "visibility").getD "internal"
  let callable := match (J.str? node "kind").getD "function" with
    | "constructor" => SourceCallable.constructor
    | "receive" => .receive selection
    | "fallback" => .fallback selection
    | _ =>
      if helper || J.str? node "kind" == some "freeFunction" then .local .freeFn
      else if visibility == "public" then .abi .publicFn selection selector
      else if visibility == "external" then .abi .externalFn selection selector
      else .local (if visibility == "private" then .privateFn else .internalFn)
  let mutability := match J.str? node "stateMutability" with
    | some "pure" => SourceMutability.pureFn
    | some "view" => .viewFn
    | some "payable" => .payable
    | _ => .nonpayable
  pure {
    declaration := J.id? node
    name := (J.str? node "name").getD ""
    signature := sourceAbiSignature declarations node
    mutability
    callable }

/-- One getter argument, retaining its generated binding, source key name
and unerased ABI type together. -/
structure GetterInput where
  name : String
  type : String
  sourceName : String
  abiType : String
  deriving Inhabited

/-- A returned binding and the expression which supplies it. -/
structure GetterOutput where
  name : String
  type : String
  value : String
  deriving Inhabited

/-- A completed getter always returns at least one value. Input metadata and
output expressions cannot get out of step with their generated bindings. -/
structure GetterPlan where
  inputs : List GetterInput := []
  first : GetterOutput
  rest : List GetterOutput := []
  /-- Public getter bounds fail with empty revert data, before the ordinary read. -/
  guards : List String := []
  deriving Inhabited

def GetterPlan.params (plan : GetterPlan) : List (String × String) :=
  plan.inputs.map fun input => (input.name, input.type)

def GetterPlan.sourceParams (plan : GetterPlan) : List String :=
  plan.inputs.map (·.sourceName)

def GetterPlan.abiParams (plan : GetterPlan) : List String :=
  plan.inputs.map (·.abiType)

def GetterPlan.rets (plan : GetterPlan) : List (String × String) :=
  (plan.first :: plan.rest).map fun output => (output.name, output.type)

def GetterPlan.returnText (plan : GetterPlan) : String :=
  match plan.rest with
  | [] => plan.first.value
  | _ :: _ => s!"({", ".intercalate ((plan.first :: plan.rest).map (·.value))})"

/-- Traversal has collected arguments and bounds, but has no result yet. -/
private structure GetterPath where
  inputs : List GetterInput := []
  guards : List String := []

/-- Elementary and primitive UDVT inputs/results. Bytes/string
are references and must not be silently omitted from a struct getter. -/
private def getterValueType (S : Structs) (declarations : List Json) (node : Json) : Except Gap String := do
  let node ← if J.kind node == "UserDefinedTypeName" then do
      let some id := J.typeRef? node
        | throw (.unsupported "a public getter value type without declaration identity")
      let some declaration := declarations.find? (J.id? · == some id)
        | throw (.unsupported "a public getter value type declaration is missing")
      unless J.kind declaration == "UserDefinedValueTypeDefinition" do
        throw (.unsupported "public getter needs a nominal or reference-valued ABI return/input")
      J.get declaration "underlyingType"
    else pure node
  unless J.kind node == "ElementaryTypeName" do
    throw (.unsupported "public getter needs a nominal or reference-valued ABI return/input")
  unless (J.typeRef? node).isNone do
    throw (.unsupported "an elementary getter type carries a nominal declaration reference")
  let type ← tyText S node
  unless (PrimTy.ofName? type).isSome || (narrowTy? type).isSome ||
      (bytesTy? type).isSome || type == "address payable" do
    throw (.unsupported "public getter needs reference-valued ABI returns/inputs")
  pure type

private def getterTerminal (S : Structs) (declarations : List Json) (taken : List String) (id : Int)
    (path : GetterPath) (values : List (Json × String)) : Except Gap GetterPlan := do
  let mut outputs : List GetterOutput := []
  let mut taken := taken
  for (typeNode, value) in values do
    let type ← getterValueType S declarations typeNode
    let name := freshSourceName taken s!"solcGetterReturn{id}_{outputs.length}"
    taken := name :: taken
    outputs := outputs ++ [{ name, type, value }]
  let first :: rest := outputs | throw (.unsupported "a public getter with no returned members")
  pure { inputs := path.inputs, first, rest, guards := path.guards }

private def getterWalk (S : Structs) (declarations : List Json) (id : Int) :
    Nat → List String → GetterPath → Json → String → Except Gap GetterPlan
  | 0, _, _, _, _ => throw (.unsupported "public getter type traversal exceeded its bound")
  | fuel + 1, taken, plan, node, path => do
    if J.kind node == "Mapping" || J.kind node == "ArrayTypeName" then
      let mapping := J.kind node == "Mapping"
      let typeNode ← if mapping then J.get node "keyType" else
        pure (Json.mkObj [("nodeType", .str "ElementaryTypeName"), ("name", .str "uint256")])
      -- An enum key has the canonical uint8 ABI, with a separate membership
      -- guard. Width alone must not admit unnamed enum values.
      let enumSize : Option Nat := do
        guard (J.kind typeNode == "UserDefinedTypeName")
        let id ← J.typeRef? typeNode
        let declaration ← declarations.find? (J.id? · == some id)
        guard (J.kind declaration == "EnumDefinition")
        let members ← J.arr? declaration "members"
        guard (!members.isEmpty && members.size ≤ 256)
        pure members.size
      let type ← if enumSize.isSome then pure "uint8" else getterValueType S declarations typeNode
      let some abi := sourceAbiType declarations (declarations.length + 1) typeNode
        | throw (.unsupported "a public getter key without its canonical ABI type")
      let name := freshSourceName taken s!"solcGetterArg{id}_{plan.inputs.length}"
      let input := identText name
      let key := if type == "bool" then s!"({input} ? 1 : 0)" else input
      let sourceName := if mapping then (J.str? node "keyName").getD "" else ""
      let guards := if mapping then plan.guards else
        plan.guards ++ [s!"require({input} < {path}.length)"]
      let guards := match enumSize with
        | some size => guards ++ [s!"require({input} < {size})"]
        | none => guards
      let plan := { plan with
        guards
        inputs := plan.inputs ++ [{ name, type, sourceName, abiType := abi }] }
      let next ← J.get node (if mapping then "valueType" else "baseType")
      getterWalk S declarations id fuel (name :: taken) plan next s!"{path}[{key}]"
    else if J.kind node == "UserDefinedTypeName" then
      let some ref := (J.ref? node).orElse fun _ => (J.opt node "pathNode").bind J.ref?
        | throw (.unsupported "a public getter result without declaration identity")
      let some declaration := declarations.find? (J.id? · == some ref)
        | throw (.unsupported "a public getter result declaration is missing")
      if J.kind declaration != "StructDefinition" then
        return ← getterTerminal S declarations taken id plan [(node, path)]
      let mut values := []
      for member in (J.arrD declaration "members").toList do
        let typeNode ← J.get member "typeName"
        -- Solc omits these two kinds only. In particular bytes/string stay,
        -- and cause an explicit unsupported result in getterTerminal.
        if ["Mapping", "ArrayTypeName"].contains (J.kind typeNode) then continue
        let name ← J.str member "name"
        values := values ++ [(typeNode, s!"{path}.{identText name}")]
      getterTerminal S declarations taken id plan values
    else getterTerminal S declarations taken id plan [(node, path)]

/-- Consume mapping keys and array indexes; keep a terminal value or exactly
solc's non-array/non-mapping struct fields, in declaration order. -/
def publicGetterPlan (S : Structs) (declarations : List Json) (taken : List String)
    (declarationNode : Json) (root : String) : Except Gap GetterPlan := do
  let some id := J.id? declarationNode | throw (.unsupported "public getter declaration has no identity")
  let typeNode ← J.get declarationNode "typeName"
  getterWalk S declarations id ((J.nodes typeNode).length + declarations.length + 1)
    taken {} typeNode root

/-- Compiler selectors are validated. Legacy fixtures may reconstruct one
from the exact, unerased getter signature; truncation is never a fallback. -/
def publicGetterIdentity (declarationNode : Json) (plan : GetterPlan) : Except Gap SourceFunction := do
  let name ← J.str declarationNode "name"
  let signature := s!"{name}({",".intercalate plan.abiParams})"
  let selector ← if (J.opt declarationNode "functionSelector").isSome then
      declarationSelector declarationNode "functionSelector" 4
    else do
      let n := Keccak.selector signature
      if h : n < 2 ^ 32 then pure ⟨n, h⟩
      else throw (.unsupported "a getter selector outside four bytes")
  pure {
    declaration := J.id? declarationNode
    name
    signature := some signature
    mutability := .viewFn
    callable := .getter selector }

end Solidity.Frontend
