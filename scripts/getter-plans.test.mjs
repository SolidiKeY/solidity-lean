import {test} from 'node:test';
import {mkdtempSync, writeFileSync, rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join, resolve} from 'node:path';
import {execFileSync} from 'node:child_process';

// Exercise plans directly: no proof search or rebuilding in this regression.
test('getter plans preserve argument metadata, return order and empty-result refusal', () => {
  const dir = mkdtempSync(join(tmpdir(), 'solidity-getter-plan-'));
  try {
    const check = join(dir, 'Check.lean');
    const fixture = resolve('tests/solc/PublicGetters.ast.json');
    writeFileSync(check, `import Solidity.Frontend.SolcJson.Getters
open Lean Solidity.Frontend
#eval do
  let fixture ← IO.ofExcept (Json.parse (← IO.FS.readFile ${JSON.stringify(fixture)}))
  let ast ← IO.ofExcept (fixture.getObjVal? "ast")
  let declarations := J.nodes ast
  let some owner := declarations.find? (J.str? · "name" == some "PublicGetters")
    | throw (IO.userError "missing contract")
  let members := (J.arrD owner "nodes").toList
  let get (name : String) : IO Json := do
    let some member := members.find? (J.str? · "name" == some name)
      | throw (IO.userError "missing variable")
    pure member
  let plan (name : String) : IO GetterPlan := do
    let .ok plan := publicGetterPlan [] declarations [] (← get name) "root"
      | throw (IO.userError "unexpected getter refusal")
    pure plan
  let mapping ← plan "allowances"
  unless mapping.sourceParams == ["who", "kind"] &&
      mapping.abiParams == ["address", "uint16"] &&
      mapping.params.map Prod.snd == ["address", "uint16"] do
    throw (IO.userError "mapping argument metadata lost or reordered")
  let scalar ← plan "count"
  unless scalar.returnText == "root" && scalar.rets.map Prod.snd == ["uint32"] do
    throw (IO.userError "scalar return changed")
  let entry ← plan "entry"
  unless entry.returnText == "(root.«value», root.«live»)" &&
      entry.rets.map Prod.snd == ["uint32", "bool"] do
    throw (IO.userError s!"struct return order or omissions changed: {entry.returnText}, {repr entry.rets}")
  let indexed ← plan "sequences"
  unless indexed.sourceParams == ["key", ""] &&
      indexed.abiParams == ["uint256", "uint256"] && indexed.guards.length == 1 do
    throw (IO.userError "mapping/array traversal metadata changed")
  -- A struct containing only omitted members must not become return ().
  let some struct := declarations.find? (fun node =>
      J.kind node == "StructDefinition" && J.str? node "name" == some "Entry")
    | throw (IO.userError "missing struct")
  let omitted := (J.arrD struct "members").filter fun member =>
    (J.opt member "typeName").any fun type =>
      ["Mapping", "ArrayTypeName"].contains (J.kind type)
  unless omitted.size == 2 do throw (IO.userError "missing omitted members")
  let empty := Json.mkObj [("nodeType", .str "StructDefinition"),
    ("id", toJson (123456 : Nat)), ("members", .arr omitted)]
  let declaration := Json.mkObj [("id", toJson (123457 : Nat)),
    ("typeName", Json.mkObj [("nodeType", .str "UserDefinedTypeName"),
      ("referencedDeclaration", toJson (123456 : Nat))])]
  match publicGetterPlan [] [empty] [] declaration "root" with
  | .error (.unsupported reason _) =>
    unless reason == "a public getter with no returned members" do
      throw (IO.userError "wrong empty getter diagnostic")
  | _ => throw (IO.userError "empty getter admitted")
`);
    execFileSync('lake', ['--quiet', '--no-build', 'lean', check, '--', '--tstack=131072'],
      {stdio:'pipe', encoding:'utf8', timeout:60000});
  } finally {
    rmSync(dir, {recursive:true, force:true});
  }
});
