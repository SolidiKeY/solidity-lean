import Solidity.Frontend.ExecutableAst.Memory.Reader
import Solidity.Frontend.ExecutableAst.Shared.Intrinsic
import Solidity.Frontend.ExecutableAst.Shared.Compose
import Solidity.Frontend.Problems
import Solidity.Syntax.Splice
import Solidity.Semantics.Run

/-! Developer admission checks only. No runtime or calculus proof verdict is
inferred from successful decoding. The harness restores signed compiler builtin
IDs externally, and records both raw and normalized byte digests. -/
open Lean Solidity
namespace Solidity.Frontend.ExecutableAst.Memory.AdmissionTests
open Shared

private def contractNode (output : Json) : Except String Json := do
  let ast ← field (← field (← field output "sources") "Identity.sol") "ast"
  let nodes ← arr ast "nodes"
  let some c := nodes.find? (fun n => (node n).toOption == some "ContractDefinition")
    | throw "missing contract"
  return c

private def decode (reader : Reader) (output : Json) : Except String (Contract × FunDecl) := do
  let c ← contractNode output
  let C ← Shared.contract reader c
  let some f := (← arr c "nodes").find? (fun n => (node n).toOption == some "FunctionDefinition")
    | throw "missing function"
  let d := (← Shared.function reader f c.compress).2
  return ({ C with funs := [("identity", d)] }, d)

private def identityShape (body : List RawStmt) : Bool :=
  match body with
  | [.declMemory (.array (.named "int")) "m"
        (some (.newArr (.array (.named "int")) (.num 1))),
      .assign (.index (.name "m") (.num 0)) (.num 1),
      .assert (.binop .eqB (.index (.name "m") (.num 0)) (.num 1))] => true
  | _ => false

#eval do
  let root := "tests/directruntime-20261104/memory-references/"
  let rows ← IO.ofExcept (Json.parse (← IO.FS.readFile (root ++ "evidence/admission-inputs.json")))
  let rows ← IO.ofExcept rows.getArr?
  for (readerName, reader) in [("memory", Memory.reader), ("composed", Shared.executableReader)] do
    let mut accepted := 0
    let mut refused := 0
    let mut typedCount := 0
    let mut obligationsCount := 0
    let mut typeRefusals := 0
    let mut results := #[]
    for row in rows do
      let file ← IO.ofExcept (str row "path")
      let expected ← IO.ofExcept (row.getObjValAs? Bool "accept")
      let output ← IO.ofExcept (Json.parse (← IO.FS.readFile (root ++ file)))
      match decode reader output with
      | .ok (C, d) =>
        unless expected do throw (IO.userError s!"accepted malformed AST: {file}")
        if (← IO.ofExcept (str row "id")) == "identity" then
          unless identityShape d.body do throw (IO.userError "Identity raw constructor mismatch")
        accepted := accepted + 1
        let shouldType := (row.getObjValAs? Bool "typed").toOption.getD false
        -- Exercise A's published builder with the exact existing producer helpers.
        -- Formula construction is not proof closure or ordinary runtime acceptance.
        let box := (file.splitOn ".").contains "box"
        let built := Shared.obligation Solidity.Frontend.lowerBodyLoops
          (fun C Γ => Solidity.Frontend.Problem.callPre C Γ false [] false [] true)
          C "identity" false box
        match built with
        | .ok _ =>
          unless shouldType do throw (IO.userError s!"built incompatible obligation {file}")
          obligationsCount := obligationsCount + 1
        | .error reason =>
          if shouldType then throw (IO.userError s!"shared obligation rejection {file}: {reason}")
        match elabProgAtS.go C 0 d.body ([], RawStmt.maxIdxs d.body + 1) (source := true) with
        | .error (_, reason) =>
          if shouldType then throw (IO.userError s!"intrinsic type rejection {file}: {reason}")
          typeRefusals := typeRefusals + 1
          results := results.push (Json.mkObj [("input",toJson file),("stage",toJson "intrinsic-type-rejected"),("reason",toJson reason)])
        | .ok ⟨_, program⟩ =>
          unless shouldType do throw (IO.userError s!"intrinsically admitted incompatible initializer {file}")
          typedCount := typedCount + 1
          let halt := match Prog.run (State.init C) program with
            | .ok _ => "success"
            | .error .revert => "revert"
            | .error .panic => "panic"
            | .error _ => "other"
          let expectedHalt ← IO.ofExcept (str row "initialModelHalt")
          unless halt == expectedHalt do throw (IO.userError s!"model outcome {file}: {halt}, expected {expectedHalt}")
          results := results.push (Json.mkObj [("input",toJson file),("stage",toJson "initial-model-execution"),("halt",toJson halt)])
      | .error reason =>
        if expected then throw (IO.userError s!"refused valid fixture {file}: {reason}")
        refused := refused + 1
        results := results.push (Json.mkObj [("input",toJson file),("stage",toJson "decode-rejected"),("reason",toJson reason)])
    IO.FS.writeFile (root ++ (if readerName == "memory" then "evidence/model-results.json" else "evidence/model-results.composed.json")) (Json.pretty (Json.arr results))
    IO.println s!"PASS {readerName}: shared obligation construction: {obligationsCount} with existing producer callbacks (not proof closure)"
    IO.println s!"PASS {readerName}: intrinsic typing: {typedCount} admitted, {typeRefusals} incompatible initializers refused; initial-model outcomes checked (not universal validity)"
    IO.println s!"PASS {readerName}: admission: {accepted} accepted, {refused} malformed refused; Identity uses existing newArr/declMemory/index/assign/assert"
