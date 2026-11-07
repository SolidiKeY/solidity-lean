import Solidity.Source.LibraryTyping
import Solidity.Source.Eval
import Solidity.Source.Infer
import Solidity.Source.Elaborate
import Solidity.Source.SemanticsExamples
import Solidity.Lowering.P8.SourceAstUnit

/-! Guards the LibraryTry regression before delegated-entry admission:
standard Error payloads decode, malformed/foreign payloads refuse, qualified
library shadowing and wrong using types refuse, and both actual compiler JSON
inputs select the same library declarations. Both original units also elaborate and execute through the Source semantics.
No physical ABI, linked-library installation or compiler-origin adequacy is claimed. -/
namespace H125.LibraryTryControls
open Lean Solidity.Source
open Solidity.Lowering.P8.SourceAstUnit

#guard errorStringBytes (errorData []) == some []
#guard errorStringBytes (errorData [102, 97, 105, 108, 117, 114, 101]) ==
  some [102, 97, 105, 108, 117, 114, 101]
#guard errorStringBytes [] == none
#guard errorStringBytes (panicData .arithmetic) == none
#guard errorStringBytes ((errorData []).take 67) == none
#guard errorStringBytes (errorSelector ++ wordBytes (toWord (2^64))) == none
#guard errorStringBytes (errorSelector ++ wordBytes (toWord 32) ++
  wordBytes (toWord (2^64))) == none

/-- Actual full-unit conversion is used; no replacement hand-written body
is supplied. Only target lookup and argument typing are tested here. -/
def resolutionChecks (doc : Json) : Except String Unit := do
  let input ← unit 128 (← doc.getObjVal? "ast")
  let E := input.env
  let C : Ctx := { env := E, scope := some "C", locals := [("x", .int IntTy.u256), ("b", .bool)] }
  unless C.libraryQualifier (.ident "L") == some "L" do throw "qualified library missing"
  let qualified := C.libraryOverloads (.ident "L") "integer" [.int IntTy.u256, .bool]
  unless qualified.map (fun d => (d.scope, d.name)) == [(some "L", "integer")] do
    throw "qualified library overload changed"
  let usingCall := C.libraryOverloads (.ident "t") "stru"
    [.struct .storage ⟨some "L", "S"⟩, .bool]
  unless usingCall.map (fun d => (d.scope, d.name)) == [(some "L", "stru")] do
    throw "typed using target changed"
  unless (C.libraryOverloads (.ident "t") "stru" [.int IntTy.u256, .bool]).isEmpty do
    throw "wrong using receiver admitted"
  let shadow := { C with locals := ("L", .bool) :: C.locals }
  unless (shadow.libraryQualifier (.ident "L")).isNone do throw "local shadow ignored"
  unless (C.libraryOverloads (.ident "L") "absent" [.bool]).isEmpty do
    throw "unknown library member admitted"
  let args : Syn (.list .expr) := .cons (.ident "b") .nil
  match TypedArgs.infer C (C.libraryArgs (.ident "t") args) with
  | some ⟨types, _⟩ =>
    unless STy.sameList types [.struct .storage ⟨some "L", "S"⟩, .bool] do
      throw "using receiver arguments changed"
  | none => throw "using argument typing failed"

#eval do
  for file in ["tests/solc/LibraryTry.ast.json", "tests/solc/LibraryTryIR.ast.json"] do
    let raw ← IO.FS.readFile file
    match (do resolutionChecks (← Json.parse raw)) with
    | .ok () => IO.println s!"{file}: Error/qualified/using resolution controls passed"
    | .error why => throw (IO.userError why)


/-- Source-only execution uses the existing toy Fixed instance, the actual
elaborated program and a deployed C. No library address/link evidence is added. -/
def executeActual (el : Elaborated) : Except Halt (List Solidity.Roadmap.Outcome) :=
  let zero := SemanticsExamples.word 0
  let self := SemanticsExamples.addr 1
  let sender := SemanticsExamples.addr 7
  let G : Glob el.res.env := ⟨el.prog, el.res.pipeline, SemanticsExamples.toyFixed,
    fun _ => zero, fun _ _ => false, fun _ => .answer (.success []), zero⟩
  let action : Nat → EM el.res.env [] (List Solidity.Roadmap.Outcome) := fun n => do
    let deployed ← deploy G n "C" self sender zero []
    let mut outputs := [deployed]
    for (signature, argument) in [("f(bool)", 1), ("f(bool)", 0), ("g(bool)", 1), ("g(bool)", 0)] do
      let data := SemanticsExamples.selOf signature ++ wordBytes (toWord argument)
      let out ← runTx G n ⟨sender, self, zero, zero, data⟩
      outputs := outputs ++ [out]
    let some root := el.res.env.decls.find? (fun d =>
        d.scope == some "C" && d.name == "t" && d.kind == DeclKind.stateVar)
      | EM.halt (.stuck "missing storage root")
    let frame : Fr := { this := self, sender := sender, value := zero, static := true, contract := "C" }
    let stored ← readAt frame (root.path.go (.field 0)) (.int IntTy.u256)
    let some word := stored.word | EM.halt (.stuck "storage observation is not a word")
    return outputs ++ [.success (wordBytes word)]
  (runAt action (St.init el.res.env) 60).1

def resultString (value : Nat) (message : List UInt8) : List UInt8 :=
  wordBytes (toWord value) ++ wordBytes (toWord 64) ++
    wordBytes (toWord message.length) ++ pad32 message


/-- A supplementary Source-only stress input. Prepend t.x=13 to L.stru
and make it non-view; the original compiler fixture is never modified.
Its existing C.g writes 9 before the call, so a callee revert must restore 9.
No compiler provenance is claimed for this derived input. -/
def rollbackStress (doc : Json) : Except String Json := do
  let ast ← doc.getObjVal? "ast"
  let tops ← ast.getObjValAs? (Array Json) "nodes"
  let some contractNode := tops.find? (fun node =>
      (node.getObjValAs? String "name").toOption == some "C")
    | throw "missing C"
  let members ← contractNode.getObjValAs? (Array Json) "nodes"
  let some g := members.find? (fun node =>
      (node.getObjValAs? String "name").toOption == some "g")
    | throw "missing C.g"
  let statements ← (← g.getObjVal? "body").getObjValAs? (Array Json) "statements"
  let some original := statements[0]? | throw "missing caller assignment"
  let expression ← original.getObjVal? "expression"
  let rhs ← expression.getObjVal? "rightHandSide"
  let assignment := original.setObjVal! "expression"
    (expression.setObjVal! "rightHandSide" ((rhs.setObjVal! "value" (.str "13")).setObjVal! "hexValue" (.str "3133")))
  let changed ← tops.mapM fun node => do
    if (node.getObjValAs? String "name").toOption != some "L" then return node
    let children ← node.getObjValAs? (Array Json) "nodes"
    let children ← children.mapM fun child => do
      if (child.getObjValAs? String "name").toOption != some "stru" then return child
      let body ← child.getObjVal? "body"
      let stmts ← body.getObjValAs? (Array Json) "statements"
      return (child.setObjVal! "body" (body.setObjVal! "statements" (.arr (#[assignment] ++ stmts)))).setObjVal!
        "stateMutability" (.str "nonpayable")
    return node.setObjVal! "nodes" (.arr children)
  return doc.setObjVal! "ast" (ast.setObjVal! "nodes" (.arr changed))

#eval do
  for (file, pipeline) in [("tests/solc/LibraryTry.ast.json", Solidity.Roadmap.Pipeline.legacy),
      ("tests/solc/LibraryTryIR.ast.json", Solidity.Roadmap.Pipeline.viaIR)] do
    let raw ← IO.FS.readFile file
    let .ok doc := Json.parse raw | throw (IO.userError "invalid fixture JSON")
    let .ok input := (do unit 128 (← doc.getObjVal? "ast"))
      | throw (IO.userError "actual unit conversion failed")
    let resolved := resolveUnit { pipeline := pipeline } input
    for d in resolved.env.decls do
      if d.hasBody then
        unless (elabBody resolved.env d).isSome do
          throw (IO.userError s!"actual body failed: {d.scope.getD ""}.{d.name}")
    let some el := elaborate resolved | throw (IO.userError "actual whole unit did not elaborate")
    let actual := executeActual el
    let failure : List UInt8 := [102, 97, 105, 108, 117, 114, 101]
    let expected : List Solidity.Roadmap.Outcome := [
      .success [], .success (resultString 8 []), .success (resultString 18 failure),
      .success (resultString 9 []), .success (resultString 19 failure), .success (wordBytes (toWord 9))]
    match actual with
    | .error why => throw (IO.userError s!"{file}: Source halted: {repr why}")
    | .ok outputs =>
      unless outputs == expected do throw (IO.userError s!"{file}: Source execution mismatch: {repr outputs}")
    IO.println s!"{file}: all actual bodies elaborate; f/g success and Error(string) Source executions passed"
    let .ok stress := rollbackStress doc | throw (IO.userError "stress transformation failed")
    let .ok stressUnit := (do unit 128 (← stress.getObjVal? "ast"))
      | throw (IO.userError "stress unit conversion failed")
    let some stressEl := elaborate (resolveUnit { pipeline := pipeline } stressUnit)
      | throw (IO.userError "stress unit did not elaborate")
    let expectedStress : List Solidity.Roadmap.Outcome := [
      .success [], .success (resultString 8 []), .success (resultString 18 failure),
      .success (resultString 13 []), .success (resultString 19 failure), .success (wordBytes (toWord 9))]
    match executeActual stressEl with
    | .error why => throw (IO.userError s!"stress Source halted: {repr why}")
    | .ok outputs => unless outputs == expectedStress do throw (IO.userError "callee storage rollback failed")
    IO.println s!"{file}: derived Source-only callee-write/revert restores caller storage"



-- Exercise the actual evaluator hook, including the zero-horizon prefix.
#eval do
  let G := SemanticsExamples.G0 .legacy
  let F := SemanticsExamples.F0
  let expression : RExpr SemanticsExamples.E0 [.bytes .calldata] (.bytes .calldata) := .local .here
  let locals : Locals SemanticsExamples.E0.layout [.bytes .calldata] := .cons (.cdRef rfl 4 7) .nil
  let initial := (locals, St.init SemanticsExamples.E0)
  let (refused, _) := (evalE G F 4 expression (calldataKnown := false)).run initial
  match refused with
  | .error (.stuck message) =>
    unless message == "unsupported calldata observation" do throw (IO.userError "wrong calldata refusal")
  | _ => throw (IO.userError "unavailable calldata observation was not refused")
  let (zeroResult, _) := (evalE G F 0 expression (calldataKnown := false)).run initial
  match zeroResult with
  | .error .timeout => pure ()
  | _ => throw (IO.userError "zero-horizon prefix changed")
  IO.println "actual evaluator: unavailable calldata refuses; zero horizon remains timeout"

/-- info: 'Solidity.Source.withLibraryCalldata_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms withLibraryCalldata_known
/-- info: 'Solidity.Source.withLibraryCalldata_unavailable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms withLibraryCalldata_unavailable
/-- info: 'Solidity.Source.withLibraryCalldata_noncalldata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms withLibraryCalldata_noncalldata
/-- info: 'Solidity.Source.errorStringBytes_wrongSelector' depends on axioms: [propext] -/
#guard_msgs in
#print axioms errorStringBytes_wrongSelector
/-- info: 'Solidity.Source.errorStringBytes_of_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms errorStringBytes_of_decode
end H125.LibraryTryControls
