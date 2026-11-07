import Solidity.Frontend.ExecutableAst.ControlTuple.Adapter
import Solidity.Frontend.ExecutableAst.Shared.Compose
import Solidity.Frontend.ExecutableAst.Shared.Intrinsic
import Solidity.Frontend.Testing

/-! Relative AST-to-obligation controls over the published Shared builder.
Both the standalone packet and published canonical composed reader use
the existing plain producer helpers. All original controls run for each. These are
trusted-verifier checks, not new kernel certificates or Source adequacy proofs.
Guards the primitive-return repair: returnGuard now proves through the shared
builder; reference input refusals remain. No verifier boundary is modified. -/
open Lean Solidity Solidity.Frontend
open Solidity.Frontend.ExecutableAst

private def producerPre : Shared.PlainEntryPre :=
  fun C Γ => Problem.callPre C Γ false [] false [] true

run_elab do
  let fixture ← Lean.ofExcept (Json.parse (← IO.FS.readFile
    "tests/directruntime-20261104/control-tuples/Obligations.ast.json"))
  let ast ← Lean.ofExcept (fixture.getObjVal? "ast")
  let nodes ← Lean.ofExcept (ast.getObjValAs? (Array Json) "nodes")
  let some source := nodes.find? (fun j => (j.getObjValAs? String "name").toOption == some "ControlTupleObligations")
    | throwError "missing obligation fixture contract"
  for (readerName, reader) in [("standalone", ControlTuple.reader),
      ("composed", Shared.executableReader)] do
    logInfo m!"READER_CHECK {readerName}"
    let base ← Lean.ofExcept (Shared.contract reader source)
    let nodes ← Lean.ofExcept (source.getObjValAs? (Array Json) "nodes")
    for (name, expectedBox, expectedDiamond) in [
        ("goodDo", "proved", "proved"), ("badDo", "refuted", "refuted"),
        ("zeroWhile", "proved", "proved"), ("continues", "proved", "proved"),
        ("breaks", "proved", "proved"), ("early", "proved", "proved"),
        ("tupleSwap", "proved", "proved"), ("repeat", "proved", "proved"),
        ("hole", "proved", "proved"), ("reverting", "proved", "refuted")] do
      let some j := nodes.find? (fun j => (j.getObjValAs? String "name").toOption == some name)
        | throwError "missing obligation function {name}"
      if ["goodDo", "badDo", "zeroWhile", "continues", "breaks", "early"].contains name then
        let body ← Lean.ofExcept (Shared.field j "body")
        let ss ← Lean.ofExcept (Shared.arr body "statements")
        let some loop := ss.find? (fun s => [some "WhileStatement", some "DoWhileStatement"].contains
            (s.getObjValAs? String "nodeType").toOption)
          | throwError "missing loop metadata control {name}"
        let specs ← Lean.ofExcept (loop.getObjValAs? (Array String) "loopSpec")
        let bound := if name == "continues" then "2" else "1"
        unless specs == #["unwind " ++ bound] do throwError "loop annotation not retained for {name}"
      let (_, d) ← Lean.ofExcept (Shared.function reader j source.compress)
      let C := { base with funs := [(name, d)] }
      for (box, expected) in [(true, expectedBox), (false, expectedDiamond)] do
        let formula ← Lean.ofExcept (Shared.obligation lowerBodyLoops producerPre C name false box)
        let result := directResult C formula
        let actual ← Lean.ofExcept (result.getObjValAs? String "status")
        unless actual == expected do
          throwError "relative obligation {readerName} {name}, box={box}: {result.compress}, expected {expected}"
        logInfo m!"RELATIVE_CHECK {readerName} {name} box={box}: {actual} (trusted verifier; no certificate)"
    let some j := nodes.find? (fun j => (j.getObjValAs? String "name").toOption == some "returnGuard")
      | throwError "missing primitive-return control"
    let (name, d) ← Lean.ofExcept (Shared.function reader j source.compress)
    let C := { base with funs := [(name, d)] }
    let formula ← Lean.ofExcept (Shared.obligation lowerBodyLoops producerPre C name false false)
    let result := directResult C formula
    unless (result.getObjValAs? String "status").toOption == some "proved" do
      throwError "primitive return obligation did not prove: {result.compress}"
    let refDecl : FunDecl := { params := [("a", .array (.prim .uint))], body := [] }
    let R := { base with funs := [("reference", refDecl)] }
    match Shared.obligation lowerBodyLoops producerPre R "reference" false true with
    | .error "plain reference obligation" => pure ()
    | _ => throwError "plain reference obligation refusal changed"
    logInfo m!"primitive return proved/reference refusal preserved ({readerName})"
