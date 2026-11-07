import Solidity.Tools.DirectRuntime
/-! Guards H90 dynamic bytes/string reference locals against premature admission
or marker erasure. These controls pin current refusals and existing type-marker
elaboration only; they neither implement admission nor prove compiler/source or
backend adequacy. Parameter/state and allocation contexts remain separate. -/
open Lean Solidity Solidity.Frontend Solidity.Frontend.ExecutableAst.Shared

/-- The existing local elaborator retains the dynamic bytes/string marker rows.
This equation says nothing about compiler metadata decoding or heap contents. -/
theorem dynamicByteRows_preserved (C : Contract) (spelling : String)
    (h : dynBytesTy spelling = true) :
    elabTyW C (.named spelling) = .ok (.array .uint, dynBytesRowsOf spelling) := by
  simp only [elabTyW, h, ↓reduceIte]
  rfl

#guard match elabTyW ({ vars := [] } : Contract) (.named "bytes") with
  | .ok (.array .uint, rows) => rows == dynBytesRowsOf "bytes" | _ => false
#guard match elabTyW ({ vars := [] } : Contract) (.named "string") with
  | .ok (.array .uint, rows) => rows == dynBytesRowsOf "string" | _ => false
#guard dynBytesRowsOf "bytes" != dynBytesRowsOf "string"
private def checked {α : Type} : Except String α → IO α
  | .ok a => pure a | .error e => throw (IO.userError e)
#eval show IO Unit from do
  let packet ← checked (Json.parse (← IO.FS.readFile "tests/directruntime-20261104/shared-translator/artifacts/dynamic-bytes/DynamicBytesBoundary.ast.json"))
  let some source := (J.nodes packet).find? (fun j => J.str? j "name" == some "DynamicBytesBoundary") |
    throw (IO.userError "dynamic-bytes fixture missing")
  for (name, spelling) in [("bytesDefault", "bytes"), ("stringDefault", "string"),
      ("bytesAlias", "bytes"), ("stringAlias", "string"), ("bytesAllocate", "bytes"),
      ("stringLiteral", "string"), ("bytesParameter", "bytes"),
      ("stringParameter", "string")] do
    let some f := (J.arrD source "nodes").find? (fun j => J.str? j "name" == some name) |
      throw (IO.userError s!"missing dynamic-byte function {name}")
    match function executableReader f "" with
    | .error reason =>
      unless reason == s!"compact verifier: unsupported type {spelling}" do
        throw (IO.userError s!"unexpected refusal {name}: {reason}")
      IO.println s!"DYNAMIC_BYTES_REFUSAL {name}: {reason}"
    | .ok _ => throw (IO.userError s!"premature dynamic-byte admission {name}")
  for (name, spelling) in [("DynamicBytesState", "bytes"), ("DynamicStringState", "string")] do
    let some state := (J.nodes packet).find? (fun j => J.str? j "name" == some name) |
      throw (IO.userError s!"missing state fixture {name}")
    match contract executableReader state with
    | .error reason =>
      unless reason == s!"compact verifier: unsupported type {spelling}" do
        throw (IO.userError s!"unexpected state refusal {name}: {reason}")
      IO.println s!"DYNAMIC_BYTES_REFUSAL {name}: {reason}"
    | .ok _ => throw (IO.userError s!"premature dynamic-byte state admission {name}")
#print axioms dynamicByteRows_preserved
