import Solidity.Tools.DirectRuntime
import Solidity.Semantics.RunFuel

/-! Guards the H90 dynamic-memory candidate against vacuous bare-declaration
positives. These controls observe empty length and its wrong-length countercase
through existing intrinsic declarations, including string-to-bytes conversion.
They do not change AST admission, frozen snapshots or the held candidate, and
are not compiler/source/default-memory or native correctness proofs. -/
namespace DynamicBytesModelControls
open Lean Solidity Solidity.Frontend Solidity.Frontend.ExecutableAst.Shared
private def checked {α : Type} : Except String α → IO α
  | .ok a => pure a | .error e => throw (IO.userError e)
private def lengthEquals (e : RawExpr) (n : Nat) : RawStmt :=
  .assert (.binop .eqB (.field e "length") (.num n))
private def cases : List (String × List RawStmt × String) := [
  ("bytesEmpty", [.declMemory (.named "bytes") "b" none,
    lengthEquals (.name "b") 0], "normal"),
  ("bytesWrong", [.declMemory (.named "bytes") "b" none,
    lengthEquals (.name "b") 1], "panic"),
  ("stringViaBytesEmpty", [.declMemory (.named "string") "s" none,
    lengthEquals (.call "bytes" [.name "s"]) 0], "normal"),
  ("stringViaBytesWrong", [.declMemory (.named "string") "s" none,
    lengthEquals (.call "bytes" [.name "s"]) 1], "panic"),
  ("bytesAliasEmpty", [.declMemory (.named "bytes") "a" none,
    .declMemory (.named "bytes") "b" (some (.name "a")),
    lengthEquals (.name "b") 0], "normal"),
  ("stringAliasEmpty", [.declMemory (.named "string") "a" none,
    .declMemory (.named "string") "b" (some (.name "a")),
    lengthEquals (.call "bytes" [.name "b"]) 0], "normal")]
/-- Marker-sensitive ABI argument checks are narrower than assignment or source
adequacy: same-marker arguments pass and implicit bytes/string mixing refuses. -/
private def markerContext : ECtx :=
  [("b", .mem bytesR (dynBytesRowsOf "bytes")),
   ("s", .mem bytesR (dynBytesRowsOf "string"))]
private def markerContract : Contract := { vars := [] }
#guard (encodeCallArg markerContract markerContext "bytes" (.name "b")).isOk
#guard (encodeCallArg markerContract markerContext "string" (.name "s")).isOk
#guard !(encodeCallArg markerContract markerContext "string" (.name "b")).isOk
#guard !(encodeCallArg markerContract markerContext "bytes" (.name "s")).isOk

#eval show IO Unit from do
  for (name, body, expected) in cases do
    let C : Contract := { vars := [], funs := [(name, { params := [], rets := [], body })] }
    for box in [false,true] do
      let formula ← checked (assertionObligation lowerBodyLoops (fun _ _ => .tt) C name box)
      let halt ← match formula with
        | .imp _ (.imp _ (.modal modality program _ .tt)) =>
          unless modality == (if box then Modality.box else .diamond) do
            throw (IO.userError "model modality changed")
          match Prog.runF 128 program (State.init C) with
          | .ok _ => pure "normal"
          | .error .panic => pure "panic"
          | .error .revert => pure "revert"
          | .error other => throw (IO.userError s!"unexpected halt {repr other}")
        | _ => throw (IO.userError "model obligation shape changed")
      unless halt == expected do throw (IO.userError s!"{name}/{box}: expected {expected}, observed {halt}")
      IO.println s!"DYNAMIC_BYTES_MODEL {name} box={box}: {halt}"
end DynamicBytesModelControls
