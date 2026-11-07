import Solidity.Tools.DirectRuntime
import Solidity.Semantics.RunFuel

/-! Guards the native control-tuple plain-return refusal regression. These finite
intrinsic executions test existing return/loop lowering, defaults, early exit,
tuple capture, failure during return evaluation and lexical shadowing in both
modalities. Existing division-by-zero model guards revert rather than source
Panic(0x12); that failure-payload gap remains explicit. They are not AST/source transport or native machine proofs. -/
namespace PrimitiveReturnControls
open Lean Solidity Solidity.Frontend Solidity.Frontend.ExecutableAst.Shared
private def decl (body : List RawStmt) : FunDecl :=
  { params := [], rets := [("result", .prim .uint)], body := body }
private def cases : List (String × FunDecl × String) := [
  ("valueAndDeadCode", decl [.ret (some (.num 7)), .assert (.bool false)], "normal"),
  ("default", decl [.assert (.binop .eqB (.name "result") (.num 0)), .ret none], "normal"),
  ("named", decl [.assign (.name "result") (.num 5),
    .assert (.binop .eqB (.name "result") (.num 5)), .ret none], "normal"),
  ("conditionalExit", decl [.ite (.bool true) [.ret (some (.num 3))] [],
    .assert (.bool false)], "normal"),
  ("loopExit", decl [.whileLoop {} (.bool true) [.ret (some (.num 3))],
    .assert (.bool false)], "normal"),
  ("tuple", { decl [.ret (some (.tuple [.num 1, .num 2]))] with
    rets := [("a", .prim .uint), ("b", .prim .uint)] }, "normal"),
  ("shadow", decl [.block [.decl (.named "uint") "result" (some (.num 9))],
    .assert (.binop .eqB (.name "result") (.num 0)), .ret none], "normal"),
  ("assertionFailure", decl [.assert (.bool false), .ret (some (.num 1))], "panic"),
  ("returnEvaluationFailure", decl [.decl (.named "uint") "zero" (some (.num 0)),
    .ret (some (.binop .div (.num 1) (.name "zero")))], "revert")]
private def checked {α : Type} : Except String α → IO α
  | .ok a => pure a | .error e => throw (IO.userError e)
#eval show IO Unit from do
  for (name, d, expected) in cases do
    let C : Contract := { vars := [], funs := [(name, d)] }
    for box in [true, false] do
      let f ← checked (assertionObligation lowerBodyLoops (fun _ _ => .tt) C name box)
      let observed ← match f with
        | .imp _ (.imp _ (.modal modality program _ .tt)) =>
          unless modality == (if box then Modality.box else .diamond) do
            throw (IO.userError "modality changed")
          match Prog.runF 128 program (State.init C) with
          | .ok _ => pure "normal"
          | .error .panic => pure "panic"
          | .error .revert => pure "revert"
          | .error e => throw (IO.userError s!"{name}: unexpected halt {repr e}")
        | _ => throw (IO.userError "return slots became entry binders")
      unless observed == expected do throw (IO.userError s!"{name}/{box}: {observed}")
      IO.println s!"PRIMITIVE_RETURN {name} box={box}: {observed}"
#eval show IO Unit from do
  let C : Contract := { vars := [("x", .prim .uint)], funs := [("effect",
    decl [.ret (some (.incDec .postInc (.name "x")))])] }
  let f ← checked (assertionObligation lowerBodyLoops (fun _ _ => .tt) C "effect" false)
  match f with
  | .imp _ (.imp _ (.modal .diamond program _ .tt)) =>
    let σ ← checked ((Prog.runF 128 program (State.init C)).mapError reprStr)
    let value := σ.st.storage.get (by rfl : C.rootType "x" = some (.prim .uint))
    match value with
    | .prim n => unless n == uintOfNat 1 do
        throw (IO.userError "return expression side effect was dropped")
    IO.println "PRIMITIVE_RETURN effect: x=1"
  | _ => throw (IO.userError "side-effect formula shape")
private def reference : Contract := { vars := [], funs := [("f",
  { decl [] with rets := [("r", .array (.prim .uint))], retMem := true })] }
private def narrow : Contract := { vars := [], funs := [("f",
  { decl [] with widths := [("result", 8)] })] }
#guard match assertionObligation lowerBodyLoops (fun _ _ => .tt) reference "f" false with
  | .error "plain return obligation" => true | _ => false
#guard match assertionObligation lowerBodyLoops (fun _ _ => .tt) narrow "f" true with
  | .error "plain return obligation" => true | _ => false

#check primitiveReturnObligation
#check assertionObligation
#print axioms primitiveReturnObligation
#print axioms assertionObligation
end PrimitiveReturnControls
