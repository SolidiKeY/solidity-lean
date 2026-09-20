import Solidity.Tactics.Derivation
import Solidity.Semantics

/-!
# Function calls: KeY `functionBodyExpand` (+ `functionCallArgCapture`)

Judgments whose programs contain `Stmt.callStmt` are checked through
`SolidityJudgment.checkInlined` — inline through the test-contract
function table (`SoliditySyntax.funDef`), then run the interpreter.
`check` itself is untouched, so call-free judgments keep their meaning.
-/

namespace Solidity
namespace TacletExamples.FunctionCalls

open Rules StandardExample SoliditySyntax Examples

set_option maxHeartbeats 8000000

/-- `result = addOne(4);` — a single expansion. -/
example :
    (SolidityJudgment.mk
      ⟨.diamond,
        [Stmt.callStmt (some (rootPlace "result")) "addOne" [intLitExpr 4]]⟩
      sexpr!{ (result == 5) }).checkInlined = true := by
  native_decide

/-- `result = double(addOne-style arg);` — a simple-argument call whose
result feeds a second call: `i = addOne(4); result = double(i);`. -/
example :
    (SolidityJudgment.mk
      ⟨.diamond,
        [ Stmt.callStmt (some (rootPlace "i")) "addOne" [intLitExpr 4],
          Stmt.callStmt (some (rootPlace "result")) "double"
            [rootExpr "i"] ]⟩
      sexpr!{ (result == 10) }).checkInlined = true := by
  native_decide

/-- `result = inc2(4);` — `inc2` itself calls `addOne` twice, so the
inliner needs depth 2. -/
example :
    (SolidityJudgment.mk
      ⟨.diamond,
        [Stmt.callStmt (some (rootPlace "result")) "inc2" [intLitExpr 4]]⟩
      sexpr!{ (result == 6) }).checkInlined = true := by
  native_decide

/-- Complex argument (`functionCallArgCapture` shape): the inlined
reading still evaluates the argument at the call site. -/
example :
    (SolidityJudgment.mk
      ⟨.diamond,
        [ sstmt!{ alice.age = 4 },
          Stmt.callStmt (some (rootPlace "result")) "addOne"
            [sexpr!{ alice.age }] ]⟩
      sexpr!{ (result == 5) }).checkInlined = true := by
  native_decide

/-- Acyclicity lock-in: every table body is call-free after depth-8
inlining, so `checkInlined`'s default fuel always suffices (the solkey
no-recursion constraint, checked rather than assumed). -/
example :
    (["addOne", "double", "inc2"].all fun fn =>
      ((funDef fn).map fun d => blockCallFree (inlineBlock 8 d.body)
        ).getD false) = true := by
  native_decide

/-- The rewrite layer: one `functionBodyExpand` step replaces the call
with KeY's `ExpandFunctionBody` block — parameter declarations from the
actuals, the uninitialized named return, the body, and the result
assignment. -/
example :
    (⟨.diamond,
      [Stmt.callStmt (some (rootPlace "result")) "addOne" [intLitExpr 4]]⟩
      : SolidityBlock)
    —→ ⟨.diamond,
      [ Stmt.stackDecl Ty.uint "addOne$x" (some (intLitExpr 4)),
        Stmt.stackDecl Ty.uint "addOne$r" none,
        Stmt.assign (varPlace Kind.stack Ty.uint "addOne$r")
          (WrappedExpr.binop BinOp.add
            (varExpr Kind.stack Ty.uint "addOne$x") (intLitExpr 1)),
        Stmt.assign (rootPlace "result")
          (varExpr Kind.stack Ty.uint "addOne$r") ]⟩ := by
  named_step RuleName.functionBodyExpand

/-- The capture step first when an argument is complex
(`functionCallArgCapture`). -/
example :
    (⟨.diamond,
      [Stmt.callStmt (some (rootPlace "result")) "addOne"
        [sexpr!{ alice.age }]]⟩ : SolidityBlock)
    —→ ⟨.diamond,
      [ Rules.captureStackValue (sexpr!{ alice.age }),
        Stmt.callStmt (some (rootPlace "result")) "addOne"
          [Rules.stackValueAlias (sexpr!{ alice.age })] ]⟩ := by
  named_step RuleName.functionCallArgCapture

end TacletExamples.FunctionCalls
end Solidity
