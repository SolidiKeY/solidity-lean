import Solidity.Yul.World.EffectfulEmitRevertPort

/-! Ordinary-function binding of the actual effectful emit/custom-error body.
Source runtime and existing ABI definitions remain unchanged. -/
namespace Solidity.Yul.World.EffectfulEmitFunction
open Solidity.Source
open Solidity.Roadmap (Bytes)
open Solidity.Yul.World.EffectfulEmitSource

def assignment (indexed anonymous : Bool) : RExpr (env indexed anonymous) [ReturningCall.uint] .bool :=
  .assign (.state flagDecl rfl rfl) (.bool true)
def args (indexed anonymous : Bool) : RConvArgs (env indexed anonymous) [ReturningCall.uint] [.bool] :=
  .cons (assignment indexed anonymous) (by cases indexed <;> cases anonymous <;> decide) .nil
def body (indexed anonymous : Bool) : RBody (env indexed anonymous) :=
  ⟨[],[ReturningCall.uint],false,[ReturningCall.uint],[ReturningCall.uint],
    .stmt (.emit (declaration indexed anonymous) rfl (args indexed anonymous))
      (.stmt (.revertError ReturningCall.errorDecl rfl
        (.cons (.const (Q.ofInt ReturningCall.value))
          (by cases indexed <;> cases anonymous <;> decide) .nil)) .nil),[]⟩
def glob {indexed anonymous} (G : Glob (env indexed anonymous)) : Glob (env indexed anonymous) :=
  {G with prog:={G.prog with contracts:=["Finite"], body:=fun d=>if d.name="answer" then some (body indexed anonymous) else none}}

/-- Derived actual ordinary-function execution, no supplied run/outcome. -/
theorem internal_actual {indexed anonymous} (G : Glob (env indexed anonymous)) (F : Fr)
    (s : EMState (env indexed anonymous) []) (normal : F.static=false)
    (code : F.contract="Finite") :
    (Source.callInternal (glob G) F 7 ReturningCall.answerDecl .nil [ReturningCall.uint]).run s=
      (.error (.revert (EffectfulEmitRevert.data G)),after G F s) := by
  cases F with
  | mk owner sender value st contract checked depth =>
    change contract="Finite" at code
    subst contract
    cases st
    · cases indexed <;> cases anonymous <;> cases G with
      | mk program pipeline fixed balance hasCode strategy timestamp => cases pipeline <;> rfl
    · cases normal

end Solidity.Yul.World.EffectfulEmitFunction
