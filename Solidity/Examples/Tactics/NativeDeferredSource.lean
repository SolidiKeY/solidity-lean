import Solidity.Semantics.NativeDeferred
import Solidity.Syntax.Splice
import Solidity.Calculus.Completeness
import Solidity.Calculus.PrintStmt

/-! Source programs retain an effectful receiver operand until its taclet fires. -/

namespace Solidity.Examples.Tactics.NativeDeferredSource

def C : Contract := contract!{
  uint calls;
  uint[] values;
  function valuesRef() returns (uint[] storage r) { calls++; r = values; }
  function operand() returns (uint v) { calls++; v = calls; }
}

def increment := sol[C]{ valuesRef().push(calls++); }
def callOperand := sol[C]{ valuesRef().push(operand()); }
def callerLocal := sol[C]{ uint i = 7; valuesRef().push(i++); calls = i; }
def afterReceiver := sol[C]{ valuesRef().push(calls++); uint afterValue = calls; }

def observe {Γ : Ctx} (o : TRes (Out C [] Γ)) : Option (Int × Int × Nat) :=
  (do
    let a ← o
    let calls ← Val.evalT a.st (.read (.root "calls" rfl))
    let first ← Val.evalT a.st
      (.read (.index (.arr .dyn) (.loc (.root "values" rfl)) (.simple (.lit 0 rfl))))
    pure (calls.1, first.1, a.st.H.length)).toOption

/-- `calls++` observes the getter's increment and then increments again. -/
theorem increment_run : observe (increment.run (State.init C)) = some (2, 1, 0) := by
  decide +kernel

/-- The operand call runs after the receiver getter, once. -/
theorem call_run : observe (callOperand.run (State.init C)) = some (2, 2, 0) := by
  decide +kernel

/-- A caller local changed by the operand remains changed after the statement. -/
theorem caller_run : observe (callerLocal.run (State.init C)) = some (8, 7, 0) := by
  decide +kernel

/-- The operand's private capture local does not leak into the next declaration. -/
theorem scope_run : ((afterReceiver.run (State.init C)).map
    (fun a => a.st.env.1.1)).toOption = some 2 := by
  decide +kernel

private def hiddenIncrement : Prog C [] [.val .uint] :=
  .cons (.declLocal .uint (.fresh "se" 1) none)
    (.cons (.assignIncDec .here .postInc rfl (.local .here) rfl) .nil)

private def hiddenArgument : Prog C [] [.val .uint] :=
  .cons (.declLocal .uint (.fresh "se" 1) none)
    (.cons (.call "operand" (.snoc .nil .uint (.user "x") (.simple (.local .here)))
      (.val .uint (.user "r") (some .here)) .nil) .nil)

private def finalValue : Src C [.val .uint] .uint := .val (.simple (.local .here))
private def emptyCode : Prog C [] [] := .nil
private def emptyValue : Src C [] .uint := .val (.simple (.lit 0 rfl))

/-- Private-prefix locals cannot be exposed by reconstructing a source operand. -/
example : hiddenIncrement.receiverExpr? [] finalValue = none ∧
    hiddenArgument.receiverExpr? [] finalValue = none ∧
    (Prog.nil (C := C) (Γ := [])).receiverExpr? []
      (.val (p := .uint) (.simple (.lit 0 rfl))) = none := by
  decide +kernel

/-- info: noncanonical receiver operands keep the explicit printer fallback -/
#guard_msgs in
run_meta do
  for name in [``hiddenIncrement, ``hiddenArgument] do
    let code := (← Lean.getConstInfo name).value!
    let value := (← Lean.getConstInfo ``finalValue).value!
    let shown ← Delab.withPrinter code false (Delab.ppDeferredExprS [] code value)
    unless shown.isNone do throwError "private operand local escaped: {shown}"
  let code := (← Lean.getConstInfo ``emptyCode).value!
  let value := (← Lean.getConstInfo ``emptyValue).value!
  let shown ← Delab.withPrinter code false (Delab.ppDeferredExprS [] code value)
  unless shown.isNone do throwError "empty deferred operand lost its native constructor"
  Lean.logInfo "noncanonical receiver operands keep the explicit printer fallback"

/-- info: four native receiver programs roundtrip through both source printers -/
#guard_msgs in
run_meta do
  for name in [``increment, ``callOperand, ``callerLocal, ``afterReceiver] do
    let info ← Lean.getConstInfo name
    let original := info.value!
    let some ss ← Delab.withPrinter original false (Delab.ppProgS [] original)
      | throwError "native receiver printer failed: {name}"
    let printed ← `(sol[C]{ $[$ss;]* })
    let parsed ← Lean.Elab.Term.TermElabM.run' do
      let p ← Lean.Elab.Term.elabTermEnsuringType printed info.type
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      pure p
    unless ← Lean.Meta.isDefEq original parsed do
      throwError "native receiver roundtrip changed {name}: {printed}"
    let shownExpr ← Lean.Meta.mkAppM ``Prog.show #[Lean.toExpr ([] : List Var), original]
    let shown ← unsafe Lean.Meta.evalExpr String (Lean.mkConst ``String) shownExpr
    let .ok shownSyntax := Lean.Parser.runParserCategory (← Lean.getEnv) `term s!"sol[C]\{ {shown} }"
      | throwError "native receiver display does not parse: {shown}"
    let parsed ← Lean.Elab.Term.TermElabM.run' do
      let p ← Lean.Elab.Term.elabTermEnsuringType shownSyntax info.type
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      pure p
    unless ← Lean.Meta.isDefEq original parsed do
      throwError "native receiver display roundtrip changed {name}: {shown}"
  Lean.logInfo "four native receiver programs roundtrip through both source printers"

end Solidity.Examples.Tactics.NativeDeferredSource
