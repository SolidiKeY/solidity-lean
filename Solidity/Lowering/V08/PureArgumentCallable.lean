import Solidity.Lowering.V08.LocalCallableTransport
import Solidity.Lowering.V08.SourceEnvironment

/-! Pure expression-argument composition for the selected integer-return body.
Individual Source expression and target Val execution facts are producer inputs,
NOT a presumed compiled-call preservation theorem. Target syntax depends on the
existing Val expression, never its runtime value. Locals and actual environment
reads below discharge these inputs; general expression/body compilation is open. -/
namespace Solidity.Lowering.V08.PureArgumentCallable
open Solidity Source
open Solidity.Lowering.V07
variable {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}

def arguments (t : Source.IntTy) (expression : Source.RExpr E srcΓ (.int t)) :
    Source.RConvArgs E srcΓ [.int t] := .cons expression (IntegerCallable.implicit_identity t) .nil

def body (p : PrimTy) (argument : Solidity.Val C Γ p) : Prog C Γ (.val p :: Γ) :=
  .cons (.declLocal p (.user "argument") (some argument)) .nil

theorem body_actual (p : PrimTy) (argument : Solidity.Val C Γ p) (state : State C Γ)
    (value : p.Denote) (evaluated : argument.evalT state = .ok value) :
    (body p argument).run state = .ok ⟨state.push (t:=.val p) value,List.prefix_refl _⟩ := by
  have step : (Stmt.declLocal p (.user "argument") (some argument) :
      Stmt C Γ (.val p :: Γ)).run state =
      .ok (⟨state.push (t:=.val p) value,List.prefix_refl _⟩ : Out C state.H (.val p :: Γ)) := by
    change TRun.declLocal p (some argument) state = _
    simp only [TRun.declLocal,evaluated]
    rfl
  unfold body
  rw [Prog.run_cons_ok step,Prog.run_nil]
  rfl

theorem result_actual (p : PrimTy) (state : State C Γ) (value : p.Denote) :
    LocalCallableTransport.result p (state.push (t:=.val p) value) = .ok value := rfl

theorem caller_restored (p : PrimTy) (argument : Solidity.Val C Γ p)
    (state : State C Γ) (value : p.Denote) :
    (state.push (t:=.val p) value).drop (body p argument).ext = state := rfl

theorem argument_actual (g : Source.Glob E) (f : Source.Fr) (extra : Nat)
    (t : Source.IntTy) (expression : Source.RExpr E srcΓ (.int t))
    (locals : Source.Locals E.layout srcΓ) (state : Source.St E)
    (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi)
    (evaluated : (Source.evalE g f (extra+11) expression).run (locals,state) =
      (.ok (.val (.int n h)),(locals,state))) :
    (Source.evalConvArgs g f (extra+12) (arguments t expression)).run (locals,state) =
      (.ok (.cons (.int n h) .nil),(locals,state)) := by
  change (do
    let rv ← Source.evalE g f (extra+11) expression
    let converted ← Source.convRV f (extra+11) (.int t) rv
    let v ← Source.getV converted
    let rest ← Source.evalConvArgs g f (extra+11) (.nil : Source.RConvArgs E srcΓ [])
    pure (Source.Vals.cons v rest)).run (locals,state) = _
  rw [Source.Hoare.run_bind,evaluated]
  dsimp only
  rw [IntegerCallable.conversion_identity]
  rfl

theorem source_expression (g : Source.Glob E) (f : Source.Fr) (decl : Source.Decl)
    (t : Source.IntTy) (selected : IntegerCallable.Inputs g f decl t) (extra : Nat)
    (expression : Source.RExpr E srcΓ (.int t)) (locals : Source.Locals E.layout srcΓ)
    (state : Source.St E) (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi)
    (evaluated : (Source.evalE g f (extra+11) expression).run (locals,state) =
      (.ok (.val (.int n h)),(locals,state))) :
    (Source.evalE g f (extra+13) (.call decl selected.signature (arguments t expression))).run
      (locals,state) = (.ok (.val (.int n h)),(locals,state)) :=
  SourceCallable.expression_complete g f (extra+12) decl selected.signature (arguments t expression)
    locals locals (.cons (.int n h) .nil) (.val (.int n h)) state state state
    (argument_actual g f extra t expression locals state n h evaluated)
    (IntegerCallable.source_call g f decl t selected extra state n h)

theorem transport (g : Source.Glob E) (f : Source.Fr) (decl : Source.Decl)
    (t : Source.IntTy) (selected : IntegerCallable.Inputs g f decl t) (extra : Nat)
    (expression : Source.RExpr E srcΓ (.int t)) (argument : Solidity.Val C Γ (integerPrim t))
    (locals : Source.Locals E.layout srcΓ) (source : Source.St E) (target : State C Γ)
    (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi)
    (sourceStep : (Source.evalE g f (extra+11) expression).run (locals,source) =
      (.ok (.val (.int n h)),(locals,source)))
    (targetStep : argument.evalT target = .ok (integerValue t n h)) :
    (Source.evalE g f (extra+13) (.call decl selected.signature (arguments t expression))).run
      (locals,source) = (.ok (.val (.int n h)),(locals,source)) ∧
    (body (integerPrim t) argument).run target =
      .ok ⟨target.push (t:=.val (integerPrim t)) (integerValue t n h),List.prefix_refl _⟩ ∧
    LocalCallableTransport.result (integerPrim t)
      (target.push (t:=.val (integerPrim t)) (integerValue t n h)) = .ok (integerValue t n h) ∧
    (target.push (t:=.val (integerPrim t)) (integerValue t n h)).drop
      (body (integerPrim t) argument).ext = target ∧
    IntValueRel t (.int n h : Source.Val E.layout (.int t)) (integerValue t n h) :=
  ⟨source_expression g f decl t selected extra expression locals source n h sourceStep,
    body_actual _ argument target _ targetStep,result_actual _ target _,
    caller_restored _ argument target _,integer_related t n h⟩

/-- Concrete producer application, not an uninhabited expression certificate. -/
theorem local_client (g : Source.Glob E) (f : Source.Fr) (decl : Source.Decl)
    (t : Source.IntTy) (selected : IntegerCallable.Inputs g f decl t) (extra : Nat)
    (i : Source.Idx srcΓ (.int t)) (j : Idx Γ (.val (integerPrim t)))
    (locals : Source.Locals E.layout srcΓ) (source : Source.St E) (target : State C Γ)
    (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi)
    (sourceRead : locals.get i = .int n h) (targetRead : TEnv.get j target.env = integerValue t n h) :
    (Source.evalE g f (extra+13) (.call decl selected.signature (arguments t (.local i)))).run
      (locals,source) = (.ok (.val (.int n h)),(locals,source)) ∧
    (body (integerPrim t) (.simple (.local j))).run target =
      .ok ⟨target.push (t:=.val (integerPrim t)) (integerValue t n h),List.prefix_refl _⟩ := by
  have reads := V07.source_local_transport g f (extra+10) (locals,source) target t i j n h sourceRead targetRead
  have complete := transport g f decl t selected extra (.local i) (.simple (.local j))
    locals source target n h reads.1 reads.2.1
  exact ⟨complete.1,complete.2.1⟩

/-- Actual non-local argument: msg.value at a populated Source machine and an
already paid typed target frame. This is BODY execution, not another World.call. -/
theorem value_client (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) :
    (Source.evalE (ScalarCallableTransport.global p) ScalarCallableTransport.frame (extra+13)
      (.call ScalarCallableTransport.declaration (IntegerCallable.uint_inputs p).signature
        (arguments Source.IntTy.u256 (.magic .msg "value" rfl)))).run
      (.cons (.bool true) .nil,ScalarCallableTransport.populated bytes) =
      (.ok (.val (.int 7 (by decide +kernel))),
        (.cons (.bool true) .nil,ScalarCallableTransport.populated bytes)) ∧
    (body PrimTy.uint (.simple (.env .msgValue rfl))).run ConstructorScalarTransport.entered =
      .ok ⟨ConstructorScalarTransport.entered.push (t:=.val .uint)
        (integerValue Source.IntTy.u256 7 (by decide +kernel)),List.prefix_refl _⟩ := by
  have sourceStep := SourceEnvironment.eval_value (ScalarCallableTransport.global p)
    ScalarCallableTransport.frame (extra+10) (.cons (.bool true) .nil) (ScalarCallableTransport.populated bytes)
  have targetStep : (Solidity.Val.simple (.env .msgValue rfl) :
      Solidity.Val ConstructorScalarTransport.Cell [] .uint).evalT ConstructorScalarTransport.entered =
      .ok (integerValue Source.IntTy.u256 7 (by decide +kernel)) := rfl
  have complete := transport (ScalarCallableTransport.global p) ScalarCallableTransport.frame
    ScalarCallableTransport.declaration Source.IntTy.u256 (IntegerCallable.uint_inputs p) extra
    (.magic .msg "value" rfl) (.simple (.env .msgValue rfl)) (.cons (.bool true) .nil)
    (ScalarCallableTransport.populated bytes) ConstructorScalarTransport.entered 7
    (by decide +kernel) sourceStep targetStep
  exact ⟨complete.1,complete.2.1⟩

def context8 : ContractWorld.Context :=
  {ConstructorScalarTransport.targetContext with mode:=.ordinary ⟨8,by decide +kernel⟩}
def entered8 : State ConstructorScalarTransport.Cell [] :=
  {ConstructorScalarTransport.entered with selfBalance:=⟨13,by decide +kernel⟩,net:=[(Controls.sender.1,8)],tx:=context8.tx ConstructorScalarTransport.targetInitial Controls.self}

theorem entered8_actual : ConstructorScalarTransport.targetInitial.enter (k:=()) Controls.self context8
    (Storage.init ConstructorScalarTransport.Cell) true = .ok entered8 := rfl

theorem value8_client (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) :
    (Source.evalE (ScalarCallableTransport.global p)
      {ScalarCallableTransport.frame with value:=ScalarCallableTransport.word 8} (extra+13)
      (.call ScalarCallableTransport.declaration ScalarCallableTransport.signature
        (arguments Source.IntTy.u256 (.magic .msg "value" rfl)))).run
      (.cons (.bool true) .nil,ScalarCallableTransport.populated bytes) =
      (.ok (.val (.int 8 (by decide +kernel))),
        (.cons (.bool true) .nil,ScalarCallableTransport.populated bytes)) ∧
    (body PrimTy.uint (.simple (.env .msgValue rfl))).run entered8 =
      .ok ⟨entered8.push (t:=.val .uint)
        (integerValue Source.IntTy.u256 8 (by decide +kernel)),List.prefix_refl _⟩ := by
  have selected : IntegerCallable.Inputs (ScalarCallableTransport.global p)
      {ScalarCallableTransport.frame with value:=ScalarCallableTransport.word 8}
      ScalarCallableTransport.declaration Source.IntTy.u256 :=
    ⟨ScalarCallableTransport.declaration_member,rfl,ScalarCallableTransport.signature,rfl⟩
  have sourceStep := SourceEnvironment.eval_value (ScalarCallableTransport.global p)
    {ScalarCallableTransport.frame with value:=ScalarCallableTransport.word 8}
    (extra+10) (.cons (.bool true) .nil) (ScalarCallableTransport.populated bytes)
  have targetStep : (Solidity.Val.simple (.env .msgValue rfl) :
      Solidity.Val ConstructorScalarTransport.Cell [] .uint).evalT entered8 =
      .ok (integerValue Source.IntTy.u256 8 (by decide +kernel)) := rfl
  have complete := transport (ScalarCallableTransport.global p)
    {ScalarCallableTransport.frame with value:=ScalarCallableTransport.word 8}
    ScalarCallableTransport.declaration Source.IntTy.u256 selected extra
    (.magic .msg "value" rfl) (.simple (.env .msgValue rfl)) (.cons (.bool true) .nil)
    (ScalarCallableTransport.populated bytes) entered8 8 (by decide +kernel) sourceStep targetStep
  exact ⟨complete.1,complete.2.1⟩

/-- Same target syntax at genuinely distinct paid frames reads7 versus8. -/
theorem value_not_constant :
    ((body PrimTy.uint (.simple (.env .msgValue rfl))).run ConstructorScalarTransport.entered).map
      (fun out => (LocalCallableTransport.result PrimTy.uint out.st).toOption.bind PrimTy.num?) ≠
    ((body PrimTy.uint (.simple (.env .msgValue rfl))).run entered8).map
      (fun out => (LocalCallableTransport.result PrimTy.uint out.st).toOption.bind PrimTy.num?) := by
  rw [body_actual PrimTy.uint _ ConstructorScalarTransport.entered
        (integerValue Source.IntTy.u256 7 (by decide +kernel)) rfl,
      body_actual PrimTy.uint _ entered8 (integerValue Source.IntTy.u256 8 (by decide +kernel)) rfl]
  change (Except.ok (some (7 : Int)) : TRes (Option Int)) ≠ .ok (some 8)
  intro same
  cases same

/-- info: 'Solidity.Lowering.V08.PureArgumentCallable.body_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.PureArgumentCallable.body_actual

/-- info: 'Solidity.Lowering.V08.PureArgumentCallable.result_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.PureArgumentCallable.result_actual

/-- info: 'Solidity.Lowering.V08.PureArgumentCallable.caller_restored' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.PureArgumentCallable.caller_restored

/-- info: 'Solidity.Lowering.V08.PureArgumentCallable.argument_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.PureArgumentCallable.argument_actual

/-- info: 'Solidity.Lowering.V08.PureArgumentCallable.source_expression' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.PureArgumentCallable.source_expression

/-- info: 'Solidity.Lowering.V08.PureArgumentCallable.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.PureArgumentCallable.transport

/-- info: 'Solidity.Lowering.V08.PureArgumentCallable.local_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.PureArgumentCallable.local_client

/-- info: 'Solidity.Lowering.V08.PureArgumentCallable.value_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.PureArgumentCallable.value_client

/-- info: 'Solidity.Lowering.V08.PureArgumentCallable.entered8_actual' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.PureArgumentCallable.entered8_actual

/-- info: 'Solidity.Lowering.V08.PureArgumentCallable.value8_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.PureArgumentCallable.value8_client

/-- info: 'Solidity.Lowering.V08.PureArgumentCallable.value_not_constant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.PureArgumentCallable.value_not_constant
end Solidity.Lowering.V08.PureArgumentCallable
