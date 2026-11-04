import Solidity.Lowering.V08.SignedCallableControls
import Solidity.Lowering.V07.Operands
import Solidity.Lowering.V07.EffectfulCondition
import Solidity.Lowering.V08.SourceCallableControls

/-! G20: execute a fixed target program reading the caller's actual local,
not a program specialized with the argument value as a literal. Source body
selection is the existing pure integer-return certificate. Arbitrary caller
contexts/states and all existing integer widths/signs are retained. This is
not general body compilation, ABI ingress or external-call admission. -/
namespace Solidity.Lowering.V08.LocalCallableTransport
open Solidity Source
open Solidity.Lowering.V07

variable {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}

def arguments (t : Source.IntTy) (i : Source.Idx srcΓ (.int t)) :
    Source.RConvArgs E srcΓ [.int t] := .cons (.local i) (IntegerCallable.implicit_identity t) .nil

def body (p : PrimTy) (j : Idx Γ (.val p)) : Prog C Γ (.val p :: Γ) :=
  .cons (.declLocal p (.user "argument") (some (.simple (.local j)))) .nil

def result (p : PrimTy) (state : State C (.val p :: Γ)) : TRes p.Denote :=
  (Solidity.Val.simple (.local .here) : Solidity.Val C (.val p :: Γ) p).evalT state

theorem body_actual (p : PrimTy) (j : Idx Γ (.val p)) (state : State C Γ) :
    (body p j).run state = .ok ⟨state.push (t:=.val p) (TEnv.get j state.env),List.prefix_refl _⟩ := rfl

theorem result_actual (p : PrimTy) (j : Idx Γ (.val p)) (state : State C Γ) :
    result p (state.push (t:=.val p) (TEnv.get j state.env)) = .ok (TEnv.get j state.env) := rfl

theorem caller_restored (p : PrimTy) (j : Idx Γ (.val p)) (state : State C Γ) :
    (state.push (t:=.val p) (TEnv.get j state.env)).drop (body (C:=C) p j).ext = state := rfl

theorem argument_actual (g : Source.Glob E) (f : Source.Fr) (extra : Nat)
    (t : Source.IntTy) (i : Source.Idx srcΓ (.int t))
    (locals : Source.Locals E.layout srcΓ) (state : Source.St E)
    (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi) (read : locals.get i = .int n h) :
    (Source.evalConvArgs g f (extra+12) (arguments t i)).run (locals,state) =
      (.ok (.cons (.int n h) .nil),(locals,state)) := by
  simp only [arguments, Source.evalConvArgs, Source.evalE, IntegerCallable.conversion_identity, Source.getV, Source.RVal.get, Source.EM.locals, bind, pure, ExceptT.run, ExceptT.bind, ExceptT.pure, get, getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, Functor.map, Source.EM.lift]
  simp only [ExceptT.mk, bind, pure, StateT.bind, StateT.pure, StateT.get, StateT.map, Except.pure, ExceptT.bindCont, read]

theorem source_expression (g : Source.Glob E) (f : Source.Fr) (decl : Source.Decl)
    (t : Source.IntTy) (selected : IntegerCallable.Inputs g f decl t) (extra : Nat)
    (i : Source.Idx srcΓ (.int t)) (locals : Source.Locals E.layout srcΓ)
    (state : Source.St E) (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi)
    (read : locals.get i = .int n h) :
    (Source.evalE g f (extra+13) (.call decl selected.signature (arguments t i))).run (locals,state) =
      (.ok (.val (.int n h)),(locals,state)) :=
  SourceCallable.expression_complete g f (extra+12) decl selected.signature (arguments t i)
    locals locals (.cons (.int n h) .nil) (.val (.int n h)) state state state
    (argument_actual g f extra t i locals state n h read)
    (IntegerCallable.source_call g f decl t selected extra state n h)

/-- The target syntax depends on the local index/type, NEVER on n, its bound
proof, Source execution or target read result. Read premises are initial locals. -/
theorem transport (g : Source.Glob E) (f : Source.Fr) (decl : Source.Decl)
    (t : Source.IntTy) (selected : IntegerCallable.Inputs g f decl t) (extra : Nat)
    (i : Source.Idx srcΓ (.int t)) (j : Idx Γ (.val (integerPrim t)))
    (locals : Source.Locals E.layout srcΓ) (source : Source.St E) (target : State C Γ)
    (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi)
    (sourceRead : locals.get i = .int n h) (targetRead : TEnv.get j target.env = integerValue t n h) :
    (Source.evalE g f (extra+13) (.call decl selected.signature (arguments t i))).run (locals,source) =
      (.ok (.val (.int n h)),(locals,source)) ∧
    (body (integerPrim t) j).run target =
      .ok ⟨target.push (t:=.val (integerPrim t)) (integerValue t n h),List.prefix_refl _⟩ ∧
    result (integerPrim t) (target.push (t:=.val (integerPrim t)) (integerValue t n h)) =
      .ok (integerValue t n h) ∧
    (target.push (t:=.val (integerPrim t)) (integerValue t n h)).drop (body (C:=C) (integerPrim t) j).ext = target ∧
    IntValueRel t (.int n h : Source.Val E.layout (.int t)) (integerValue t n h) := by
  refine ⟨source_expression g f decl t selected extra i locals source n h sourceRead,?_,?_,?_,integer_related t n h⟩
  · rw [body_actual,targetRead]
  · rw [←targetRead]; exact result_actual _ j target
  · rw [←targetRead]; exact caller_restored _ j target

/-- A single fixed program handles BOTH runtime values, retaining a real
populated Source machine. The target caller also has an unrelated bool local. -/
theorem signed_client (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes)
    (n : Int) (h : SignedCallableControls.t.lo ≤ n ∧ n ≤ SignedCallableControls.t.hi)
    (C : Contract) (base : State C []) :
    (Source.evalE (SignedCallableControls.global p) SignedCallableControls.frame (extra+13)
      (.call SignedCallableControls.declaration (SignedCallableControls.inputs p).signature
        (arguments SignedCallableControls.t .here))).run
      (.cons (.int n h) .nil,SignedCallableControls.populated bytes) =
      (.ok (.val (.int n h)),(.cons (.int n h) .nil,SignedCallableControls.populated bytes)) ∧
    (body (integerPrim SignedCallableControls.t) (.here : Idx [.val (integerPrim SignedCallableControls.t),.val .bool]
      (.val (integerPrim SignedCallableControls.t)))).run
      ((base.push (t:=.val .bool) true).push (t:=.val (integerPrim SignedCallableControls.t))
        (integerValue SignedCallableControls.t n h)) =
      .ok ⟨((base.push (t:=.val .bool) true).push (t:=.val (integerPrim SignedCallableControls.t))
        (integerValue SignedCallableControls.t n h)).push (t:=.val (integerPrim SignedCallableControls.t))
        (integerValue SignedCallableControls.t n h),List.prefix_refl _⟩ := by
  have checked := transport (SignedCallableControls.global p) SignedCallableControls.frame
    SignedCallableControls.declaration SignedCallableControls.t (SignedCallableControls.inputs p)
    extra .here .here (.cons (.int n h) .nil) (SignedCallableControls.populated bytes)
    ((base.push (t:=.val .bool) true).push (t:=.val (integerPrim SignedCallableControls.t))
      (integerValue SignedCallableControls.t n h)) n h rfl rfl
  exact ⟨checked.1,checked.2.1⟩

theorem body_observation (p : PrimTy) (j : Idx Γ (.val p)) (state : State C Γ) :
    ((body p j).run state).map (fun out => result p out.st) = .ok (.ok (TEnv.get j state.env)) := by
  rw [body_actual]
  rfl

def twoLocals (base : State C []) :
    State C [.val (integerPrim SignedCallableControls.t),.val (integerPrim SignedCallableControls.t),.val .bool] :=
  ((base.push (t:=.val .bool) true).push (t:=.val (integerPrim SignedCallableControls.t))
    (integerValue SignedCallableControls.t 7 (by decide +kernel))).push
      (t:=.val (integerPrim SignedCallableControls.t))
      (integerValue SignedCallableControls.t (-128) (by decide +kernel))

theorem wrong_target_index (base : State C []) :
    ((body (integerPrim SignedCallableControls.t) .here).run (twoLocals base)).map
      (fun out => result (integerPrim SignedCallableControls.t) out.st) ≠
    ((body (integerPrim SignedCallableControls.t) (.there .here)).run (twoLocals base)).map
      (fun out => result (integerPrim SignedCallableControls.t) out.st) := by
  rw [body_observation,body_observation]
  intro same
  have numeric := congrArg (fun r => r.toOption.bind (fun inner => inner.toOption.bind PrimTy.num?)) same
  change some (-128 : Int) = some 7 at numeric
  cases numeric

def twoSourceLocals : Source.Locals SignedCallableControls.E.layout
    [.int SignedCallableControls.t,.int SignedCallableControls.t] :=
  .cons SignedCallableControls.minimum (.cons (.int 7 (by decide +kernel)) .nil)

theorem wrong_source_index (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) :
    (Source.evalE (SignedCallableControls.global p) SignedCallableControls.frame (extra+13)
      (.call SignedCallableControls.declaration (SignedCallableControls.inputs p).signature
        (arguments SignedCallableControls.t .here))).run
        (twoSourceLocals,SignedCallableControls.populated bytes) ≠
    (Source.evalE (SignedCallableControls.global p) SignedCallableControls.frame (extra+13)
      (.call SignedCallableControls.declaration (SignedCallableControls.inputs p).signature
        (arguments SignedCallableControls.t (.there .here)))).run
        (twoSourceLocals,SignedCallableControls.populated bytes) := by
  rw [source_expression _ _ _ _ (SignedCallableControls.inputs p) extra .here twoSourceLocals
        (SignedCallableControls.populated bytes) (-128) (by decide +kernel) rfl,
      source_expression _ _ _ _ (SignedCallableControls.inputs p) extra (.there .here) twoSourceLocals
        (SignedCallableControls.populated bytes) 7 (by decide +kernel) rfl]
  intro same
  cases same

theorem zero_horizon (g : Source.Glob E) (f : Source.Fr) (decl : Source.Decl)
    (t : Source.IntTy) (selected : IntegerCallable.Inputs g f decl t)
    (i : Source.Idx srcΓ (.int t)) (locals : Source.Locals E.layout srcΓ) (state : Source.St E) :
    (Source.evalE g f 0 (.call decl selected.signature (arguments t i))).run (locals,state) =
      (.error .timeout,(locals,state)) := rfl

/-- info: 'Solidity.Lowering.V08.LocalCallableTransport.body_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LocalCallableTransport.body_actual

/-- info: 'Solidity.Lowering.V08.LocalCallableTransport.result_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LocalCallableTransport.result_actual

/-- info: 'Solidity.Lowering.V08.LocalCallableTransport.caller_restored' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LocalCallableTransport.caller_restored

/-- info: 'Solidity.Lowering.V08.LocalCallableTransport.argument_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LocalCallableTransport.argument_actual

/-- info: 'Solidity.Lowering.V08.LocalCallableTransport.source_expression' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LocalCallableTransport.source_expression

/-- info: 'Solidity.Lowering.V08.LocalCallableTransport.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LocalCallableTransport.transport

/-- info: 'Solidity.Lowering.V08.LocalCallableTransport.signed_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LocalCallableTransport.signed_client

/-- info: 'Solidity.Lowering.V08.LocalCallableTransport.body_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LocalCallableTransport.body_observation

/-- info: 'Solidity.Lowering.V08.LocalCallableTransport.wrong_target_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LocalCallableTransport.wrong_target_index

/-- info: 'Solidity.Lowering.V08.LocalCallableTransport.wrong_source_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LocalCallableTransport.wrong_source_index

/-- info: 'Solidity.Lowering.V08.LocalCallableTransport.zero_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LocalCallableTransport.zero_horizon
end Solidity.Lowering.V08.LocalCallableTransport


/-! A producer-backed G20 ARGUMENT component. The actual Source call selects
SourceCallableControls.bodyFirst, including its reached heap allocation. The
target is V07's genuine assignment operand, NOT an implementation of that
callee. This relates argument value and retained caller write; canonical body,
heap, ABI, admission and runtime-frame compilation are not concluded. -/
namespace Solidity.Lowering.V08.EffectfulCallableArgument
open Solidity Source
open Solidity.Lowering.V07
namespace Fixture
abbrev E := SourceCallableControls.E
abbrev g := SourceCallableControls.global
abbrev f := SourceCallableControls.callerFrame
abbrev decl := SourceCallableControls.functionDecl
abbrev sig := SourceCallableControls.signature

def locals (old rhs : Bool) : Source.Locals E.layout [.bool,.bool] :=
  .cons (.bool old) (.cons (.bool rhs) .nil)
def assignment : Source.RExpr E [.bool,.bool] .bool :=
  .assign (.local .here) (.local (.there .here))
def args : Source.RConvArgs E [.bool,.bool] [.bool,.bool] :=
  .cons assignment rfl (.cons (.local .here) rfl .nil)
def reversed : Source.RConvArgs E [.bool,.bool] [.bool,.bool] :=
  .cons (.local .here) rfl (.cons assignment rfl .nil)
def expression : Source.RExpr E [.bool,.bool] .bool := .call decl sig args
def reversedExpression : Source.RExpr E [.bool,.bool] .bool := .call decl sig reversed
end Fixture
open Fixture

theorem arguments_actual (p : Roadmap.Pipeline) (extra : Nat) (old rhs : Bool)
    (state : Source.St E) :
    (Source.evalConvArgs (g p) f (extra+25) args).run (locals old rhs,state) =
      (.ok (SourceCallableControls.params rhs rhs),(locals rhs rhs,state)) := by
  rfl

/-- No callee equation is assumed: dispatch, body effects, result extraction
and caller-local restoration reduce through the existing actual evaluator. -/
theorem source_actual (p : Roadmap.Pipeline) (extra : Nat) (old rhs : Bool) :
    (Source.evalE (g p) f (extra+26) expression).run (locals old rhs,SourceCallableControls.populated) =
      (.ok (.val (.bool rhs)),(locals rhs rhs,
        SourceKeccak.afterLiteral SourceCallableControls.populated SourceCallableControls.binary)) :=
  SourceCallable.expression_complete (g p) f (extra+25) decl sig args
    (locals old rhs) (locals rhs rhs) (SourceCallableControls.params rhs rhs) (.val (.bool rhs))
    SourceCallableControls.populated SourceCallableControls.populated _
    (arguments_actual p extra old rhs _) (SourceCallableControls.call_execute p extra rhs rhs)

theorem reversed_arguments_actual (p : Roadmap.Pipeline) (extra : Nat) (old rhs : Bool)
    (state : Source.St E) :
    (Source.evalConvArgs (g p) f (extra+25) reversed).run (locals old rhs,state) =
      (.ok (SourceCallableControls.params old rhs),(locals rhs rhs,state)) := by
  rfl

theorem reversed_actual (p : Roadmap.Pipeline) (extra : Nat) (old rhs : Bool) :
    (Source.evalE (g p) f (extra+26) reversedExpression).run (locals old rhs,SourceCallableControls.populated) =
      (.ok (.val (.bool old)),(locals rhs rhs,
        SourceKeccak.afterLiteral SourceCallableControls.populated SourceCallableControls.binary)) :=
  SourceCallable.expression_complete (g p) f (extra+25) decl sig reversed
    (locals old rhs) (locals rhs rhs) (SourceCallableControls.params old rhs) (.val (.bool old))
    SourceCallableControls.populated SourceCallableControls.populated _
    (reversed_arguments_actual p extra old rhs _) (SourceCallableControls.call_execute p extra old rhs)

/-- Fixed target syntax reads its actual caller local. Only the independent
initial value correspondence is required, not an assumed execution relation. -/
theorem transport {C : Contract} {Γ : Ctx} (p : Roadmap.Pipeline) (extra : Nat)
    (old rhs : Bool) (target : State C Γ)
    (write read : Idx Γ (.val .bool)) (initialRead : TEnv.get read target.env = rhs) :
    (Source.evalE (g p) f (extra+26) expression).run (locals old rhs,SourceCallableControls.populated) =
      (.ok (.val (.bool rhs)),(locals rhs rhs,
        SourceKeccak.afterLiteral SourceCallableControls.populated SourceCallableControls.binary)) ∧
    (assignLocalOperand write read).run target =
      .ok (⟨target.setLocal write rhs,List.prefix_refl _⟩,.prim rhs) ∧
    (target.setLocal write rhs).glob = target.glob := by
  refine ⟨source_actual p extra old rhs,?_,rfl⟩
  rw [assigned_condition_operand_run,initialRead]

def live : PrimTy.uint.Denote := integerValue Source.IntTy.u256 42 (by decide +kernel)
def target {C : Contract} (base : State C []) (old rhs : Bool) :
    State C [.val .bool,.val .uint,.val .bool] :=
  ((base.push (t:=.val .bool) rhs).push (t:=.val .uint) live).push (t:=.val .bool) old

def operand {C : Contract} : DeferredSource.Operand C [.val .bool,.val .uint,.val .bool] (.prim .bool) :=
  assignLocalOperand .here (.there (.there .here))

/-- Different source/target positions, unrelated live integer, populated
Source machine and arbitrary complete target state. Both Boolean values work. -/
theorem inhabited {C : Contract} (base : State C []) (p : Roadmap.Pipeline)
    (extra : Nat) (old rhs : Bool) :
    (Source.evalE (g p) f (extra+26) expression).run
      (locals old rhs,SourceCallableControls.populated) =
      (.ok (.val (.bool rhs)),(locals rhs rhs,
        SourceKeccak.afterLiteral SourceCallableControls.populated SourceCallableControls.binary)) ∧
    operand.run (target base old rhs) =
      .ok (⟨(target base old rhs).setLocal .here rhs,List.prefix_refl _⟩,.prim rhs) := by
  have applied := transport p extra old rhs (target base old rhs)
    .here (.there (.there .here)) rfl
  exact ⟨applied.1,applied.2.1⟩

def observe {C : Contract} (state : State C [.val .bool,.val .uint,.val .bool]) :
    Bool × Option Int × Bool :=
  (TEnv.get (.here : Idx [.val .bool,.val .uint,.val .bool] (.val .bool)) state.env,
   PrimTy.num? (TEnv.get (.there .here : Idx [.val .bool,.val .uint,.val .bool] (.val .uint)) state.env),
   TEnv.get (.there (.there .here) : Idx [.val .bool,.val .uint,.val .bool] (.val .bool)) state.env)

theorem target_vector {C : Contract} (base : State C []) (old rhs : Bool) :
    ((operand.run (target base old rhs)).toOption.map fun result => observe result.1.st) =
      some (rhs,some 42,rhs) := by
  rw [operand,assigned_condition_operand_run]
  rfl

theorem closed_client (old rhs : Bool) :
    operand.run (target ConstructorScalarTransport.entered old rhs) =
      .ok (⟨(target ConstructorScalarTransport.entered old rhs).setLocal .here rhs,List.prefix_refl _⟩,.prim rhs) :=
  (inhabited ConstructorScalarTransport.entered .viaIR 0 old rhs).2

theorem populated_retained :
    (SourceKeccak.afterLiteral SourceCallableControls.populated SourceCallableControls.binary).ex = SourceCallableControls.populated.ex ∧
    (SourceKeccak.afterLiteral SourceCallableControls.populated SourceCallableControls.binary).events = SourceCallableControls.populated.events ∧
    (SourceKeccak.afterLiteral SourceCallableControls.populated SourceCallableControls.binary).logs = SourceCallableControls.populated.logs ∧
    (SourceKeccak.afterLiteral SourceCallableControls.populated SourceCallableControls.binary).fnLocals = SourceCallableControls.populated.fnLocals ∧
    (SourceKeccak.afterLiteral SourceCallableControls.populated SourceCallableControls.binary).heap.next = 2 ∧
    (SourceKeccak.afterLiteral SourceCallableControls.populated SourceCallableControls.binary).heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    (SourceKeccak.afterLiteral SourceCallableControls.populated SourceCallableControls.binary).heap.get 1 = some ⟨.bytes .memory,.bytes SourceCallableControls.binary⟩ :=
  SourceCallableControls.retained_machine

theorem wrong_order (p : Roadmap.Pipeline) :
    (Source.evalE (g p) f 26 expression).run (locals true false,SourceCallableControls.populated) ≠
    (Source.evalE (g p) f 26 reversedExpression).run (locals true false,SourceCallableControls.populated) := by
  rw [source_actual p 0,reversed_actual p 0]
  intro same
  have value := congrArg Prod.fst same
  cases value

theorem wrong_read {C : Contract} (base : State C []) :
    (assignLocalOperand (.here : Idx [.val .bool,.val .uint,.val .bool] (.val .bool)) .here).run
      (target base true false) ≠ operand.run (target base true false) := by
  rw [operand,assigned_condition_operand_run,assigned_condition_operand_run]
  intro same
  have value := congrArg (fun r => r.toOption.map (fun result => result.2)) same
  cases value

/-- A return-value-only relation would miss the caller write. -/
theorem skipped_write {C : Contract} (base : State C []) :
    operand.run (target base true false) ≠
      .ok (⟨target base true false,List.prefix_refl _⟩,.prim false) := by
  rw [operand,assigned_condition_operand_run]
  intro same
  have value := congrArg (fun r => r.toOption.map (fun result => (observe result.1.st).1)) same
  cases value

theorem zero_horizon (p : Roadmap.Pipeline) (old rhs : Bool) (state : Source.St E) :
    (Source.evalE (g p) f 0 expression).run (locals old rhs,state) =
      (.error .timeout,(locals old rhs,state)) := by
  rfl

theorem reached_timeout (p : Roadmap.Pipeline) (old rhs : Bool) (state : Source.St E) :
    (Source.evalE (g p) f 4 expression).run (locals old rhs,state) =
      (.error .timeout,(locals rhs rhs,state)) := by
  rfl

/-- info: 'Solidity.Lowering.V08.EffectfulCallableArgument.arguments_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.EffectfulCallableArgument.arguments_actual
/-- info: 'Solidity.Lowering.V08.EffectfulCallableArgument.source_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.EffectfulCallableArgument.source_actual
/-- info: 'Solidity.Lowering.V08.EffectfulCallableArgument.reversed_arguments_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.EffectfulCallableArgument.reversed_arguments_actual
/-- info: 'Solidity.Lowering.V08.EffectfulCallableArgument.reversed_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.EffectfulCallableArgument.reversed_actual
/-- info: 'Solidity.Lowering.V08.EffectfulCallableArgument.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.EffectfulCallableArgument.transport
/-- info: 'Solidity.Lowering.V08.EffectfulCallableArgument.inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.EffectfulCallableArgument.inhabited
/-- info: 'Solidity.Lowering.V08.EffectfulCallableArgument.target_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.EffectfulCallableArgument.target_vector
/-- info: 'Solidity.Lowering.V08.EffectfulCallableArgument.closed_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.EffectfulCallableArgument.closed_client
/-- info: 'Solidity.Lowering.V08.EffectfulCallableArgument.populated_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.EffectfulCallableArgument.populated_retained
/-- info: 'Solidity.Lowering.V08.EffectfulCallableArgument.wrong_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.EffectfulCallableArgument.wrong_order
/-- info: 'Solidity.Lowering.V08.EffectfulCallableArgument.wrong_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.EffectfulCallableArgument.wrong_read
/-- info: 'Solidity.Lowering.V08.EffectfulCallableArgument.skipped_write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.EffectfulCallableArgument.skipped_write
/-- info: 'Solidity.Lowering.V08.EffectfulCallableArgument.zero_horizon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.EffectfulCallableArgument.zero_horizon
/-- info: 'Solidity.Lowering.V08.EffectfulCallableArgument.reached_timeout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.EffectfulCallableArgument.reached_timeout
end Solidity.Lowering.V08.EffectfulCallableArgument


/-! Environment/context/width-polymorphic assignment-argument application.
The existing IntegerCallable.Inputs selects the actual pure argument-return
body; it does NOT assume its execution. The target is the real published V07
assignment operand. General callee compilation, external frames, ABI, admission
and whole Source/target world/heap correspondence are not concluded. -/
namespace Solidity.Lowering.V08.AssignedIntegerCallable
open Solidity Source
open Solidity.Lowering.V07
variable {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}

def arguments (t : Source.IntTy) (i a : Source.Idx srcΓ (.int t)) :
    Source.RConvArgs E srcΓ [.int t] :=
  .cons (.assign (.local i) (.local a)) (IntegerCallable.implicit_identity t) .nil

theorem argument_actual (g : Source.Glob E) (f : Source.Fr) (extra : Nat)
    (t : Source.IntTy) (i a : Source.Idx srcΓ (.int t))
    (locals : Source.Locals E.layout srcΓ) (state : Source.St E)
    (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi) (read : locals.get a = .int n h) :
    (Source.evalConvArgs g f (extra+12) (arguments t i a)).run (locals,state) =
      (.ok (.cons (.int n h) .nil),(locals.set i (.int n h),state)) := by
  simp only [arguments, Source.evalConvArgs, IntegerCallable.conversion_identity]
  rw [Source.Hoare.run_bind,
    source_assign_local_run g f (extra+9) (locals,state) i a (.int n h) read]
  rfl

theorem source_expression (g : Source.Glob E) (f : Source.Fr) (decl : Source.Decl)
    (t : Source.IntTy) (selected : IntegerCallable.Inputs g f decl t) (extra : Nat)
    (i a : Source.Idx srcΓ (.int t)) (locals : Source.Locals E.layout srcΓ)
    (state : Source.St E) (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi)
    (read : locals.get a = .int n h) :
    (Source.evalE g f (extra+13) (.call decl selected.signature (arguments t i a))).run (locals,state) =
      (.ok (.val (.int n h)),(locals.set i (.int n h),state)) :=
  SourceCallable.expression_complete g f (extra+12) decl selected.signature (arguments t i a)
    locals (locals.set i (.int n h)) (.cons (.int n h) .nil) (.val (.int n h)) state state state
    (argument_actual g f extra t i a locals state n h read)
    (IntegerCallable.source_call g f decl t selected extra state n h)

/-- The exact whole Source state is retained; the target Out retains its
actual caller write. Initial independent typed value reads are the only
Source/target correspondence premises in this component. -/
theorem transport (g : Source.Glob E) (f : Source.Fr) (decl : Source.Decl)
    (t : Source.IntTy) (selected : IntegerCallable.Inputs g f decl t) (extra : Nat)
    (i a : Source.Idx srcΓ (.int t)) (j b : Idx Γ (.val (integerPrim t)))
    (locals : Source.Locals E.layout srcΓ) (source : Source.St E) (target : State C Γ)
    (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi)
    (sourceRead : locals.get a = .int n h) (targetRead : TEnv.get b target.env = integerValue t n h) :
    (Source.evalE g f (extra+13) (.call decl selected.signature (arguments t i a))).run (locals,source) =
      (.ok (.val (.int n h)),(locals.set i (.int n h),source)) ∧
    (assignLocalOperand j b).run target =
      .ok (⟨target.setLocal j (integerValue t n h),List.prefix_refl _⟩,.prim (integerValue t n h)) ∧
    IntValueRel t (.int n h : Source.Val E.layout (.int t)) (integerValue t n h) ∧
    (target.setLocal j (integerValue t n h)).glob = target.glob :=
  ⟨source_expression g f decl t selected extra i a locals source n h sourceRead,
    assign_local_operand_run target j b _ targetRead,integer_related t n h,rfl⟩


abbrev t := SignedCallableControls.t
def sourceLocals (old rhs : Int) (ho : t.lo ≤ old ∧ old ≤ t.hi)
    (hr : t.lo ≤ rhs ∧ rhs ≤ t.hi) : Source.Locals SignedCallableControls.E.layout [.int t,.bool,.int t] :=
  .cons (.int old ho) (.cons (.bool false) (.cons (.int rhs hr) .nil))
def target {C : Contract} (base : State C []) (old rhs : Int)
    (ho : t.lo ≤ old ∧ old ≤ t.hi) (hr : t.lo ≤ rhs ∧ rhs ≤ t.hi) :
    State C [.val .bool,.val (integerPrim t),.val (integerPrim t)] :=
  ((base.push (t:=.val (integerPrim t)) (integerValue t rhs hr)).push
    (t:=.val (integerPrim t)) (integerValue t old ho)).push (t:=.val .bool) true

def operand {C : Contract} : DeferredSource.Operand C
    [.val .bool,.val (integerPrim t),.val (integerPrim t)] (.prim (integerPrim t)) :=
  assignLocalOperand (.there .here) (.there (.there .here))

theorem signed_client (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes)
    (old rhs : Int) (ho : t.lo ≤ old ∧ old ≤ t.hi) (hr : t.lo ≤ rhs ∧ rhs ≤ t.hi)
    {C : Contract} (base : State C []) :
    (Source.evalE (SignedCallableControls.global p) SignedCallableControls.frame (extra+13)
      (.call SignedCallableControls.declaration (SignedCallableControls.inputs p).signature
        (arguments t .here (.there (.there .here))))).run
      (sourceLocals old rhs ho hr,SignedCallableControls.populated bytes) =
      (.ok (.val (.int rhs hr)),(sourceLocals rhs rhs hr hr,SignedCallableControls.populated bytes)) ∧
    operand.run (target base old rhs ho hr) =
      .ok (⟨(target base old rhs ho hr).setLocal (.there .here) (integerValue t rhs hr),
        List.prefix_refl _⟩,.prim (integerValue t rhs hr)) := by
  have applied := transport (SignedCallableControls.global p) SignedCallableControls.frame
    SignedCallableControls.declaration t (SignedCallableControls.inputs p) extra
    .here (.there (.there .here)) (.there .here) (.there (.there .here))
    (sourceLocals old rhs ho hr) (SignedCallableControls.populated bytes)
    (target base old rhs ho hr) rhs hr rfl rfl
  exact ⟨applied.1,applied.2.1⟩

def targetVector {C : Contract}
    (state : State C [.val .bool,.val (integerPrim t),.val (integerPrim t)]) :
    Bool × Option Int × Option Int :=
  (TEnv.get (.here : Idx [.val .bool,.val (integerPrim t),.val (integerPrim t)] (.val .bool)) state.env,
   PrimTy.num? (TEnv.get (.there .here : Idx [.val .bool,.val (integerPrim t),.val (integerPrim t)] (.val (integerPrim t))) state.env),
   PrimTy.num? (TEnv.get (.there (.there .here) : Idx [.val .bool,.val (integerPrim t),.val (integerPrim t)] (.val (integerPrim t))) state.env))

theorem target_vector {C : Contract} (base : State C []) (old rhs : Int)
    (ho : t.lo ≤ old ∧ old ≤ t.hi) (hr : t.lo ≤ rhs ∧ rhs ≤ t.hi) :
    (operand.run (target base old rhs ho hr)).toOption.map (fun result => targetVector result.1.st) =
      some (true,some rhs,some rhs) := by
  rfl

/-- A genuine selected body still allows caller-local assignment in static
context: this operation is not a persistent/transient store. -/
theorem static_inputs (g : Source.Glob E) (f : Source.Fr) (decl : Source.Decl)
    (ty : Source.IntTy) (selected : IntegerCallable.Inputs g f decl ty) :
    IntegerCallable.Inputs g {f with static:=true} decl ty :=
  ⟨selected.member,selected.kind,selected.signature,selected.selected⟩

theorem static_client (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (SignedCallableControls.global p) {SignedCallableControls.frame with static:=true} 13
      (.call SignedCallableControls.declaration
        (static_inputs _ _ _ _ (SignedCallableControls.inputs p)).signature
        (arguments t .here (.there (.there .here))))).run
      (sourceLocals 127 (-128) (by decide +kernel) (by decide +kernel),SignedCallableControls.populated bytes) =
      (.ok (.val (.int (-128) (by decide +kernel))),
        (sourceLocals (-128) (-128) (by decide +kernel) (by decide +kernel),SignedCallableControls.populated bytes)) :=
  source_expression _ _ _ _ (static_inputs _ _ _ _ (SignedCallableControls.inputs p)) 0
    .here (.there (.there .here)) _ _ (-128) (by decide +kernel) rfl

theorem wrong_source_read (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (SignedCallableControls.global p) SignedCallableControls.frame 13
      (.call SignedCallableControls.declaration (SignedCallableControls.inputs p).signature
        (arguments t .here .here))).run
      (sourceLocals 127 (-128) (by decide +kernel) (by decide +kernel),SignedCallableControls.populated bytes) ≠
    (Source.evalE (SignedCallableControls.global p) SignedCallableControls.frame 13
      (.call SignedCallableControls.declaration (SignedCallableControls.inputs p).signature
        (arguments t .here (.there (.there .here))))).run
      (sourceLocals 127 (-128) (by decide +kernel) (by decide +kernel),SignedCallableControls.populated bytes) := by
  rw [source_expression _ _ _ _ (SignedCallableControls.inputs p) 0 .here .here _ _ 127 (by decide +kernel) rfl,
      source_expression _ _ _ _ (SignedCallableControls.inputs p) 0 .here (.there (.there .here)) _ _ (-128) (by decide +kernel) rfl]
  intro same
  cases same

theorem wrong_target_read {C : Contract} (base : State C []) :
    (assignLocalOperand (.there .here : Idx [.val .bool,.val (integerPrim t),.val (integerPrim t)] (.val (integerPrim t)))
      (.there .here)).run (target base 127 (-128) (by decide +kernel) (by decide +kernel)) ≠
    operand.run (target base 127 (-128) (by decide +kernel) (by decide +kernel)) := by
  rw [operand,assign_local_operand_run _ _ _ _ rfl,assign_local_operand_run _ _ _ _ rfl]
  intro same
  have numeric := congrArg (fun r => r.toOption.map (fun result => match result.2 with | .prim v => PrimTy.num? v)) same
  change some (some (127 : Int)) = some (some (-128 : Int)) at numeric
  cases numeric

theorem skipped_write {C : Contract} (base : State C []) :
    operand.run (target base 127 (-128) (by decide +kernel) (by decide +kernel)) ≠
      .ok (⟨target base 127 (-128) (by decide +kernel) (by decide +kernel),List.prefix_refl _⟩,
        .prim (integerValue t (-128) (by decide +kernel))) := by
  rw [operand,assign_local_operand_run _ _ _ _ rfl]
  intro same
  have numeric := congrArg (fun r => r.toOption.map (fun result => (targetVector result.1.st).2.1)) same
  change some (some (-128 : Int)) = some (some (127 : Int)) at numeric
  cases numeric

theorem reached_timeout (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (SignedCallableControls.global p) SignedCallableControls.frame 4
      (.call SignedCallableControls.declaration (SignedCallableControls.inputs p).signature
        (arguments t .here (.there (.there .here))))).run
      (sourceLocals 127 (-128) (by decide +kernel) (by decide +kernel),SignedCallableControls.populated bytes) =
      (.error .timeout,
        (sourceLocals (-128) (-128) (by decide +kernel) (by decide +kernel),SignedCallableControls.populated bytes)) := by
  rfl

theorem zero_horizon (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (SignedCallableControls.global p) SignedCallableControls.frame 0
      (.call SignedCallableControls.declaration (SignedCallableControls.inputs p).signature
        (arguments t .here (.there (.there .here))))).run
      (sourceLocals 127 (-128) (by decide +kernel) (by decide +kernel),SignedCallableControls.populated bytes) =
      (.error .timeout,
        (sourceLocals 127 (-128) (by decide +kernel) (by decide +kernel),SignedCallableControls.populated bytes)) := by
  rfl

theorem unsigned_inputs (p : Roadmap.Pipeline) :
    IntegerCallable.Inputs (ScalarCallableTransport.global p) ScalarCallableTransport.frame
      ScalarCallableTransport.declaration Source.IntTy.u256 :=
  ⟨ScalarCallableTransport.declaration_member,rfl,ScalarCallableTransport.signature,rfl⟩

def maximum : Int := 2^256-1
def unsignedLocals : Source.Locals ScalarCallableTransport.E.layout
    [.int Source.IntTy.u256,.int Source.IntTy.u256] :=
  .cons (.int 1 (by decide +kernel)) (.cons (.int maximum (by decide +kernel)) .nil)

theorem unsigned_maximum (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (ScalarCallableTransport.global p) ScalarCallableTransport.frame 13
      (.call ScalarCallableTransport.declaration (unsigned_inputs p).signature
        (arguments Source.IntTy.u256 .here (.there .here)))).run
      (unsignedLocals,ScalarCallableTransport.populated bytes) =
      (.ok (.val (.int maximum (by decide +kernel))),
        (.cons (.int maximum (by decide +kernel)) (.cons (.int maximum (by decide +kernel)) .nil),
          ScalarCallableTransport.populated bytes)) :=
  source_expression _ _ _ _ (unsigned_inputs p) 0 .here (.there .here) _ _ maximum (by decide +kernel) rfl


def closedSource (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :=
  (Source.evalE (SignedCallableControls.global p) SignedCallableControls.frame 13
    (.call SignedCallableControls.declaration (SignedCallableControls.inputs p).signature
      (arguments t .here (.there (.there .here))))).run
    (sourceLocals 127 (-128) (by decide +kernel) (by decide +kernel),SignedCallableControls.populated bytes)

def closedTarget :=
  operand.run (target ConstructorScalarTransport.entered 127 (-128) (by decide +kernel) (by decide +kernel))

theorem closed_boundary (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    closedSource p bytes =
      (.ok (.val (.int (-128) (by decide +kernel))),
        (sourceLocals (-128) (-128) (by decide +kernel) (by decide +kernel),SignedCallableControls.populated bytes)) ∧
    closedTarget = .ok (⟨(target ConstructorScalarTransport.entered 127 (-128) (by decide +kernel) (by decide +kernel)).setLocal
      (.there .here) (integerValue t (-128) (by decide +kernel)),List.prefix_refl _⟩,
        .prim (integerValue t (-128) (by decide +kernel))) :=
  signed_client p 0 bytes 127 (-128) (by decide +kernel) (by decide +kernel) ConstructorScalarTransport.entered

theorem payload_clients (p : Roadmap.Pipeline) :
    ∀ bytes ∈ [[],[0,255,128],List.replicate 33 129],
      closedSource p bytes =
        (.ok (.val (.int (-128) (by decide +kernel))),
          (sourceLocals (-128) (-128) (by decide +kernel) (by decide +kernel),SignedCallableControls.populated bytes)) :=
  fun bytes _ => (closed_boundary p bytes).1

/-- These populated input fields are retained by the complete Source result
above, not inferred from a smaller balance-only projection. -/
theorem populated_fields (bytes : Roadmap.Bytes) :
    ((SignedCallableControls.populated bytes).ex.world.accounts SignedCallableControls.frame.sender).balance = 93 ∧
    ((SignedCallableControls.populated bytes).ex.world.accounts SignedCallableControls.frame.this).balance = 12 ∧
    ((SignedCallableControls.populated bytes).ex.world.accounts SignedCallableControls.frame.sender).nonce = 3 ∧
    ((SignedCallableControls.populated bytes).ex.world.accounts SignedCallableControls.frame.this).nonce = 1 ∧
    ((SignedCallableControls.populated bytes).ex.world.accounts SignedCallableControls.frame.this).code = some 0 ∧
    ((SignedCallableControls.populated bytes).ex.world.accounts SignedCallableControls.frame.this).storage.read ScalarCallableTransport.saved.path =
      some (.int 42 (by decide +kernel)) ∧
    ((SignedCallableControls.populated bytes).ex.transient.cells SignedCallableControls.frame.this).read ScalarCallableTransport.scratch.path =
      some (.int 9 (by decide +kernel)) ∧
    ((SignedCallableControls.populated bytes).ex.transient.cells SignedCallableControls.frame.sender).read ScalarCallableTransport.scratch.path =
      some (.int 17 (by decide +kernel)) ∧
    (SignedCallableControls.populated bytes).ex.journal.length = 4 ∧
    (SignedCallableControls.populated bytes).heap.next = 2 ∧
    (SignedCallableControls.populated bytes).heap.get 0 = some ⟨.bytes .memory,.bytes bytes⟩ ∧
    (SignedCallableControls.populated bytes).heap.get 1 = some ⟨.bytes .memory,.bytes [128,255]⟩ ∧
    (SignedCallableControls.populated bytes).events = [.call SignedCallableControls.frame.sender (ScalarCallableTransport.word 7) bytes false] ∧
    (SignedCallableControls.populated bytes).logs = [(SignedCallableControls.frame.this,bytes),(SignedCallableControls.frame.sender,[0xab,0,255])] ∧
    (SignedCallableControls.populated bytes).fnLocals = ⟨[.bool],.cons (.bool true) .nil⟩ :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Lowering.V08.AssignedIntegerCallable.argument_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.AssignedIntegerCallable.argument_actual
/-- info: 'Solidity.Lowering.V08.AssignedIntegerCallable.source_expression' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.AssignedIntegerCallable.source_expression
/-- info: 'Solidity.Lowering.V08.AssignedIntegerCallable.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.AssignedIntegerCallable.transport
/-- info: 'Solidity.Lowering.V08.AssignedIntegerCallable.signed_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.AssignedIntegerCallable.signed_client
/-- info: 'Solidity.Lowering.V08.AssignedIntegerCallable.target_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.AssignedIntegerCallable.target_vector
/-- info: 'Solidity.Lowering.V08.AssignedIntegerCallable.static_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.AssignedIntegerCallable.static_inputs
/-- info: 'Solidity.Lowering.V08.AssignedIntegerCallable.static_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.AssignedIntegerCallable.static_client
/-- info: 'Solidity.Lowering.V08.AssignedIntegerCallable.wrong_source_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.AssignedIntegerCallable.wrong_source_read
/-- info: 'Solidity.Lowering.V08.AssignedIntegerCallable.wrong_target_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.AssignedIntegerCallable.wrong_target_read
/-- info: 'Solidity.Lowering.V08.AssignedIntegerCallable.skipped_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.AssignedIntegerCallable.skipped_write
/-- info: 'Solidity.Lowering.V08.AssignedIntegerCallable.reached_timeout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.AssignedIntegerCallable.reached_timeout
/-- info: 'Solidity.Lowering.V08.AssignedIntegerCallable.zero_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.AssignedIntegerCallable.zero_horizon
/-- info: 'Solidity.Lowering.V08.AssignedIntegerCallable.unsigned_inputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.AssignedIntegerCallable.unsigned_inputs
/-- info: 'Solidity.Lowering.V08.AssignedIntegerCallable.unsigned_maximum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.AssignedIntegerCallable.unsigned_maximum
/-- info: 'Solidity.Lowering.V08.AssignedIntegerCallable.closed_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.AssignedIntegerCallable.closed_boundary
/-- info: 'Solidity.Lowering.V08.AssignedIntegerCallable.payload_clients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.AssignedIntegerCallable.payload_clients
/-- info: 'Solidity.Lowering.V08.AssignedIntegerCallable.populated_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.AssignedIntegerCallable.populated_fields
end Solidity.Lowering.V08.AssignedIntegerCallable


/-! Reached caller alignment for actual assignment-argument execution.
R relates initial VALUES and contains no execution/preservation premise.
Published ContextMap positions prevent binding collapse; canonical extraction,
heap alias meaning, callee compilation and external/runtime frames stay open. -/
namespace Solidity.Lowering.V08.AssignedCallableContext
open Solidity Source
open Solidity.Lowering.V07
variable {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}

theorem transport (g : Source.Glob E) (f : Source.Fr) (decl : Source.Decl)
    (t : Source.IntTy) (selected : IntegerCallable.Inputs g f decl t) (extra : Nat)
    (i a : Source.Idx srcΓ (.int t)) (j b : Idx Γ (.val (integerPrim t)))
    (locals : Source.Locals E.layout srcΓ) (source : Source.St E) (target : State C Γ)
    (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (initial : m.Related R locals target.env)
    (writeMap : m.slot i = ⟨.val (integerPrim t),j⟩)
    (readMap : m.slot a = ⟨.val (integerPrim t),b⟩)
    (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi)
    (sourceRead : locals.get a = .int n h) (targetRead : TEnv.get b target.env = integerValue t n h) :
    (Source.evalE g f (extra+13) (.call decl selected.signature (AssignedIntegerCallable.arguments t i a))).run
      (locals,source) = (.ok (.val (.int n h)),(locals.set i (.int n h),source)) ∧
    (assignLocalOperand j b).run target =
      .ok (⟨target.setLocal j (integerValue t n h),List.prefix_refl _⟩,.prim (integerValue t n h)) ∧
    IntValueRel t (.int n h : Source.Val E.layout (.int t)) (integerValue t n h) ∧
    m.Related R (locals.set i (.int n h)) (target.setLocal j (integerValue t n h)).env ∧
    (target.setLocal j (integerValue t n h)).glob = target.glob := by
  have actual := AssignedIntegerCallable.transport g f decl t selected extra i a j b locals source target n h sourceRead targetRead
  have reached : m.Related R (locals.set i (locals.get a))
      (TEnv.set j (TEnv.get b target.env) target.env) :=
    ContextMap.related_assign m R locals target.env initial i a j b writeMap readMap
  rw [sourceRead,targetRead] at reached
  exact ⟨actual.1,actual.2.1,actual.2.2.1,reached,actual.2.2.2⟩

abbrev t := SignedCallableControls.t
abbrev Src : Source.RCtx := [.int t,.bool,.int t]
abbrev Dst : Ctx := [.val .uint,.val (integerPrim t),.val .bool,.val (integerPrim t)]

def slots : ContextMap Src Dst :=
  (((ContextMap.empty.cons (.int t) (.val (integerPrim t))).cons .bool (.val .bool)).cons
    (.int t) (.val (integerPrim t))).wk (Thin.drop .refl)

/-- Nontrivial numeric/Boolean witness relation; unsupported shapes are false.
The generic transport above does not restrict a future producer's value relation. -/
def Values {C : Contract} {H : HTy} (τ : Source.STy) (u : LTy)
    (sv : Source.Val SignedCallableControls.E.layout τ) (tv : u.TDenote C H) : Prop :=
  match τ,u with
  | .int _,.val _ => sv.key = PrimTy.num? tv
  | .bool,.val .bool => sv = .bool tv
  | _,_ => False

def target {C : Contract} (base : State C []) (old rhs : Int)
    (ho : t.lo ≤ old ∧ old ≤ t.hi) (hr : t.lo ≤ rhs ∧ rhs ≤ t.hi) : State C Dst :=
  (((base.push (t:=.val (integerPrim t)) (integerValue t rhs hr)).push (t:=.val .bool) false).push
    (t:=.val (integerPrim t)) (integerValue t old ho)).push (t:=.val .uint) EffectfulCallableArgument.live

def operand {C : Contract} : DeferredSource.Operand C Dst (.prim (integerPrim t)) :=
  assignLocalOperand (.there .here) (.there (.there (.there .here)))

theorem initial_alignment {C : Contract} (base : State C []) (old rhs : Int)
    (ho : t.lo ≤ old ∧ old ≤ t.hi) (hr : t.lo ≤ rhs ∧ rhs ≤ t.hi) :
    slots.Related Values (AssignedIntegerCallable.sourceLocals old rhs ho hr) (target base old rhs ho hr).env := by
  intro τ i
  cases i with
  | here => exact integer_related t old ho
  | there i => cases i with
    | here => rfl
    | there i => cases i with
      | here => exact integer_related t rhs hr
      | there i => cases i

theorem client {C : Contract} (base : State C []) (p : Roadmap.Pipeline) (extra : Nat)
    (bytes : Roadmap.Bytes) (old rhs : Int)
    (ho : t.lo ≤ old ∧ old ≤ t.hi) (hr : t.lo ≤ rhs ∧ rhs ≤ t.hi) :
    (Source.evalE (SignedCallableControls.global p) SignedCallableControls.frame (extra+13)
      (.call SignedCallableControls.declaration (SignedCallableControls.inputs p).signature
        (AssignedIntegerCallable.arguments t .here (.there (.there .here))))).run
      (AssignedIntegerCallable.sourceLocals old rhs ho hr,SignedCallableControls.populated bytes) =
      (.ok (.val (.int rhs hr)),(AssignedIntegerCallable.sourceLocals rhs rhs hr hr,SignedCallableControls.populated bytes)) ∧
    operand.run (target base old rhs ho hr) =
      .ok (⟨(target base old rhs ho hr).setLocal (.there .here) (integerValue t rhs hr),List.prefix_refl _⟩,.prim (integerValue t rhs hr)) ∧
    IntValueRel t (.int rhs hr : Source.Val SignedCallableControls.E.layout (.int t)) (integerValue t rhs hr) ∧
    slots.Related Values (AssignedIntegerCallable.sourceLocals rhs rhs hr hr)
      ((target base old rhs ho hr).setLocal (.there .here) (integerValue t rhs hr)).env ∧
    ((target base old rhs ho hr).setLocal (.there .here) (integerValue t rhs hr)).glob = (target base old rhs ho hr).glob :=
  transport _ _ _ _ (SignedCallableControls.inputs p) extra .here (.there (.there .here))
    (.there .here) (.there (.there (.there .here))) _ _ _ slots Values
    (initial_alignment base old rhs ho hr) rfl rfl rhs hr rfl rfl

def vector {C : Contract} (state : State C Dst) : Option Int × Option Int × Bool × Option Int :=
  (PrimTy.num? (TEnv.get (.here : Idx Dst (.val .uint)) state.env),
   PrimTy.num? (TEnv.get (.there .here : Idx Dst (.val (integerPrim t))) state.env),
   TEnv.get (.there (.there .here) : Idx Dst (.val .bool)) state.env,
   PrimTy.num? (TEnv.get (.there (.there (.there .here)) : Idx Dst (.val (integerPrim t))) state.env))

theorem actual_vector {C : Contract} (base : State C []) (old rhs : Int)
    (ho : t.lo ≤ old ∧ old ≤ t.hi) (hr : t.lo ≤ rhs ∧ rhs ≤ t.hi) :
    (operand.run (target base old rhs ho hr)).toOption.map (fun result => vector result.1.st) =
      some (some 42,some rhs,false,some rhs) := by
  rfl

theorem wrong_source_snapshot {C : Contract} (base : State C []) :
    ¬ slots.Related Values
      (AssignedIntegerCallable.sourceLocals 127 (-128) (by decide +kernel) (by decide +kernel))
      ((target base 127 (-128) (by decide +kernel) (by decide +kernel)).setLocal
        (.there .here) (integerValue t (-128) (by decide +kernel))).env := by
  intro relation
  have wrong := relation (.here : Source.Idx Src (.int t))
  change some (127 : Int) = some (-128 : Int) at wrong
  cases wrong

/-- Actual extra target-local mutation, not a guessed alternate outcome. -/
def corruptLive {C : Contract} : Prog C Dst Dst :=
  .cons (.assignLocal (.there (.there .here)) (.simple (.bool true))) .nil

theorem corrupt_live_run {C : Contract} (state : State C Dst) :
    corruptLive.run state = .ok ⟨state.setLocal (.there (.there .here)) true,List.prefix_refl _⟩ := by
  rfl

theorem wrong_live_binding {C : Contract} (base : State C []) :
    ¬ slots.Related Values
      (AssignedIntegerCallable.sourceLocals (-128) (-128) (by decide +kernel) (by decide +kernel))
      (((target base 127 (-128) (by decide +kernel) (by decide +kernel)).setLocal
        (.there .here) (integerValue t (-128) (by decide +kernel))).setLocal (.there (.there .here)) true).env := by
  intro relation
  have wrong := relation (.there .here : Source.Idx Src .bool)
  cases wrong


def corruptExecution {C : Contract} (base : State C []) :
    TRes ((Option Int × Option Int × Bool × Option Int) × Option Int) := do
  let (out,value) ← operand.run (target base 127 (-128) (by decide +kernel) (by decide +kernel))
  let damaged ← corruptLive.run out.st
  pure (vector damaged.st,match value with | .prim v => PrimTy.num? v)

theorem corrupt_actual {C : Contract} (base : State C []) :
    corruptExecution base = .ok ((some 42,some (-128),true,some (-128)),some (-128)) := by
  rfl

theorem closed_client (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    AssignedIntegerCallable.closedSource p bytes =
      (.ok (.val (.int (-128) (by decide +kernel))),
        (AssignedIntegerCallable.sourceLocals (-128) (-128) (by decide +kernel) (by decide +kernel),SignedCallableControls.populated bytes)) ∧
    operand.run (target ConstructorScalarTransport.entered 127 (-128) (by decide +kernel) (by decide +kernel)) =
      .ok (⟨(target ConstructorScalarTransport.entered 127 (-128) (by decide +kernel) (by decide +kernel)).setLocal
        (.there .here) (integerValue t (-128) (by decide +kernel)),List.prefix_refl _⟩,.prim (integerValue t (-128) (by decide +kernel))) ∧
    slots.Related Values (AssignedIntegerCallable.sourceLocals (-128) (-128) (by decide +kernel) (by decide +kernel))
      ((target ConstructorScalarTransport.entered 127 (-128) (by decide +kernel) (by decide +kernel)).setLocal
        (.there .here) (integerValue t (-128) (by decide +kernel))).env := by
  have actual := client ConstructorScalarTransport.entered p 0 bytes 127 (-128) (by decide +kernel) (by decide +kernel)
  exact ⟨actual.1,actual.2.1,actual.2.2.2.1⟩

/-- info: 'Solidity.Lowering.V08.AssignedCallableContext.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.AssignedCallableContext.transport
/-- info: 'Solidity.Lowering.V08.AssignedCallableContext.initial_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.AssignedCallableContext.initial_alignment
/-- info: 'Solidity.Lowering.V08.AssignedCallableContext.client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.AssignedCallableContext.client
/-- info: 'Solidity.Lowering.V08.AssignedCallableContext.actual_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.AssignedCallableContext.actual_vector
/-- info: 'Solidity.Lowering.V08.AssignedCallableContext.wrong_source_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.AssignedCallableContext.wrong_source_snapshot
/-- info: 'Solidity.Lowering.V08.AssignedCallableContext.corrupt_live_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.AssignedCallableContext.corrupt_live_run
/-- info: 'Solidity.Lowering.V08.AssignedCallableContext.wrong_live_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.AssignedCallableContext.wrong_live_binding
/-- info: 'Solidity.Lowering.V08.AssignedCallableContext.corrupt_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.AssignedCallableContext.corrupt_actual
/-- info: 'Solidity.Lowering.V08.AssignedCallableContext.closed_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.AssignedCallableContext.closed_client
end Solidity.Lowering.V08.AssignedCallableContext
