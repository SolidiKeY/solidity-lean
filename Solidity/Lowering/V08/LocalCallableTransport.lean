import Solidity.Lowering.V08.SignedCallableControls
import Solidity.Lowering.V07.Operands

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
