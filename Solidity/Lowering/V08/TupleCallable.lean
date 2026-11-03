import Solidity.Lowering.V08.PureArgumentCallable

/-! G20 ordered two-argument/two-result callable transport. Existing Source
retTuple/mkRet, typed intrinsic locals and actual Prog execution are used.
No ABI tuple codec or external-call semantics. Canonical body/admission/frame
mapping remains separate. Different signedness/widths retain distinct types. -/
namespace Solidity.Lowering.V08.TupleCallable
open Solidity Source
open Solidity.Lowering.V07
abbrev L : Source.STy := .int SignedCallableControls.t
abbrev R : Source.STy := .int Source.IntTy.u256
abbrev leftRange (n : Int) := SignedCallableControls.t.lo ≤ n ∧ n ≤ SignedCallableControls.t.hi
abbrev rightRange (n : Int) := Source.IntTy.u256.lo ≤ n ∧ n ≤ Source.IntTy.u256.hi

def params : Syn (.list .param) :=
  .cons (.param SignedCallableControls.intSyntax none (some "left"))
    (.cons (.param Source.Examples.u256 none (some "right")) .nil)
def returns : Syn (.list .param) :=
  .cons (.param SignedCallableControls.intSyntax none (some "first"))
    (.cons (.param Source.Examples.u256 none (some "second")) .nil)
def fnSyntax : Syn (.part false) :=
  .function (.ident "pair") params (some .pub) none .nil false none returns
    (.some (.block (.cons (.stmtItem (.returnStmt
      (.some (.tuple (.some (.ident "left")) (.cons (.some (.ident "right")) .nil))))) .nil)))
def unit : Syn .unit := .unit (.cons (.contract false "C" .none .nil
  (.cons ScalarCallableTransport.savedSyntax (.cons ScalarCallableTransport.scratchSyntax
    (.cons fnSyntax .nil)))) .nil)
def E : Source.Env := unit.env
def declaration : Source.Decl := ⟨.function,"pair",some "C",false,fnSyntax⟩
def left (n : Int) (h : leftRange n) : Source.Val E.layout L := .int n h
def right (n : Int) (h : rightRange n) : Source.Val E.layout R := .int n h

def sourceBody : Source.RBody E :=
  ⟨[L,R],[L,R],false,[R,L,R,L],[R,L,R,L],
    .stmt (.retTuple (.cons (.local (.there (.there (.there .here)))) rfl
      (.cons (.local (.there (.there .here))) rfl .nil))) .nil,[]⟩
def program : Source.Program E :=
  {body:=fun _ => some sourceBody,consts:=fun _ => none,inits:=fun _ => [],ctor:=fun _ => none,
    ctorLocals:=fun _ => [],baseArgs:=fun _ => [],contracts:=["C"]}
def global (p : Roadmap.Pipeline) : Source.Glob E :=
  {prog:=program,pipeline:=p,fixed:=Source.SemanticsExamples.toyFixed,
    balance0:=fun _ => ScalarCallableTransport.word 93,hasCode:=fun _ _ => false,
    callee:=fun _ => .answer (.success []),timestamp:=ScalarCallableTransport.word 12345}
abbrev frame := ScalarCallableTransport.frame

def populated (bytes : Roadmap.Bytes) : Source.St E :=
  {Source.St.init E with
    ex:=(Source.St.init E).ex.run [
      .account frame.sender (fun a => {a with balance:=ScalarCallableTransport.word 93,nonce:=3}),
      .account frame.this (fun a => {a with balance:=ScalarCallableTransport.word 12,nonce:=1,code:=some 0,storage:=a.storage.write ScalarCallableTransport.saved.path (.int 42 (by decide +kernel))}),
      .transient frame.this (fun a => a.write ScalarCallableTransport.scratch.path (.int 9 (by decide +kernel))),
      .transient frame.sender (fun a => a.write ScalarCallableTransport.scratch.path (.int 17 (by decide +kernel)))]
    heap:=((Source.Heap.empty.alloc ⟨.bytes .memory,.bytes bytes⟩).1.alloc ⟨.bytes .memory,.bytes [128,255]⟩).1
    events:=[.call frame.sender (ScalarCallableTransport.word 7) bytes false]
    logs:=[(frame.this,bytes),(frame.sender,[0xab,0,255])]
    fnLocals:=⟨[.bool],.cons (.bool true) .nil⟩}

theorem signature : declaration.fnSig E = some ([L,R],[L,R]) := rfl

def values (x y : Int) (hx : leftRange x) (hy : rightRange y) : Source.Vals E.layout [L,R] :=
  .cons (left x hx) (.cons (right y hy) .nil)
def outputs (x y : Int) (hx : leftRange x) (hy : rightRange y) : Source.RVals E.layout [L,R] :=
  .cons (.val (left x hx)) (.cons (.val (right y hy)) .nil)
def returned (x y : Int) (hx : leftRange x) (hy : rightRange y) : Source.Locals E.layout [R,L,R,L] :=
  .cons (right y hy) (.cons (left x hx) (.cons (right y hy) (.cons (left x hx) .nil)))

theorem internal_actual (g : Source.Glob E) (f : Source.Fr) (extra : Nat) (state : Source.St E)
    (selected : g.prog.body (g.dispatchFn f.contract declaration) = some sourceBody)
    (x y : Int) (hx : leftRange x) (hy : rightRange y) :
    (Source.callInternal g f (extra+32) declaration (values x y hx hy) [L,R]).run (Source.L0 E,state) =
      (.ok (.tuple (outputs x y hx hy)),(Source.L0 E,state)) :=
  SourceCallable.complete g f (extra+31) declaration (values x y hx hy) sourceBody selected
    (.cons (left 0 (by decide +kernel)) (.cons (right 0 (by decide +kernel)) .nil)) rfl
    (returned x y hx hy) (outputs x y hx hy) state state state (by rfl) (by rfl) rfl

variable {srcΓ : Source.RCtx}
def arguments (i : Source.Idx srcΓ L) (j : Source.Idx srcΓ R) : Source.RConvArgs E srcΓ [L,R] :=
  .cons (.local i) rfl (.cons (.local j) rfl .nil)

theorem arguments_actual (g : Source.Glob E) (f : Source.Fr) (extra : Nat)
    (i : Source.Idx srcΓ L) (j : Source.Idx srcΓ R) (locals : Source.Locals E.layout srcΓ)
    (state : Source.St E) (x y : Int) (hx : leftRange x) (hy : rightRange y)
    (readLeft : locals.get i = left x hx) (readRight : locals.get j = right y hy) :
    (Source.evalConvArgs g f (extra+32) (arguments i j)).run (locals,state) =
      (.ok (values x y hx hy),(locals,state)) := by
  simp only [arguments,Source.evalConvArgs,Source.evalE,IntegerCallable.conversion_identity,
    Source.getV,Source.RVal.get,Source.EM.locals,bind,pure,ExceptT.run,ExceptT.bind,
    ExceptT.pure,
    get,getThe,MonadStateOf.get,liftM,
    monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,Source.EM.lift]
  simp only [ExceptT.mk,bind,pure,StateT.bind,StateT.pure,StateT.get,
    StateT.map,Except.pure,ExceptT.bindCont,readLeft,readRight,left,right,values]

theorem expression_actual (g : Source.Glob E) (f : Source.Fr) (extra : Nat)
    (selected : g.prog.body (g.dispatchFn f.contract declaration) = some sourceBody)
    (i : Source.Idx srcΓ L) (j : Source.Idx srcΓ R) (locals : Source.Locals E.layout srcΓ)
    (state : Source.St E) (x y : Int) (hx : leftRange x) (hy : rightRange y)
    (readLeft : locals.get i = left x hx) (readRight : locals.get j = right y hy) :
    (Source.evalE g f (extra+33) (.call declaration signature (arguments i j))).run (locals,state) =
      (.ok (.tuple (outputs x y hx hy)),(locals,state)) :=
  SourceCallable.expression_complete g f (extra+32) declaration signature (arguments i j)
    locals locals (values x y hx hy) (.tuple (outputs x y hx hy)) state state state
    (arguments_actual g f extra i j locals state x y hx hy readLeft readRight)
    (internal_actual g f extra state selected x y hx hy)

variable {Γ : Ctx} {C : Contract}
def body (i : Idx Γ (.val .int)) (j : Idx Γ (.val .uint)) : Prog C Γ (.val .uint :: .val .int :: Γ) :=
  .cons (.declLocal .int (.user "left") (some (.simple (.local i))))
    (.cons (.declLocal .uint (.user "right") (some (.simple (.local (.there j))))) .nil)
def result (state : State C (.val .uint :: .val .int :: Γ)) : TRes (PrimTy.int.Denote × PrimTy.uint.Denote) := do
  let a ← (Solidity.Val.simple (.local (.there .here)) : Solidity.Val C _ .int).evalT state
  let b ← (Solidity.Val.simple (.local .here) : Solidity.Val C _ .uint).evalT state
  pure (a,b)

theorem body_actual (i : Idx Γ (.val .int)) (j : Idx Γ (.val .uint)) (state : State C Γ) :
    (body i j).run state = .ok ⟨(state.push (t:=.val .int) (TEnv.get i state.env)).push
      (t:=.val .uint) (TEnv.get j state.env),List.prefix_refl _⟩ := rfl

theorem result_actual (state : State C Γ) (a : PrimTy.int.Denote) (b : PrimTy.uint.Denote) :
    result ((state.push (t:=.val .int) a).push (t:=.val .uint) b) = .ok (a,b) := rfl

theorem caller_restored (i : Idx Γ (.val .int)) (j : Idx Γ (.val .uint)) (state : State C Γ) :
    ((state.push (t:=.val .int) (TEnv.get i state.env)).push (t:=.val .uint) (TEnv.get j state.env)).drop
      (body (C:=C) i j).ext = state := rfl

/-- Observation of the actual run, preserving its outer status and exact
inner result status. This is not another callable/world evaluator. -/
def observeBody (i : Idx Γ (.val .int)) (j : Idx Γ (.val .uint)) (state : State C Γ) :=
  ((body i j).run state).map (fun out => (out.st.drop (body (C:=C) i j).ext,result out.st))

theorem observed_actual (i : Idx Γ (.val .int)) (j : Idx Γ (.val .uint)) (state : State C Γ) :
    observeBody i j state = .ok (state,.ok (TEnv.get i state.env,TEnv.get j state.env)) := by
  rw [observeBody,body_actual]
  rfl

theorem transport (g : Source.Glob E) (f : Source.Fr) (extra : Nat)
    (selected : g.prog.body (g.dispatchFn f.contract declaration) = some sourceBody)
    (i : Source.Idx srcΓ L) (j : Source.Idx srcΓ R) (locals : Source.Locals E.layout srcΓ)
    (source : Source.St E) (target : State C Γ) (ti : Idx Γ (.val .int)) (tj : Idx Γ (.val .uint))
    (x y : Int) (hx : leftRange x) (hy : rightRange y)
    (sourceLeft : locals.get i = left x hx) (sourceRight : locals.get j = right y hy)
    (targetLeft : TEnv.get ti target.env = integerValue SignedCallableControls.t x hx)
    (targetRight : TEnv.get tj target.env = integerValue Source.IntTy.u256 y hy) :
    (Source.evalE g f (extra+33) (.call declaration signature (arguments i j))).run (locals,source) =
      (.ok (.tuple (outputs x y hx hy)),(locals,source)) ∧
    observeBody ti tj target = .ok (target,.ok (integerValue SignedCallableControls.t x hx,
      integerValue Source.IntTy.u256 y hy)) ∧
    IntValueRel SignedCallableControls.t (left x hx) (integerValue SignedCallableControls.t x hx) ∧
    IntValueRel Source.IntTy.u256 (right y hy) (integerValue Source.IntTy.u256 y hy) := by
  refine ⟨expression_actual g f extra selected i j locals source x y hx hy sourceLeft sourceRight,?_,
    integer_related _ x hx,integer_related _ y hy⟩
  rw [observed_actual,targetLeft,targetRight]

def sourceCaller (x y : Int) (hx : leftRange x) (hy : rightRange y) :
    Source.Locals E.layout [L,R,.bool,L] :=
  .cons (left x hx) (.cons (right y hy) (.cons (.bool true) (.cons (left (-1) (by decide +kernel)) .nil)))
def targetCaller (base : State C []) (x y : Int) (hx : leftRange x) (hy : rightRange y) :
    State C [.val .int,.val .uint,.val .bool,.val .int] :=
  (((base.push (t:=.val .int) (integerValue SignedCallableControls.t (-1) (by decide +kernel))).push
    (t:=.val .bool) true).push (t:=.val .uint) (integerValue Source.IntTy.u256 y hy)).push
      (t:=.val .int) (integerValue SignedCallableControls.t x hx)

theorem populated_client (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes)
    (x y : Int) (hx : leftRange x) (hy : rightRange y) :
    (Source.evalE (global p) frame (extra+33) (.call declaration signature
      (arguments .here (.there .here)))).run (sourceCaller x y hx hy,populated bytes) =
      (.ok (.tuple (outputs x y hx hy)),(sourceCaller x y hx hy,populated bytes)) ∧
    observeBody .here (.there .here) (targetCaller ConstructorScalarTransport.entered x y hx hy) =
      .ok (targetCaller ConstructorScalarTransport.entered x y hx hy,
        .ok (integerValue SignedCallableControls.t x hx,integerValue Source.IntTy.u256 y hy)) := by
  have complete := transport (global p) frame extra rfl .here (.there .here)
    (sourceCaller x y hx hy) (populated bytes) (targetCaller ConstructorScalarTransport.entered x y hx hy)
    .here (.there .here) x y hx hy rfl rfl rfl rfl
  exact ⟨complete.1,complete.2.1⟩

theorem wrong_target_slot (base : State C []) :
    observeBody .here (.there .here) (targetCaller base (-128) 7 (by decide +kernel) (by decide +kernel)) ≠
    observeBody (.there (.there (.there .here))) (.there .here)
      (targetCaller base (-128) 7 (by decide +kernel) (by decide +kernel)) := by
  rw [observed_actual,observed_actual]
  intro same
  have number := congrArg (fun r => r.toOption.bind (fun out => out.2.toOption.map (fun pair => pair.1.1))) same
  change some (-128 : Int) = some (-1) at number
  cases number

theorem wrong_result_order :
    (observeBody .here (.there .here) (targetCaller ConstructorScalarTransport.entered (-128) 7
      (by decide +kernel) (by decide +kernel))).map
      (fun out => out.2.toOption.map (fun pair => (pair.1.1,pair.2.1))) ≠ .ok (some (7,-128)) := by
  rw [observed_actual]
  change (Except.ok (some ((-128 : Int),7)) : TRes (Option (Int × Int))) ≠ .ok (some (7,-128))
  intro same
  cases same

theorem wrong_source_slot (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global p) frame 33 (.call declaration signature (arguments .here (.there .here)))).run
      (sourceCaller (-128) 7 (by decide +kernel) (by decide +kernel),populated bytes) ≠
    (Source.evalE (global p) frame 33 (.call declaration signature
      (arguments (.there (.there (.there .here))) (.there .here)))).run
      (sourceCaller (-128) 7 (by decide +kernel) (by decide +kernel),populated bytes) := by
  rw [expression_actual (global p) frame 0 rfl .here (.there .here) _ _ (-128) 7
        (by decide +kernel) (by decide +kernel) rfl rfl,
      expression_actual (global p) frame 0 rfl (.there (.there (.there .here))) (.there .here) _ _ (-1) 7
        (by decide +kernel) (by decide +kernel) rfl rfl]
  intro same
  cases same

theorem zero_horizon (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (global p) frame 0 (.call declaration signature (arguments .here (.there .here)))).run
      (sourceCaller (-128) 7 (by decide +kernel) (by decide +kernel),populated bytes) =
      (.error .timeout,(sourceCaller (-128) 7 (by decide +kernel) (by decide +kernel),populated bytes)) := rfl

/-- info: 'Solidity.Lowering.V08.TupleCallable.signature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.TupleCallable.signature

/-- info: 'Solidity.Lowering.V08.TupleCallable.internal_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.TupleCallable.internal_actual

/-- info: 'Solidity.Lowering.V08.TupleCallable.arguments_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.TupleCallable.arguments_actual

/-- info: 'Solidity.Lowering.V08.TupleCallable.expression_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.TupleCallable.expression_actual

/-- info: 'Solidity.Lowering.V08.TupleCallable.body_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.TupleCallable.body_actual

/-- info: 'Solidity.Lowering.V08.TupleCallable.result_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.TupleCallable.result_actual

/-- info: 'Solidity.Lowering.V08.TupleCallable.caller_restored' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.TupleCallable.caller_restored

/-- info: 'Solidity.Lowering.V08.TupleCallable.observed_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.TupleCallable.observed_actual

/-- info: 'Solidity.Lowering.V08.TupleCallable.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.TupleCallable.transport

/-- info: 'Solidity.Lowering.V08.TupleCallable.populated_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.TupleCallable.populated_client

/-- info: 'Solidity.Lowering.V08.TupleCallable.wrong_target_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.TupleCallable.wrong_target_slot

/-- info: 'Solidity.Lowering.V08.TupleCallable.wrong_result_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.TupleCallable.wrong_result_order

/-- info: 'Solidity.Lowering.V08.TupleCallable.wrong_source_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.TupleCallable.wrong_source_slot

/-- info: 'Solidity.Lowering.V08.TupleCallable.zero_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.TupleCallable.zero_horizon
end Solidity.Lowering.V08.TupleCallable
