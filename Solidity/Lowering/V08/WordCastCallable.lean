import Solidity.Lowering.V08.LocalCallableTransport
import Solidity.Lowering.V07.WordCasts

/-! Signed assignment/cast arguments feeding an actual Source uint echo.
The published V07 operand preserves the RAW signed caller write while returning
the converted unsigned value. No target callee, heap/world/frame or admission
compiler is supplied. Bounds are intrinsic integer bounds, not an admission cutoff. -/
namespace Solidity.Lowering.V08.WordCastCallable
open Solidity Source
open Solidity.Lowering.V07
variable {E : Source.Env} {srcΓ : Source.RCtx}

def arguments (i a : Source.Idx srcΓ (.int WordCasts.signed)) :
    Source.RConvArgs E srcΓ [.int Source.IntTy.u256] :=
  .cons (.convExplicit (τ:=.int Source.IntTy.u256)
    (.assign (.local i) (.local a)) (by rfl))
    (IntegerCallable.implicit_identity Source.IntTy.u256) .nil

theorem argument_actual (g : Source.Glob E) (f : Source.Fr) (extra : Nat)
    (i a : Source.Idx srcΓ (.int WordCasts.signed))
    (locals : Source.Locals E.layout srcΓ) (source : Source.St E)
    (x : Int) (bound : WordCasts.signed.lo ≤ x ∧ x ≤ WordCasts.signed.hi)
    (read : locals.get a = .int x bound) :
    (Source.evalConvArgs g f (extra+13) (arguments i a)).run (locals,source) =
      (.ok (.cons (Source.intWrap Source.IntTy.u256 x) .nil),
        (locals.set i (.int x bound),source)) := by
  simp only [arguments,Source.evalConvArgs,IntegerCallable.conversion_identity]
  rw [Source.Hoare.run_bind,
    WordCasts.source_to_uint g f (extra+11) (locals,source) _ _ x bound
      (source_assign_local_run g f (extra+9) (locals,source) i a _ read)]
  rfl


theorem source_expression (g : Source.Glob E) (f : Source.Fr) (decl : Source.Decl)
    (selected : IntegerCallable.Inputs g f decl Source.IntTy.u256) (extra : Nat)
    (i a : Source.Idx srcΓ (.int WordCasts.signed))
    (locals : Source.Locals E.layout srcΓ) (source : Source.St E)
    (x : Int) (bound : WordCasts.signed.lo ≤ x ∧ x ≤ WordCasts.signed.hi)
    (read : locals.get a = .int x bound) :
    (Source.evalE g f (extra+14) (.call decl selected.signature (arguments i a))).run (locals,source) =
      (.ok (.val (Source.intWrap Source.IntTy.u256 x)),(locals.set i (.int x bound),source)) := by
  exact SourceCallable.expression_complete g f (extra+13) decl selected.signature (arguments i a)
    locals (locals.set i (.int x bound)) (.cons (Source.intWrap Source.IntTy.u256 x) .nil)
    (.val (Source.intWrap Source.IntTy.u256 x)) source source source
    (argument_actual g f extra i a locals source x bound read)
    (IntegerCallable.source_call g f decl Source.IntTy.u256 selected (extra+1) source
      (Source.IntTy.u256.wrap x) (Source.IntTy.u256.wrap_mem x))


/-- Initial values and alias reflection, not a desired post relation, supply
both the actual cast operand and its reached numeric caller relation. -/
theorem transport {C : Contract} {Γ : Ctx} {ι : Type}
    (g : Source.Glob E) (f : Source.Fr) (decl : Source.Decl)
    (selected : IntegerCallable.Inputs g f decl Source.IntTy.u256) (extra : Nat)
    (locals : Source.Locals E.layout srcΓ) (source : Source.St E) (target : State C Γ)
    (si : ι → Source.Idx srcΓ (.int WordCasts.signed)) (ti : ι → Idx Γ (.val .int))
    (family : IntegerLocalFamily WordCasts.signed si ti locals target.env)
    (i a : ι) (x : Int) (bound : WordCasts.signed.lo ≤ x ∧ x ≤ WordCasts.signed.hi)
    (read : locals.get (si a) = .int x bound) :
    (Source.evalE g f (extra+14) (.call decl selected.signature (arguments (si i) (si a)))).run
      (locals,source) = (.ok (.val (Source.intWrap Source.IntTy.u256 x)),
        (locals.set (si i) (.int x bound),source)) ∧
    (WordCasts.assignedToUint (ti i) (ti a)).run target =
      .ok (⟨target.setLocal (ti i) (integerValue WordCasts.signed x bound),List.prefix_refl _⟩,
        .prim (integerValue Source.IntTy.u256 (Source.IntTy.u256.wrap x) (Source.IntTy.u256.wrap_mem x))) ∧
    IntValueRel Source.IntTy.u256 (Source.intWrap Source.IntTy.u256 x : Source.Val E.layout _)
      (integerValue Source.IntTy.u256 (Source.IntTy.u256.wrap x) (Source.IntTy.u256.wrap_mem x)) ∧
    IntegerLocalFamily WordCasts.signed si ti (locals.set (si i) (.int x bound))
      (target.setLocal (ti i) (integerValue WordCasts.signed x bound)).env := by
  have actual := WordCasts.assignment_to_uint_transport g f (extra+9) (locals,source) target
    si ti family i a x bound read
  exact ⟨source_expression g f decl selected extra (si i) (si a) locals source x bound read,
    actual.2.1,actual.2.2.1,actual.2.2.2⟩


namespace Controls
abbrev fixtureEnv := ScalarCallableTransport.E
abbrev t := WordCasts.signed
abbrev range (x : Int) := t.lo ≤ x ∧ x ≤ t.hi
abbrev Src : Source.RCtx := [.int t,.bool,.int t]
abbrev Dst : Ctx := [.val .uint,.val .int,.val .bool,.val .int]
def si (k : Bool) : Source.Idx Src (.int t) := if k then .there (.there .here) else .here
def ti (k : Bool) : Idx Dst (.val .int) := if k then .there (.there (.there .here)) else .there .here

def locals (old x : Int) (ho : range old) (hx : range x) : Source.Locals fixtureEnv.layout Src :=
  .cons (.int old ho) (.cons (.bool false) (.cons (.int x hx) .nil))
def target {C : Contract} (base : State C []) (old x : Int) (ho : range old) (hx : range x) :
    State C Dst :=
  (((base.push (t:=.val .int) (integerValue t x hx)).push (t:=.val .bool) false).push
    (t:=.val .int) (integerValue t old ho)).push (t:=.val .uint) EffectfulCallableArgument.live

theorem initial_family {C : Contract} (base : State C []) (old x : Int) (ho : range old) (hx : range x) :
    IntegerLocalFamily t si ti (locals old x ho hx) (target base old x ho hx).env := by
  refine ⟨?_,?_⟩
  · intro k
    cases k with
    | false => exact integer_related t old ho
    | true => exact integer_related t x hx
  · intro k l
    cases k <;> cases l <;> decide +kernel


def expression (p : Roadmap.Pipeline) : Source.RExpr fixtureEnv Src (.int Source.IntTy.u256) :=
  .call ScalarCallableTransport.declaration (AssignedIntegerCallable.unsigned_inputs p).signature
    (arguments (si false) (si true))

theorem client {C : Contract} (base : State C []) (p : Roadmap.Pipeline) (extra : Nat)
    (bytes : Roadmap.Bytes) (old x : Int) (ho : range old) (hx : range x) :
    (Source.evalE (ScalarCallableTransport.global p) ScalarCallableTransport.frame (extra+14)
      (expression p)).run (locals old x ho hx,ScalarCallableTransport.populated bytes) =
      (.ok (.val (Source.intWrap Source.IntTy.u256 x)),
        ((locals old x ho hx).set (si false) (.int x hx),ScalarCallableTransport.populated bytes)) ∧
    (WordCasts.assignedToUint (ti false) (ti true)).run (target base old x ho hx) =
      .ok (⟨(target base old x ho hx).setLocal (ti false) (integerValue t x hx),List.prefix_refl _⟩,
        .prim (integerValue Source.IntTy.u256 (Source.IntTy.u256.wrap x) (Source.IntTy.u256.wrap_mem x))) ∧
    IntegerLocalFamily t si ti ((locals old x ho hx).set (si false) (.int x hx))
      ((target base old x ho hx).setLocal (ti false) (integerValue t x hx)).env := by
  have actual := transport (ScalarCallableTransport.global p) ScalarCallableTransport.frame
    ScalarCallableTransport.declaration (AssignedIntegerCallable.unsigned_inputs p) extra
    (locals old x ho hx) (ScalarCallableTransport.populated bytes) (target base old x ho hx)
    si ti (initial_family base old x ho hx) false true x hx rfl
  exact ⟨actual.1,actual.2.1,actual.2.2.2⟩


def unsignedMax : Int := 2^256-1
def minimum : Int := -(2^255)
def maximum : Int := 2^255-1

theorem boundary_ranges : range (-1) ∧ range minimum ∧ range 0 ∧ range maximum := by decide +kernel

theorem boundary_wraps : Source.IntTy.u256.wrap (-1) = unsignedMax ∧
    Source.IntTy.u256.wrap minimum = 2^255 ∧ Source.IntTy.u256.wrap 0 = 0 ∧
    Source.IntTy.u256.wrap maximum = maximum := by decide +kernel

def observe {C : Contract} (state : State C Dst) : Option Int × Option Int × Bool × Option Int :=
  (PrimTy.num? (TEnv.get (.here : Idx Dst (.val .uint)) state.env),
    PrimTy.num? (TEnv.get (ti false) state.env),TEnv.get (.there (.there .here)) state.env,
    PrimTy.num? (TEnv.get (ti true) state.env))

theorem before_vector {C : Contract} (base : State C []) (old x : Int) (ho : range old) (hx : range x) :
    observe (target base old x ho hx) = (some 42,some old,false,some x) := by
  change (some 42,PrimTy.num? (integerValue t old ho),false,PrimTy.num? (integerValue t x hx)) = _
  rw [integer_observe t old ho,integer_observe t x hx]


theorem written_vector {C : Contract} (base : State C []) (old x : Int) (ho : range old) (hx : range x) :
    observe ((target base old x ho hx).setLocal (ti false) (integerValue t x hx)) =
      (some 42,some x,false,some x) := by
  change (some 42,PrimTy.num? (integerValue t x hx),false,PrimTy.num? (integerValue t x hx)) = _
  rw [integer_observe t x hx]

theorem target_vector {C : Contract} (base : State C []) (old x : Int) (ho : range old) (hx : range x) :
    ((WordCasts.assignedToUint (ti false) (ti true)).run (target base old x ho hx)).toOption.map
      (fun out => (observe out.1.st,match out.2 with | .prim value => PrimTy.num? value)) =
      some ((some 42,some x,false,some x),some (Source.IntTy.u256.wrap x)) := by
  rw [WordCasts.assigned_to_uint_run (target base old x ho hx) (ti false) (ti true) x hx rfl]
  change some ((some 42,PrimTy.num? (integerValue t x hx),false,PrimTy.num? (integerValue t x hx)),
    PrimTy.num? (integerValue Source.IntTy.u256 (Source.IntTy.u256.wrap x) (Source.IntTy.u256.wrap_mem x))) = _
  rw [integer_observe t x hx,integer_observe Source.IntTy.u256 _ _]


/-- Same reached Source machine, but the signed caller cell and unsigned
return value have different numeric observations at -1. -/
theorem negative_one_source (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (ScalarCallableTransport.global p) ScalarCallableTransport.frame 14 (expression p)).run
      (locals 0 (-1) (by decide +kernel) (by decide +kernel),ScalarCallableTransport.populated bytes) =
      (.ok (.val (.int unsignedMax (by decide +kernel))),
        (locals (-1) (-1) (by decide +kernel) (by decide +kernel),ScalarCallableTransport.populated bytes)) := by
  have actual := source_expression (ScalarCallableTransport.global p) ScalarCallableTransport.frame
    ScalarCallableTransport.declaration (AssignedIntegerCallable.unsigned_inputs p) 0
    (si false) (si true) (locals 0 (-1) (by decide +kernel) (by decide +kernel))
    (ScalarCallableTransport.populated bytes) (-1) (by decide +kernel) rfl
  simpa only [Source.intWrap,boundary_wraps.1] using actual


theorem negative_one_vector {C : Contract} (base : State C []) :
    ((WordCasts.assignedToUint (ti false) (ti true)).run
      (target base 0 (-1) (by decide +kernel) (by decide +kernel))).toOption.map
      (fun out => (observe out.1.st,match out.2 with | .prim value => PrimTy.num? value)) =
      some ((some 42,some (-1),false,some (-1)),some unsignedMax) := by
  simpa only [boundary_wraps.1] using target_vector base 0 (-1) (by decide +kernel) (by decide +kernel)


theorem wrong_snapshot {C : Contract} (base : State C []) :
    ¬ IntegerLocalFamily t si ti (locals 0 (-1) (by decide +kernel) (by decide +kernel))
      ((target base 0 (-1) (by decide +kernel) (by decide +kernel)).setLocal (ti false)
        (integerValue t (-1) (by decide +kernel))).env := by
  intro wrong
  have value := wrong.values false
  change some (0 : Int) = some (-1 : Int) at value
  cases value


theorem wrong_return {C : Contract} (base : State C []) :
    (WordCasts.assignedToUint (ti false) (ti true)).run
      (target base 0 (-1) (by decide +kernel) (by decide +kernel)) ≠
      .ok (⟨(target base 0 (-1) (by decide +kernel) (by decide +kernel)).setLocal (ti false)
        (integerValue t (-1) (by decide +kernel)),List.prefix_refl _⟩,
        .prim (integerValue Source.IntTy.u256 0 (by decide +kernel))) := by
  intro wrong
  have value := congrArg (fun result => result.toOption.map
    (fun out => (observe out.1.st,match out.2 with | .prim value => PrimTy.num? value))) wrong
  dsimp only at value
  rw [negative_one_vector] at value
  change some ((some 42,some (-1),false,some (-1)),some unsignedMax) =
    some (observe ((target base 0 (-1) (by decide +kernel) (by decide +kernel)).setLocal
      (ti false) (integerValue t (-1) (by decide +kernel))),
        PrimTy.num? (integerValue Source.IntTy.u256 0 (by decide +kernel))) at value
  rw [written_vector,integer_observe Source.IntTy.u256 0 (by decide +kernel)] at value
  have returns : some unsignedMax = some (0 : Int) := congrArg Prod.snd (Option.some.inj value)
  have different : unsignedMax ≠ 0 := by decide +kernel
  exact different (Option.some.inj returns)

theorem raw_return_distinct {C : Contract} (base : State C []) :
    ((WordCasts.assignedToUint (ti false) (ti true)).run
      (target base 0 (-1) (by decide +kernel) (by decide +kernel))).toOption.map
      (fun out => PrimTy.num? (TEnv.get (ti false) out.1.st.env)) ≠
    ((WordCasts.assignedToUint (ti false) (ti true)).run
      (target base 0 (-1) (by decide +kernel) (by decide +kernel))).toOption.map
      (fun out => match out.2 with | .prim value => PrimTy.num? value) := by
  have vector := negative_one_vector base
  have stored : ((WordCasts.assignedToUint (ti false) (ti true)).run
      (target base 0 (-1) (by decide +kernel) (by decide +kernel))).toOption.map
      (fun out => PrimTy.num? (TEnv.get (ti false) out.1.st.env)) = some (some (-1 : Int)) := by
    have projected := congrArg (fun value => value.map (fun pair => pair.1.2.1)) vector
    simpa only [Option.map_map,observe] using projected
  have returned : ((WordCasts.assignedToUint (ti false) (ti true)).run
      (target base 0 (-1) (by decide +kernel) (by decide +kernel))).toOption.map
      (fun out => match out.2 with | .prim value => PrimTy.num? value) = some (some unsignedMax) := by
    have projected := congrArg (fun value => value.map Prod.snd) vector
    simpa only [Option.map_map] using projected
  rw [stored,returned]
  intro wrong
  have different : (-1 : Int) ≠ unsignedMax := by decide +kernel
  exact different (Option.some.inj (Option.some.inj wrong))

theorem boundary_clients (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    ∀ x ∈ [(-1 : Int),minimum,0,maximum], ∀ hx : range x,
      (Source.evalE (ScalarCallableTransport.global p) ScalarCallableTransport.frame 14 (expression p)).run
        (locals 0 x (by decide +kernel) hx,ScalarCallableTransport.populated bytes) =
        (.ok (.val (Source.intWrap Source.IntTy.u256 x)),
          (locals x x hx hx,ScalarCallableTransport.populated bytes)) := by
  intro x _ hx
  exact source_expression (ScalarCallableTransport.global p) ScalarCallableTransport.frame
    ScalarCallableTransport.declaration (AssignedIntegerCallable.unsigned_inputs p) 0
    (si false) (si true) (locals 0 x (by decide +kernel) hx)
    (ScalarCallableTransport.populated bytes) x hx rfl


theorem payload_clients (p : Roadmap.Pipeline) :
    ∀ bytes ∈ [[],[0,255,128],List.replicate 33 129],
      (Source.evalE (ScalarCallableTransport.global p) ScalarCallableTransport.frame 14 (expression p)).run
        (locals 0 (-1) (by decide +kernel) (by decide +kernel),ScalarCallableTransport.populated bytes) =
        (.ok (.val (.int unsignedMax (by decide +kernel))),
          (locals (-1) (-1) (by decide +kernel) (by decide +kernel),ScalarCallableTransport.populated bytes)) := by
  exact fun bytes _ => negative_one_source p bytes

theorem reached_timeout (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (ScalarCallableTransport.global p) ScalarCallableTransport.frame 5 (expression p)).run
      (locals 0 (-1) (by decide +kernel) (by decide +kernel),ScalarCallableTransport.populated bytes) =
      (.error .timeout,
        (locals (-1) (-1) (by decide +kernel) (by decide +kernel),ScalarCallableTransport.populated bytes)) := by
  rfl

theorem static_execution (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (ScalarCallableTransport.global p) {ScalarCallableTransport.frame with static := true}
      14 (expression p)).run
      (locals 0 (-1) (by decide +kernel) (by decide +kernel),ScalarCallableTransport.populated bytes) =
      (.ok (.val (Source.intWrap Source.IntTy.u256 (-1))),
        (locals (-1) (-1) (by decide +kernel) (by decide +kernel),ScalarCallableTransport.populated bytes)) := by
  exact source_expression (ScalarCallableTransport.global p) {ScalarCallableTransport.frame with static := true}
    ScalarCallableTransport.declaration
    ⟨(AssignedIntegerCallable.unsigned_inputs p).member,(AssignedIntegerCallable.unsigned_inputs p).kind,
      (AssignedIntegerCallable.unsigned_inputs p).signature,rfl⟩ 0
    (si false) (si true) (locals 0 (-1) (by decide +kernel) (by decide +kernel))
    (ScalarCallableTransport.populated bytes) (-1) (by decide +kernel) rfl


/-- Nonempty closed target state supplied by an actual existing entry,
not an arbitrary state equality or an assumed successful action. -/
theorem closed_client (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    ∃ out : Out ConstructorScalarTransport.Cell ConstructorScalarTransport.entered.H Dst × SVal (.prim .uint),
      (Source.evalE (ScalarCallableTransport.global p) ScalarCallableTransport.frame 14 (expression p)).run
        (locals 0 (-1) (by decide +kernel) (by decide +kernel),ScalarCallableTransport.populated bytes) =
        (.ok (.val (.int unsignedMax (by decide +kernel))),
          (locals (-1) (-1) (by decide +kernel) (by decide +kernel),ScalarCallableTransport.populated bytes)) ∧
      (WordCasts.assignedToUint (ti false) (ti true)).run
        (target ConstructorScalarTransport.entered 0 (-1) (by decide +kernel) (by decide +kernel)) = .ok out ∧
      observe out.1.st = (some 42,some (-1),false,some (-1)) ∧
      (match out.2 with | .prim value => PrimTy.num? value) = some unsignedMax := by
  have vector := negative_one_vector ConstructorScalarTransport.entered
  cases executed : (WordCasts.assignedToUint (ti false) (ti true)).run
      (target ConstructorScalarTransport.entered 0 (-1) (by decide +kernel) (by decide +kernel)) with
  | error halt => rw [executed] at vector; cases vector
  | ok out =>
    rw [executed] at vector
    have pair := Option.some.inj vector
    exact ⟨out,negative_one_source p bytes,rfl,congrArg Prod.fst pair,congrArg Prod.snd pair⟩


theorem zero_horizon (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (Source.evalE (ScalarCallableTransport.global p) ScalarCallableTransport.frame 0 (expression p)).run
      (locals 0 (-1) (by decide +kernel) (by decide +kernel),ScalarCallableTransport.populated bytes) =
      (.error .timeout,
        (locals 0 (-1) (by decide +kernel) (by decide +kernel),ScalarCallableTransport.populated bytes)) := by rfl
end Controls
end Solidity.Lowering.V08.WordCastCallable

/-- info: 'Solidity.Lowering.V08.WordCastCallable.argument_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.WordCastCallable.argument_actual
/-- info: 'Solidity.Lowering.V08.WordCastCallable.source_expression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.WordCastCallable.source_expression
/-- info: 'Solidity.Lowering.V08.WordCastCallable.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.WordCastCallable.transport
/-- info: 'Solidity.Lowering.V08.WordCastCallable.Controls.initial_family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.WordCastCallable.Controls.initial_family
/-- info: 'Solidity.Lowering.V08.WordCastCallable.Controls.client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.WordCastCallable.Controls.client
/-- info: 'Solidity.Lowering.V08.WordCastCallable.Controls.boundary_ranges' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.WordCastCallable.Controls.boundary_ranges
/-- info: 'Solidity.Lowering.V08.WordCastCallable.Controls.boundary_wraps' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.WordCastCallable.Controls.boundary_wraps
/-- info: 'Solidity.Lowering.V08.WordCastCallable.Controls.before_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.WordCastCallable.Controls.before_vector
/-- info: 'Solidity.Lowering.V08.WordCastCallable.Controls.written_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.WordCastCallable.Controls.written_vector
/-- info: 'Solidity.Lowering.V08.WordCastCallable.Controls.target_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.WordCastCallable.Controls.target_vector
/-- info: 'Solidity.Lowering.V08.WordCastCallable.Controls.negative_one_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.WordCastCallable.Controls.negative_one_source
/-- info: 'Solidity.Lowering.V08.WordCastCallable.Controls.negative_one_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.WordCastCallable.Controls.negative_one_vector
/-- info: 'Solidity.Lowering.V08.WordCastCallable.Controls.wrong_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.WordCastCallable.Controls.wrong_snapshot
/-- info: 'Solidity.Lowering.V08.WordCastCallable.Controls.wrong_return' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.WordCastCallable.Controls.wrong_return
/-- info: 'Solidity.Lowering.V08.WordCastCallable.Controls.raw_return_distinct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.WordCastCallable.Controls.raw_return_distinct
/-- info: 'Solidity.Lowering.V08.WordCastCallable.Controls.boundary_clients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.WordCastCallable.Controls.boundary_clients
/-- info: 'Solidity.Lowering.V08.WordCastCallable.Controls.payload_clients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.WordCastCallable.Controls.payload_clients
/-- info: 'Solidity.Lowering.V08.WordCastCallable.Controls.reached_timeout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.WordCastCallable.Controls.reached_timeout
/-- info: 'Solidity.Lowering.V08.WordCastCallable.Controls.static_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.WordCastCallable.Controls.static_execution
/-- info: 'Solidity.Lowering.V08.WordCastCallable.Controls.closed_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.WordCastCallable.Controls.closed_client
/-- info: 'Solidity.Lowering.V08.WordCastCallable.Controls.zero_horizon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.WordCastCallable.Controls.zero_horizon
