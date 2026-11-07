import Solidity.Lowering.V07.P12NegatedCondition
import Solidity.Lowering.V07.P12AssignedConditionControls
import Solidity.Lowering.V07.ShortCircuitControls

namespace Solidity.Lowering.V07.P12NegatedConditionControls
open Source.SemanticsExamples P12NextInterface
open P12NegatedCondition
open P12Controls (C E SrcCtx TgtCtx source target mapping)
open P12AssignedConditionControls (values worlds initial initial_pair srcPair tgtPair)
open MixedAssignmentControls (globals)

def expr : Source.RExpr E SrcCtx .bool := .assign (.local .here) (.local (.there .here))
def producer (p : Roadmap.Pipeline) (checked : Bool) :=
  negate (globals p) {F0 with checked := checked} mapping values worlds expr
    (P12AssignedConditionControls.producer p checked)
def double_producer (p : Roadmap.Pipeline) (checked : Bool) :=
  negate (globals p) {F0 with checked := checked} mapping values worlds (.unary .not expr) (producer p checked)

def code_client (p : Roadmap.Pipeline) (checked : Bool) :=
  operand_code (P12AssignedConditionControls.producer p checked).operand
def run_client (p : Roadmap.Pipeline) (checked : Bool) :=
  operand_run (P12AssignedConditionControls.producer p checked).operand target
def operand_success_client := operand_success (assignLocalOperand (C := C) (Γ := TgtCtx) .here (.there .here))
  target ⟨target.setLocal .here true,List.prefix_refl _⟩ true (assigned_condition_operand_run target .here (.there .here))
def double_client (p : Roadmap.Pipeline) (checked : Bool) :=
  double_negate_run (P12AssignedConditionControls.producer p checked).operand target

def source_zero_client (p : Roadmap.Pipeline) := source_zero (globals p) F0 source expr
def source_run_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_run (globals p) {F0 with checked := checked} (fuel+2) source
    (source.1.set .here (.bool true),source.2) expr true
    (source_assign_local_run (globals p) {F0 with checked := checked} fuel source .here (.there .here) _ rfl)
def source_success_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_success (globals p) {F0 with checked := checked} (fuel+2) source
    (source.1.set .here (.bool true),source.2) expr false (source_run_client p checked fuel)
def success_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  (producer p checked).success (fuel+3) source (source.1.set .here (.bool true),source.2)
    target false initial (source_run_client p checked fuel)
def extension_client (p : Roadmap.Pipeline) (checked : Bool) := DeferredSource.Operand.run_wk
  (producer p checked).operand (Thin.drop (t := .val .bool) .refl) target (true,target.env)
def live_reference_client := P12Controls.live_memory_and_storage

theorem actual_source_failure (p : Roadmap.Pipeline) (checked : Bool) :
    (Source.evalE (globals p) {F0 with checked := checked} 10 ShortCircuitControls.failure).run source =
      (.error (.revert (Source.panicData .divZero)),source) := by
  cases p <;> cases checked <;> rfl

def source_error_client (p : Roadmap.Pipeline) (checked : Bool) :=
  source_error (globals p) {F0 with checked := checked} 10 source source ShortCircuitControls.failure
    (.revert (Source.panicData .divZero)) (actual_source_failure p checked)
def source_revert_client (p : Roadmap.Pipeline) (checked : Bool) :=
  source_revert (globals p) {F0 with checked := checked} 10 source source ShortCircuitControls.failure
    (Source.panicData .divZero) (source_error_client p checked)

def failing : DeferredSource.Operand C TgtCtx (.prim .bool) :=
  ⟨_,.cons (.revertData [.bytes (Source.panicData .divZero)]) .nil,.val (.simple (.bool false))⟩
theorem actual_native_failure : failing.run target = .error (THalt.ofData (Source.panicData .divZero)) := by
  rfl

def error_client := operand_error failing target (THalt.ofData (Source.panicData .divZero)) actual_native_failure

def observe (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) (old rhs : Bool) : Option (List Int) :=
  let s := srcPair old rhs
  let t := tgtPair old rhs
  let sourceObservation := match (Source.evalE (globals p) {F0 with checked := checked} fuel
      (.unary .not expr)).run s with
    | (.ok (.val (.bool c)),post) => match post.1.get .here,post.1.get (.there .here) with
      | .bool a,.bool b => some [1,Int.ofNat c.toNat,Int.ofNat a.toNat,Int.ofNat b.toNat]
      | _,_ => none
    | (.error .timeout,post) => match post.1.get .here,post.1.get (.there .here) with
      | .bool a,.bool b => some [-1,-1,Int.ofNat a.toNat,Int.ofNat b.toNat]
      | _,_ => none
    | _ => none
  match sourceObservation,(producer p checked).operand.code.run t,(producer p checked).operand.run t,
      (double_producer p checked).operand.run t with
  | some xs,.ok cap,.ok (out,.prim result),.ok (twice,.prim result2) => some (xs ++
      [Int.ofNat (TEnv.get .here cap.st.env).toNat,
       Int.ofNat (TEnv.get (.there .here) cap.st.env).toNat,
       Int.ofNat (TEnv.get (.there (.there .here)) cap.st.env).toNat,
       Int.ofNat result.toNat,Int.ofNat (TEnv.get .here out.st.env).toNat,
       Int.ofNat (TEnv.get (.there .here) out.st.env).toNat,
       Int.ofNat result2.toNat,Int.ofNat (TEnv.get .here twice.st.env).toNat])
  | _,_,_,_ => none

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun checked =>
  [false,true].all fun old => [false,true].all fun rhs => (List.range 7).all fun fuel =>
    let o := Int.ofNat old.toNat
    let r := Int.ofNat rhs.toNat
    let n := Int.ofNat (!rhs).toNat
    observe p checked fuel old rhs == some
      ((if fuel < 3 then [-1,-1,o,r] else [1,n,r,r]) ++ [r,r,r,n,r,r,r,r])))

-- A toggling operand makes duplicated prefix evaluation observable.
def flip : DeferredSource.Operand C TgtCtx (.prim .bool) :=
  ⟨_,.cons (.assignLocal .here (.unop .not rfl rfl (.simple (.local .here)))) .nil,
    .val (.simple (.local .here))⟩
def wrongTwice : DeferredSource.Operand C TgtCtx (.prim .bool) :=
  ⟨_,flip.code.join flip.code,.val (.unop .not rfl rfl (.simple (.local .here)))⟩
def wrongCaller : DeferredSource.Operand C TgtCtx (.prim .bool) :=
  ⟨_,.cons (.assignLocal .here (.unop .not rfl rfl (.simple (.local (.there .here))))) .nil,
    .val (.simple (.local .here))⟩
def resultAndCaller (e : DeferredSource.Operand C TgtCtx (.prim .bool)) : Option (Bool × Bool) :=
  match e.run target with | .ok (out,.prim result) => some (result,TEnv.get .here out.st.env) | _ => none
/-- info: [some (false, true), some (true, true), some (false, false), some (false, true), some (true, false)] -/
#guard_msgs in
#eval IO.println (reprStr [resultAndCaller (producer .legacy true).operand,
  resultAndCaller (P12AssignedConditionControls.producer .legacy true).operand,
  resultAndCaller wrongCaller,resultAndCaller (operand flip),resultAndCaller wrongTwice])

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  match (Source.evalE (globals .legacy) F0 11 (.unary .not ShortCircuitControls.failure)).run source,
      (operand failing).run target,(operand (operand failing)).run target with
  | (.error (.revert data),_),.error native,.error twice =>
      data == Source.panicData .divZero && native == THalt.ofData data && twice == native
  | _,_,_ => false))

/-- info: 'Solidity.Lowering.V07.P12NegatedConditionControls.producer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedConditionControls.producer

/-- info: 'Solidity.Lowering.V07.P12NegatedConditionControls.double_producer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedConditionControls.double_producer

/-- info: 'Solidity.Lowering.V07.P12NegatedConditionControls.code_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedConditionControls.code_client

/-- info: 'Solidity.Lowering.V07.P12NegatedConditionControls.run_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedConditionControls.run_client

/-- info: 'Solidity.Lowering.V07.P12NegatedConditionControls.operand_success_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedConditionControls.operand_success_client

/-- info: 'Solidity.Lowering.V07.P12NegatedConditionControls.double_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedConditionControls.double_client

/-- info: 'Solidity.Lowering.V07.P12NegatedConditionControls.source_zero_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedConditionControls.source_zero_client

/-- info: 'Solidity.Lowering.V07.P12NegatedConditionControls.source_run_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedConditionControls.source_run_client

/-- info: 'Solidity.Lowering.V07.P12NegatedConditionControls.source_success_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedConditionControls.source_success_client

/-- info: 'Solidity.Lowering.V07.P12NegatedConditionControls.success_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedConditionControls.success_client

/-- info: 'Solidity.Lowering.V07.P12NegatedConditionControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedConditionControls.extension_client

/-- info: 'Solidity.Lowering.V07.P12NegatedConditionControls.live_reference_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedConditionControls.live_reference_client

/-- info: 'Solidity.Lowering.V07.P12NegatedConditionControls.actual_source_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedConditionControls.actual_source_failure

/-- info: 'Solidity.Lowering.V07.P12NegatedConditionControls.source_error_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedConditionControls.source_error_client

/-- info: 'Solidity.Lowering.V07.P12NegatedConditionControls.source_revert_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedConditionControls.source_revert_client

/-- info: 'Solidity.Lowering.V07.P12NegatedConditionControls.actual_native_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedConditionControls.actual_native_failure

/-- info: 'Solidity.Lowering.V07.P12NegatedConditionControls.error_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.P12NegatedConditionControls.error_client

end Solidity.Lowering.V07.P12NegatedConditionControls
