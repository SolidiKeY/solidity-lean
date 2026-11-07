import Solidity.Lowering.V08.PureArgumentCallable

/-! Guards individually feasible pure-argument evaluation premises witnessed
at different message-value frames. The SAME selected call, populated source
pair and actual entered target frame prove both evaluations. The target reads
msg.value dynamically rather than specializing an argument literal. This is a
component fixture, not arbitrary-body/frame/World or SourceSpec/H68 adequacy. -/
namespace H62.AuditV08Adapters.PureArgumentJoint
open Solidity Source
open Solidity.Lowering.V07 Solidity.Lowering.V08

def sourceLocals : Source.Locals ScalarCallableTransport.E.layout [.bool] := .cons (.bool true) .nil
def argument : Solidity.Val ConstructorScalarTransport.Cell [] .uint := .simple (.env .msgValue rfl)
def sourceArgument : Source.RExpr ScalarCallableTransport.E [.bool] (.int Source.IntTy.u256) :=
  .magic .msg "value" rfl

/-- The four public premise groups use the SAME message value and caller.
In particular, sourceStep and targetStep are proved executions, not inputs. -/
def Joint (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) : Prop :=
  IntegerCallable.Inputs (ScalarCallableTransport.global p) ScalarCallableTransport.frame
    ScalarCallableTransport.declaration Source.IntTy.u256 ∧
  (Source.IntTy.u256.lo ≤ 7 ∧ 7 ≤ Source.IntTy.u256.hi) ∧
  (Source.evalE (ScalarCallableTransport.global p) ScalarCallableTransport.frame (extra+11)
    sourceArgument).run (sourceLocals,ScalarCallableTransport.populated bytes) =
      (.ok (.val (.int 7 (by decide))),(sourceLocals,ScalarCallableTransport.populated bytes)) ∧
  argument.evalT ConstructorScalarTransport.entered = .ok (integerValue Source.IntTy.u256 7 (by decide))

theorem joint (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) : Joint p extra bytes :=
  ⟨IntegerCallable.uint_inputs p, by decide,
    SourceEnvironment.eval_value (ScalarCallableTransport.global p) ScalarCallableTransport.frame
      (extra+10) sourceLocals (ScalarCallableTransport.populated bytes), rfl⟩

theorem inhabited : ∃ (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes), Joint p extra bytes :=
  ⟨.legacy, 0, [], joint _ _ _⟩

/-- All five original clauses, including result extraction and complete caller
restoration, instantiated without a new evaluation or preservation premise. -/
theorem actual (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) :
    (Source.evalE (ScalarCallableTransport.global p) ScalarCallableTransport.frame (extra+13)
      (.call ScalarCallableTransport.declaration (IntegerCallable.uint_inputs p).signature
        (PureArgumentCallable.arguments Source.IntTy.u256 sourceArgument))).run
      (sourceLocals,ScalarCallableTransport.populated bytes) =
      (.ok (.val (.int 7 (by decide))),(sourceLocals,ScalarCallableTransport.populated bytes)) ∧
    (PureArgumentCallable.body PrimTy.uint argument).run ConstructorScalarTransport.entered =
      .ok ⟨ConstructorScalarTransport.entered.push (t:=.val .uint)
        (integerValue Source.IntTy.u256 7 (by decide)),List.prefix_refl _⟩ ∧
    LocalCallableTransport.result PrimTy.uint
      (ConstructorScalarTransport.entered.push (t:=.val .uint) (integerValue Source.IntTy.u256 7 (by decide))) =
      .ok (integerValue Source.IntTy.u256 7 (by decide)) ∧
    (ConstructorScalarTransport.entered.push (t:=.val .uint)
      (integerValue Source.IntTy.u256 7 (by decide))).drop
      (PureArgumentCallable.body PrimTy.uint argument).ext = ConstructorScalarTransport.entered ∧
    IntValueRel Source.IntTy.u256 (.int 7 (by decide) : Source.Val ScalarCallableTransport.E.layout _)
      (integerValue Source.IntTy.u256 7 (by decide)) :=
  PureArgumentCallable.transport (ScalarCallableTransport.global p) ScalarCallableTransport.frame
    ScalarCallableTransport.declaration Source.IntTy.u256 (IntegerCallable.uint_inputs p) extra
    sourceArgument argument sourceLocals (ScalarCallableTransport.populated bytes)
    ConstructorScalarTransport.entered 7 (by decide) (joint p extra bytes).2.2.1 (joint p extra bytes).2.2.2

/-- The entered frame for value8 cannot witness the value7 target-step premise. -/
theorem mismatched_frame_refused :
    argument.evalT PureArgumentCallable.entered8 ≠ .ok (integerValue Source.IntTy.u256 7 (by decide)) := by
  intro bad
  have number := congrArg (fun result => result.toOption.bind PrimTy.num?) bad
  change some (8 : Int) = some 7 at number
  cases number

/-- Same target syntax reads two distinct genuinely paid frames. This control
uses a numeric projection only; actual above keeps complete states/statuses. -/
theorem dynamic_value_not_constant :
    ((PureArgumentCallable.body PrimTy.uint argument).run ConstructorScalarTransport.entered).map
      (fun out => (LocalCallableTransport.result PrimTy.uint out.st).toOption.bind PrimTy.num?) ≠
    ((PureArgumentCallable.body PrimTy.uint argument).run PureArgumentCallable.entered8).map
      (fun out => (LocalCallableTransport.result PrimTy.uint out.st).toOption.bind PrimTy.num?) :=
  PureArgumentCallable.value_not_constant

#print axioms inhabited
#print axioms actual
#print axioms mismatched_frame_refused
#print axioms dynamic_value_not_constant
end H62.AuditV08Adapters.PureArgumentJoint
