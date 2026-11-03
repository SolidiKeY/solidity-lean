import Solidity.Lowering.V08.ConstructorScalarTransport
import Solidity.Lowering.V08.LibraryCreation

/-! Actual continuations of the checked scalar constructor component. Reads and
later failures are derived from reached operations, not supplied whole-handler
outputs. This does not invent independent Source try-new/catch semantics. -/
namespace Solidity.Lowering.V08.ConstructorContinuations
open Solidity ContractWorld
open ConstructorScalarTransport

def readCreated (w : World catalog) (reference : Handle ()) : TRes (World catalog × Option Int) := do
  let store ← TRes.ofOpt (w.storage? reference)
  let .prim value ← TRes.ofOpt (store.find (SRef.ofRoot "saved" rfl))
  pure (w,PrimTy.num? value)

def caught (w : World catalog) (_ : THalt) : TRes (World catalog × Option Int) :=
  .ok (w,some (-1))

def attempt (n : Int) (h : range n)
    (success handler : World catalog → Handle () → TRes (World catalog × Option Int)) :=
  targetInitial.tryCreate (.ok ()) () (fun _ => Controls.self)
    (fun _ => targetBody n h) (fun _ => targetContext) success
    (fun w _ => handler w ⟨Controls.self⟩)

theorem read_reached (n : Int) (h : range n) :
    readCreated (targetNext n h) ⟨Controls.self⟩ = .ok (targetNext n h,some n) := by rfl

/-- Actual completed creation selects success for ANY continuations. No whole
continuation equation is an assumption of constructor or body preservation. -/
theorem from_created {K : Type} {cs : K → Contract} {β : Type}
    (w next : World cs) (kind : K) (address : Address) (ctor : Prog (cs kind) [] [])
    (ctx : Context) (reference : Handle kind)
    (success : World cs → Handle kind → TRes (World cs × β))
    (handler : World cs → THalt → TRes (World cs × β))
    (mutable : ctx.isStatic=false)
    (created : w.create kind address ctor ctx = .ok (next,reference)) :
    w.tryCreate (.ok ()) kind (fun _ => address) (fun _ => ctor) (fun _ => ctx) success handler =
      success next reference := by
  simp only [World.tryCreate,bind,Except.bind,mutable,Bool.false_eq_true,if_false,created]

theorem selects_success (n : Int) (h : range n)
    (success handler : World catalog → Handle () → TRes (World catalog × Option Int)) :
    attempt n h success handler = success (targetNext n h) ⟨Controls.self⟩ := by
  exact from_created (cs:=catalog) targetInitial (targetNext n h) () Controls.self
    (targetBody n h) targetContext ⟨Controls.self⟩ success
    (fun w _ => handler w ⟨Controls.self⟩) rfl (creation_actual n h)

def readAttempt (n : Int) (h : range n) := attempt n h readCreated (fun w _ => caught w .panic)

theorem read_commit (n : Int) (h : range n) : readAttempt n h = .ok (targetNext n h,some n) := by
  rw [readAttempt,selects_success,read_reached]

/-- A SECOND creation collides at the actual newly installed account. -/
theorem collision_reached (n : Int) (h : range n) :
    (targetNext n h).create () Controls.self .nil targetContext = .error .revert := by rfl

def collideAfterRead (w : World catalog) (reference : Handle ()) : TRes (World catalog × Option Int) := do
  let (_,value) ← readCreated w reference
  let (next,_) ← w.create () reference.address .nil targetContext
  pure (next,value)

theorem later_failure (n : Int) (h : range n) :
    collideAfterRead (targetNext n h) ⟨Controls.self⟩ = .error .revert := by
  unfold collideAfterRead
  rw [read_reached]
  simp only [bind,Except.bind,collision_reached]

def failingAttempt (n : Int) (h : range n) := attempt n h collideAfterRead (fun w _ => caught w .panic)

theorem success_failure_not_recaught (n : Int) (h : range n) :
    failingAttempt n h = .error .revert := by
  rw [failingAttempt,selects_success,later_failure]

theorem enclosing_atomic (n : Int) (h : range n) :
    atomic targetInitial (failingAttempt n h) = (targetInitial,.error .revert) := by
  rw [success_failure_not_recaught]
  rfl

/-- Occupied-account failure in the creation guard is caught at the PREEXISTING
reached world, before executing a second constructor body. -/
def occupiedAttempt (n : Int) (h : range n) :=
  (targetNext n h).tryCreate (.ok ()) () (fun _ => Controls.self)
    (fun _ => Prog.nil) (fun _ => targetContext) readCreated caught

theorem constructor_failure_caught (n : Int) (h : range n) :
    occupiedAttempt n h = .ok (targetNext n h,some (-1)) := by
  unfold occupiedAttempt World.tryCreate
  simp only [bind,Except.bind,show targetContext.isStatic=false from rfl,Bool.false_eq_true,if_false,
    collision_reached,catchable,caught]
  rfl

/-- Compare actual Source constructor execution to actual creation+read, only
through the shared numeric observation (never completion vs installation). -/
theorem source_to_tryread (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) (n : Int) (h : range n) :
    sourceObservation p bytes n h =
      (readAttempt n h).toOption.map (fun out => ((out.1.balance Controls.self).1.toNat,out.2)) := by
  rw [constructor_value_transport,target_created,read_commit]
  rfl

theorem wrong_catch_value (n : Int) (h : range n) :
    failingAttempt n h ≠ .ok (targetNext n h,some (-1)) := by
  rw [success_failure_not_recaught]
  intro wrong
  cases wrong

theorem wrong_rollback_snapshot (n : Int) (h : range n) :
    (atomic targetInitial (failingAttempt n h)).1 ≠ targetNext n h := by
  rw [enclosing_atomic]
  intro same
  have balances := congrArg (fun w => (w.balance Controls.sender).1) same
  change (93 : Int) = 86 at balances
  cases balances

theorem argument_failure (halt : THalt) :
    targetInitial.tryCreate (α:=Unit) (.error halt) () (fun _ => Controls.self)
      (fun _ => Prog.nil) (fun _ => targetContext) readCreated caught = .error halt := rfl

theorem static_failure (n : Int) (h : range n) :
    targetInitial.tryCreate (.ok ()) () (fun _ => Controls.self)
      (fun _ => targetBody n h) (fun _ => {targetContext with mode:=.readOnly}) readCreated caught =
      .error .revert := rfl

/-- info: 'Solidity.Lowering.V08.ConstructorContinuations.read_reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConstructorContinuations.read_reached

/-- info: 'Solidity.Lowering.V08.ConstructorContinuations.from_created' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConstructorContinuations.from_created

/-- info: 'Solidity.Lowering.V08.ConstructorContinuations.selects_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConstructorContinuations.selects_success

/-- info: 'Solidity.Lowering.V08.ConstructorContinuations.read_commit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConstructorContinuations.read_commit

/-- info: 'Solidity.Lowering.V08.ConstructorContinuations.collision_reached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConstructorContinuations.collision_reached

/-- info: 'Solidity.Lowering.V08.ConstructorContinuations.later_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConstructorContinuations.later_failure

/-- info: 'Solidity.Lowering.V08.ConstructorContinuations.success_failure_not_recaught' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConstructorContinuations.success_failure_not_recaught

/-- info: 'Solidity.Lowering.V08.ConstructorContinuations.enclosing_atomic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConstructorContinuations.enclosing_atomic

/-- info: 'Solidity.Lowering.V08.ConstructorContinuations.constructor_failure_caught' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConstructorContinuations.constructor_failure_caught

/-- info: 'Solidity.Lowering.V08.ConstructorContinuations.source_to_tryread' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConstructorContinuations.source_to_tryread

/-- info: 'Solidity.Lowering.V08.ConstructorContinuations.wrong_catch_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConstructorContinuations.wrong_catch_value

/-- info: 'Solidity.Lowering.V08.ConstructorContinuations.wrong_rollback_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConstructorContinuations.wrong_rollback_snapshot

/-- info: 'Solidity.Lowering.V08.ConstructorContinuations.argument_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConstructorContinuations.argument_failure

/-- info: 'Solidity.Lowering.V08.ConstructorContinuations.static_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConstructorContinuations.static_failure
end Solidity.Lowering.V08.ConstructorContinuations
