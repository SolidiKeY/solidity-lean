import Solidity.Backend.Passes.ReachabilityControls

/-! Runtime reference selection and effect order over existing typed locals.
This is intrinsic conditional reassignment, not a source ternary or general
tuple/function-reference lowering theorem. -/
namespace Solidity.Backend.Passes.ReferenceControls
open Solidity.Evm Solidity.Evm.Memory
open Solidity.Backend.Passes.Controls.Fixture

abbrev Γb : Ctx := .val .bool :: Γ
def fb : Frag Γb := (Frag.init Γ).push (.val .bool) .ok
def state (b : Bool) : State C Γb := σ.push (t := .val .bool) b
def target (b : Bool) : Machine := writeMachine machine 4 (.val (bword b))

private abbrev destination : Idx Γb (.mem (.array (.prim .uint))) :=
  .there (.there .here)
private abbrev independent : Idx Γb (.mem (.array (.prim .uint))) :=
  .there (.there (.there (.there .here)))
private abbrev aliased : Idx Γb (.mem (.array (.prim .uint))) :=
  .there (.there (.there .here))

def switchAlias : Stmt C Γb Γb :=
  .ite (.simple (.local .here))
    (.cons (.rebindMem destination (.alias (.var independent rfl))) .nil)
    (.cons (.rebindMem destination (.alias (.var aliased rfl))) .nil)
def readAlias : Stmt C Γb Γb :=
  .assignLocal (.there .here)
    (.readMem (.index .dyn (.var destination rfl) (.simple (.lit 0 rfl))))
def branchThenRead : Prog C Γb Γb := .cons switchAlias (.cons readAlias .nil)
def wrongOrder : Prog C Γb Γb := .cons readAlias (.cons switchAlias .nil)
def checked : Compiler.Compilation 0 fb branchThenRead :=
  (Compiler.compile 0 fb branchThenRead).get (by decide +kernel)
def checkedWrong : Compiler.Compilation 0 fb wrongOrder :=
  (Compiler.compile 0 fb wrongOrder).get (by decide +kernel)

theorem input_repr (b : Bool) : StateRepr 1 0 6 fb (state b) base (target b) :=
  LinkedControls.frame_six.consVal (p := .bool) b (.val (bword b)) rfl (by decide)

theorem certificate (b : Bool) (tail : List Word) :
    checked.Agrees 1 6 base (state b) {(target b) with stack := tail} := by
  apply checked.correct
  apply (checked.memory_input (by decide +kernel) _ _ _ _ _).mpr
  exact ⟨(input_repr b).stack tail, by decide +kernel,
    .inl (allocationCostProg_zero _ (by decide +kernel) _)⟩

private def sourceIdentity (out : TRes (Solidity.Out C (state true).H Γb)) : Option Nat :=
  match out with
  | .ok o => (TEnv.get destination o.st.env).map (fun r => r.id)
  | .error _ => none
private def sourceValue (out : TRes (Solidity.Out C (state true).H Γb)) : Option Int :=
  match out with
  | .ok o => some (TEnv.get (.there .here : Idx Γb (.val .uint)) o.st.env).1
  | .error _ => none
private def targetCell (a : Nat) : Evm.Out → Option Nat
  | .ok m _ => match m.mem a with | .val w => some w.val | _ => none
  | _ => none

/-- One compiled runtime conditional selects two different actual references,
not two copies of one evaluator or a compile-time literal branch. -/
theorem both_source_branches :
    sourceIdentity (branchThenRead.run (state true)) = some 1 ∧
    sourceValue (branchThenRead.run (state true)) = some 4 ∧
    sourceIdentity (branchThenRead.run (state false)) = some 0 ∧
    sourceValue (branchThenRead.run (state false)) = some 7 := by
  repeat' constructor <;> decide +kernel

theorem both_target_branches :
    targetCell 2 (run checked.code (target true)) = some 20 ∧
    targetCell 3 (run checked.code (target true)) = some 4 ∧
    targetCell 2 (run checked.code (target false)) = some 16 ∧
    targetCell 3 (run checked.code (target false)) = some 7 := by
  repeat' constructor <;> decide +kernel

/-- Moving the read in front of the reference effect leaves the old value7
even though the final pointer now selects the independent array. -/
theorem wrong_order :
    sourceValue (wrongOrder.run (state true)) = some 7 ∧
    targetCell 2 (run checkedWrong.code (target true)) = some 20 ∧
    targetCell 3 (run checkedWrong.code (target true)) = some 7 := by
  repeat' constructor <;> decide +kernel

def initializeBool (b : Bool) : Prog C Γ Γb :=
  .cons (.declLocal .bool (.user "select") (some (.simple (.bool b)))) .nil

theorem reachable (b : Bool) :
    (ReachabilityControls.populatedBuilder.join (initializeBool b)).run (State.init C) =
      .ok ⟨state b, ⟨σ.H, rfl⟩⟩ := by
  rw [DeferredSource.join_run]
  simp only [TRun.seq, ReachabilityControls.fresh_state_reaches_fixture, Except.map]
  cases b <;> with_unfolding_all rfl

end Solidity.Backend.Passes.ReferenceControls
