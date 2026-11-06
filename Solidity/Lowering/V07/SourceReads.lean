import Solidity.Lowering.V07.Scalar
import Solidity.Source.Eval
import Solidity.Source.Hoare
import Solidity.Semantics.Run

/-! Actual Source and intrinsic local reads. Both executions are the published
ones; local environment premises are initial observations, never desired runs.
Pure-pair order laws below do not assert commutation of effectful operands. -/
namespace Solidity.Lowering.V07
variable {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}

theorem source_local_transport (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (t : Source.IntTy)
    (i : Source.Idx srcΓ (.int t)) (j : Idx Γ (.val (integerPrim t)))
    (x : Int) (range : t.lo ≤ x ∧ x ≤ t.hi)
    (sourceRead : source.1.get i = .int x range)
    (targetRead : TEnv.get j target.env = integerValue t x range) :
    (Source.evalE G F (fuel+1) (.local i)).run source = (.ok (.val (.int x range)),source) ∧
    (.simple (.local j) : Val C Γ (integerPrim t)).evalT target = .ok (integerValue t x range) ∧
    IntValueRel t (.int x range : Source.Val E.layout (.int t)) (integerValue t x range) := by
  refine ⟨?_,congrArg Except.ok targetRead,integer_related t x range⟩
  change (Except.ok (Source.RVal.val (source.1.get i)),source) = _
  rw [sourceRead]

theorem source_pure_pair {σ τ : Source.STy} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (state : Source.EMState E srcΓ) (left : Source.RExpr E srcΓ σ) (right : Source.RExpr E srcΓ τ)
    (x : Source.RVal E.layout σ) (y : Source.RVal E.layout τ)
    (leftRun : (Source.evalE G F fuel left).run state = (.ok x,state))
    (rightRun : (Source.evalE G F fuel right).run state = (.ok y,state)) :
    (Source.evalPair G F (fuel+1) left right).run state = (.ok (x,y),state) := by
  rw [Source.evalPair]
  cases order : G.pipeline
  · rw [Source.Hoare.run_bind,rightRun]
    dsimp only
    rw [Source.Hoare.run_bind,leftRun]
    rfl
  · rw [Source.Hoare.run_bind,leftRun]
    dsimp only
    rw [Source.Hoare.run_bind,rightRun]
    rfl

theorem source_local_pair (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (state : Source.EMState E srcΓ) (t : Source.IntTy)
    (left right : Source.Idx srcΓ (.int t)) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (leftRead : state.1.get left = .int x hx) (rightRead : state.1.get right = .int y hy) :
    (Source.evalPair G F (fuel+2) (.local left) (.local right)).run state =
      (.ok (.val (.int x hx),.val (.int y hy)),state) := by
  apply source_pure_pair G F (fuel+1) state (.local left) (.local right)
  · change (Except.ok (Source.RVal.val (state.1.get left)),state) = _
    rw [leftRead]
  · change (Except.ok (Source.RVal.val (state.1.get right)),state) = _
    rw [rightRead]

end Solidity.Lowering.V07
