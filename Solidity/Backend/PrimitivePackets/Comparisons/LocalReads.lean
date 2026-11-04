import Solidity.Lowering.V07.SourceReads

/-! Pure local relational comparisons over full-width source integers.
Operation indices choose existing Source/intrinsic operators, not another AST.
The actual Source pair evaluator is used for either pipeline and checked mode. -/
namespace Solidity.Backend.PrimitivePackets.Comparisons
open Lowering.V07
inductive Order where | lt | le | gt | ge deriving DecidableEq, Repr

def sourceOp : Order → Source.BinOp
  | .lt => .lt | .le => .le | .gt => .gt | .ge => .ge

def targetOp : Order → BinOp
  | .lt => .lt | .le => .le | .gt => .gt | .ge => .ge

def result : Order → Int → Int → Bool
  | .lt,x,y => decide (x<y) | .le,x,y => decide (x≤y)
  | .gt,x,y => decide (y<x) | .ge,x,y => decide (y≤x)

def ty (signed : Bool) : Source.IntTy := ⟨signed,256,by decide⟩
abbrev prim (signed : Bool) := integerPrim (ty signed)

theorem accepts (o : Order) (signed : Bool) : (targetOp o).accepts (prim signed) = true := by
  cases o <;> cases signed <;> rfl

theorem returns (o : Order) (signed : Bool) : (targetOp o).ret (prim signed) = .bool := by
  cases o <;> cases signed <;> rfl

def expression {E : Source.Env} {Γ : Source.RCtx} (o : Order) (signed : Bool)
    (a b : Source.Idx Γ (.int (ty signed))) : Source.RExpr E Γ .bool :=
  .compare (sourceOp o) (.local a) (.local b)

theorem source_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (state : Source.EMState E Γ)
    (o : Order) (signed : Bool) (a b : Source.Idx Γ (.int (ty signed)))
    (x y : Int) (hx : (ty signed).lo≤x ∧ x≤(ty signed).hi)
    (hy : (ty signed).lo≤y ∧ y≤(ty signed).hi)
    (left : state.1.get a = .int x hx) (right : state.1.get b = .int y hy) :
    (Source.evalE G F (n+3) (expression o signed a b)).run state =
      (.ok (.val (.bool (result o x y))),state) := by
  rw [expression,Source.evalE]
  rw [Source.Hoare.run_bind,source_local_pair G F n state (ty signed) a b x y hx hy left right]
  cases o <;> rfl

theorem source_zero {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (state : Source.EMState E Γ)
    (o : Order) (signed : Bool) (a b : Source.Idx Γ (.int (ty signed))) :
    (Source.evalE G F 0 (expression o signed a b)).run state = (.error .timeout,state) := rfl

#print axioms source_run
end Solidity.Backend.PrimitivePackets.Comparisons
