import Solidity.Syntax.Elab.Context

/-!
# Checks: the total passes of `Syntax/Elab/Context.lean`

`RawExpr.mapM` is a plain `def` (`RawExpr.mapMFuel` to a depth past its
argument's size), so the kernel evaluates the passes built on it, and its
defining equation holds for a callback whose results are no larger in a
measure (`RawExpr.mapM_eq_of_measure`): `RawExpr.rename` is one, by the number
of nodes.  Two callbacks outside that condition are recorded: one that wraps
its argument, for which the equation is false, and `RawExpr.orderNamed`'s,
which grows a malformed named call.
-/

namespace Solidity.Examples.ElabTotal.Context

open Solidity Semantics

/-! ## `RawExpr.mapM` -/

/-- The kernel evaluates a rename: no `native_decide`. -/
example : RawExpr.rename [("x", "y")] (.binop .add (.name "x") (.call "x" [.name "z", .num 3])) =
    .binop .add (.name "y") (.call "y" [.name "z", .num 3]) := by
  rfl

/-- `RawExpr.rename`'s node: a name or a called name, renamed. -/
def renameNode (ρ : List (String × String)) : RawExpr → RawExpr
  | .name x => .name ((lookupBy x ρ).getD x)
  | .call g as => .call ((lookupBy g ρ).getD g) as
  | e => e

theorem renameNode_nodes (ρ : List (String × String)) (e : RawExpr) :
    (renameNode ρ e).nodes ≤ e.nodes := by
  cases e <;> simp [renameNode, RawExpr.nodes]

/-- `RawExpr.rename` is `RawExpr.mapM` of `renameNode`. -/
theorem rename_eq_mapM (ρ : List (String × String)) (e : RawExpr) :
    e.rename ρ = RawExpr.mapM (m := Id) (renameNode ρ) e := by
  unfold RawExpr.rename
  exact congrArg (fun f => Id.run (RawExpr.mapM f e)) (funext fun e => by cases e <;> rfl)

/-- The defining equations of `RawExpr.rename`, from `RawExpr.mapM_id_eq` at
the number of nodes. -/
theorem rename_name (ρ : List (String × String)) (x : String) :
    (RawExpr.name x).rename ρ = .name ((lookupBy x ρ).getD x) := by
  rw [rename_eq_mapM, RawExpr.mapM_id_eq RawExpr.measure_nodes _ (renameNode_nodes ρ)]; rfl

theorem rename_binop (ρ : List (String × String)) (op : BinOp) (a b : RawExpr) :
    (RawExpr.binop op a b).rename ρ = .binop op (a.rename ρ) (b.rename ρ) := by
  rw [rename_eq_mapM, RawExpr.mapM_id_eq RawExpr.measure_nodes _ (renameNode_nodes ρ),
    rename_eq_mapM, rename_eq_mapM]; rfl

theorem rename_call (ρ : List (String × String)) (g : String) (as : List RawExpr) :
    (RawExpr.call g as).rename ρ = .call ((lookupBy g ρ).getD g) (as.map (·.rename ρ)) := by
  rw [rename_eq_mapM, RawExpr.mapM_id_eq RawExpr.measure_nodes _ (renameNode_nodes ρ)]
  simp only [renameNode, rename_eq_mapM]

/-- In `Except`, the equation at a node the callback keeps (`sizeOf`). -/
example (f : RawExpr → Except String RawExpr)
    (hf : ∀ e e', f e = .ok e' → sizeOf e' ≤ sizeOf e) (a : RawExpr)
    (h : f (.unop .not a) = .ok (.unop .not a)) :
    RawExpr.mapM f (.unop .not a) = (do return .unop .not (← a.mapM f)) := by
  rw [RawExpr.mapM_except_eq RawExpr.measure_sizeOf f hf, h]; rfl

/-- **Where the equation is false**: a callback that wraps its argument.  The
partial rewrite did not end on it; the total one stops at its depth, and its
result is not the equation's (`x = -x` has no solution). -/
example (e : RawExpr) :
    let x : RawExpr := Id.run (RawExpr.mapM (fun e => pure (.unop .neg e)) e)
    x ≠ .unop .neg x := by
  intro x h; clear_value x; have := congrArg sizeOf h; simp at this

/-- **A callback of the elaborator outside the condition**: `orderNamed` on a
named call with fewer arguments than names pads with `0`, a node more (the
parser writes as many arguments as names; the type does not say so). -/
example :
    RawExpr.orderNamed [("f", { params := [("a", .prim .uint)], body := [] })] (.named "f" ["a"] []) =
      .ok (.call "f" [.num 0]) := by
  rfl

example : (RawExpr.named "f" ["a"] []).nodes < (RawExpr.call "f" [.num 0]).nodes := by decide

end Solidity.Examples.ElabTotal.Context
