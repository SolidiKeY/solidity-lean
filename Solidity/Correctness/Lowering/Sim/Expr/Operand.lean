import Solidity.Syntax.Elab.Arms

/-!
# The capture arm on operands and arithmetic (ls2-expressions)

What `hoistWith` returns, at an arbitrary callback record, on the leaves of
`Sim.exprFamily`'s `operand` family and on the arithmetic nodes whose arm is
one callback. These equations mention no simulation relation: any version of
the case interface reads the arms through them.

* a name, a Boolean, an environment read and a numeral have no captures and
  keep the state (`hoist_name`, `hoist_bool`, `hoist_env`, `hoist_num`);
* a unary operation is the operand's captures (`rc.hoist`), then
  `narrowCapture` (`hoist_unop`);
* a compound assignment with a target without `++`/`--` is the block of that
  one statement (`rc.elabStmtsP`), its value the target (`hoist_opAssign`).

Not here: `.ternary`, `.binop`, `.modular`, `.incDec`, `.assign` (their arms
branch on `synth`, `hasNarrow` and the scope).
-/
namespace Solidity.Correctness.Lowering.Sim

variable [FreshNames] (C : Contract) (rc : ElabRec C)

theorem hoist_name (x : String) : hoistWith C rc (.name x) = pure ([], .name x) := rfl

theorem hoist_bool (b : Bool) : hoistWith C rc (.bool b) = pure ([], .bool b) := rfl

theorem hoist_env (k : EnvKey) : hoistWith C rc (.env k) = pure ([], .env k) := rfl

theorem hoist_num (n : Nat) : hoistWith C rc (.num n) = pure ([], .num n) := by
  have fold : (RawExpr.num n).foldConst = pure (.num n) := by
    simp [RawExpr.foldConst, RawExpr.constRat?, pure, Except.pure]
  unfold hoistWith
  rw [fold]
  rfl

theorem hoist_unop (op : UnOp) (a : RawExpr) (h : (RawExpr.unop op a).constRat? = none) :
    hoistWith C rc (.unop op a) = (do
      let (P, a) ← rc.hoist a
      let (Q, e) ← narrowCapture C (.unop op a)
      pure (P ++ Q, e)) := by
  have fold : (RawExpr.unop op a).foldConst = pure (.unop op a) := by
    simp [RawExpr.foldConst, h]
  unfold hoistWith
  rw [fold]
  rfl

theorem hoist_opAssign (op : BinOp) (l r : RawExpr) (h : l.hasIncDec = false) :
    hoistWith C rc (.opAssign op l r) = (do
      let Q ← rc.elabStmtsP [.opAssign op l r]
      pure (Q, l)) := by
  have fold : (RawExpr.opAssign op l r).foldConst = pure (.opAssign op l r) := rfl
  unfold hoistWith
  rw [fold]
  show (do
    if l.hasIncDec then _
    let Q ← rc.elabStmtsP [.opAssign op l r]
    pure (Q, l)) = _
  rw [h]
  rfl

end Solidity.Correctness.Lowering.Sim
