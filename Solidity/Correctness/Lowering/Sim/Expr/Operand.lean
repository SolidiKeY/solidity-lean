import Solidity.Syntax.Elab.Arms
import Solidity.Correctness.Lowering.Sim.Expr.Run

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

For a capture predicate `S` with `Pieces S` (`Sim/Expr/Run.lean`) the arms
emit captures in `S`, from the obligations of the callbacks they call as
hypotheses (`hoist_leaf_emits`, `hoist_unop_emits`, `hoist_opAssign_emits`).

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

open Solidity.Goals (ElabRan)

variable {C rc} {S : ElabScope → ECtx × Nat → SProg C → ECtx × Nat → Prop}

/-- A leaf operand emits no captures. -/
theorem hoist_leaf_emits (ok : Pieces S) {e : RawExpr}
    (leaf : (∃ x, e = .name x) ∨ (∃ b, e = .bool b) ∨ (∃ k, e = .env k) ∨ ∃ n, e = .num n)
    {sc : ElabScope} {st st' : ECtx × Nat} {out : SProg C × RawExpr}
    (ran : ElabRan (hoistWith C rc e) sc st out st') : S sc st out.1 st' := by
  have h : hoistWith C rc e = pure ([], e) := by
    obtain ⟨x, rfl⟩ | ⟨b, rfl⟩ | ⟨k, rfl⟩ | ⟨n, rfl⟩ := leaf
    · exact hoist_name C rc x
    · exact hoist_bool C rc b
    · exact hoist_env C rc k
    · exact hoist_num C rc n
  rw [h] at ran
  obtain ⟨h₁, h₂⟩ := ran_pure ran
  rw [h₁, h₂]
  exact ok.nil sc st

/-- A unary operation emits its operand's captures, then `narrowCapture`'s. -/
theorem hoist_unop_emits (ok : Pieces S) (hoist : Emits S rc.hoist)
    (narrow : Emits S (narrowCapture C)) {op : UnOp} {a : RawExpr}
    (h : (RawExpr.unop op a).constRat? = none) {sc : ElabScope} {st st' : ECtx × Nat}
    {out : SProg C × RawExpr} (ran : ElabRan (hoistWith C rc (.unop op a)) sc st out st') :
    S sc st out.1 st' := by
  rw [hoist_unop C rc op a h] at ran
  obtain ⟨⟨P, a'⟩, st₁, r₁, r₂⟩ := ran_bind ran
  obtain ⟨⟨Q, e⟩, st₂, r₃, r₄⟩ := ran_bind r₂
  obtain ⟨rfl, rfl⟩ := ran_pure r₄
  exact ok.append (hoist _ _ _ _ _ r₁) (narrow _ _ _ _ _ r₃)

/-- A compound assignment as a value emits the block of that statement. -/
theorem hoist_opAssign_emits
    (block : ∀ ss sc st P st', ElabRan (rc.elabStmtsP ss) sc st P st' → S sc st P st')
    {op : BinOp} {l r : RawExpr} (h : l.hasIncDec = false) {sc : ElabScope}
    {st st' : ECtx × Nat} {out : SProg C × RawExpr}
    (ran : ElabRan (hoistWith C rc (.opAssign op l r)) sc st out st') : S sc st out.1 st' := by
  rw [hoist_opAssign C rc op l r h] at ran
  obtain ⟨Q, st₁, r₁, r₂⟩ := ran_bind ran
  obtain ⟨rfl, rfl⟩ := ran_pure r₂
  exact block _ _ _ _ _ r₁

end Solidity.Correctness.Lowering.Sim
