import Solidity.Semantics.NoPanicOps

/-!
# Only an `assert` panics

A statement with no `assert` in it never panics (`Prog.run_noPanic`): every
operation it runs is one of `Semantics/NoPanicOps.lean`'s, none of which
panics.
-/

namespace Solidity

open Semantics

variable {C : Contract}

/-- A `transfer` never panics. -/
theorem Stmt.run_transfer_noPanic (σ : State) (r a : Val C .uint) :
    NoPanic ((Stmt.transfer r a).run σ) := by
  simp only [Stmt.run]; no_panic

/-! ## Statements

A statement panics only through an `assert` it runs: one of its own, or one in
a branch, a callee or a clause. -/

mutual

/-- Whether an `assert` occurs in the statement, in a branch, a callee or a
clause included. -/
def Stmt.mayPanic : Stmt C → Bool
  | .assert _ => true
  | .ite _ thn els => Prog.mayPanic thn || Prog.mayPanic els
  | .call _ _ _ _ body => Prog.mayPanic body
  | .tryCall _ _ ok err _ pnc other =>
    Prog.mayPanic ok || Prog.mayPanic err || Prog.mayPanic pnc || Prog.mayPanic other
  | .loop _ _ body => Prog.mayPanic body
  | _ => false

def Prog.mayPanic : List (Stmt C) → Bool
  | [] => false
  | s :: P => s.mayPanic || Prog.mayPanic P

end

mutual

/-- **Only an `assert` panics**: a statement with none in it never does. -/
theorem Stmt.run_noPanic (σ : State) : (s : Stmt C) → s.mayPanic = false → NoPanic (s.run σ)
  | .assign .., _ | .rebind .., _ | .assignLocal .., _ | .declLocal .., _ | .declStorage .., _
  | .opAssign .., _ | .incDec .., _ | .assignIncDec .., _ | .push .., _ | .pop .., _
  | .transfer .., _ | .send .., _ | .declMem .., _ | .rebindMem .., _ | .assignFromMem .., _
  | .assignMem .., _ | .delete .., _ | .deleteMem .., _ | .assignNew .., _ | .require _, _
  | .revert, _ => by
    simp only [Stmt.run] <;> no_panic
  | .assert _, h => by simp only [Stmt.mayPanic, Bool.true_eq_false] at h
  | .ite c thn els, h => by
    simp only [Stmt.mayPanic, Bool.or_eq_false_iff] at h
    have h₁ := fun τ => Prog.run_noPanic τ thn h.1
    have h₂ := fun τ => Prog.run_noPanic τ els h.2
    simp only [Stmt.run]
    refine NoPanic.bind (by simp only [ne_eq, Val.eval_noPanic, not_false_eq_true]) fun _ _ => ?_
    split <;> simp only [ne_eq, not_false_eq_true, h₁, h₂, Except.error.injEq, reduceCtorEq]
  | .call _ args _ ret body, h => by
    simp only [Stmt.mayPanic] at h
    have h₁ := fun τ => Prog.run_noPanic τ body h
    simp only [Stmt.run]; no_panic
  | .tryCall call rets ok err code pnc other, h => by
    simp only [Stmt.mayPanic, Bool.or_eq_false_iff] at h
    have h₁ := fun τ => Prog.run_noPanic τ ok h.1.1.1
    have h₂ := fun τ => Prog.run_noPanic τ err h.1.1.2
    have h₃ := fun τ => Prog.run_noPanic τ pnc h.1.2
    have h₄ := fun τ => Prog.run_noPanic τ other h.2
    simp only [Stmt.run]
    refine NoPanic.bind (by simp only [ne_eq, ExtCall.key_noPanic, not_false_eq_true]) fun _ _ => ?_
    split
    · simp only [ne_eq, Except.error.injEq, reduceCtorEq, not_false_eq_true]
    · exact NoPanic.bind (by simp only [ne_eq, bindData_noPanic, not_false_eq_true]) fun _ _ => h₁ _
    · exact h₂ _
    · exact NoPanic.bind (by simp only [ne_eq, bindData_noPanic, not_false_eq_true]) fun _ _ => h₃ _
    · exact h₄ _
  | .loop _ c body, h => by
    simp only [Stmt.mayPanic] at h
    have h₁ := fun τ => Prog.run_noPanic τ body h
    simp only [Stmt.run]
    refine Loop.run_induct (P := fun _ => True) (Q := NoPanic) trivial (fun τ _ => ?_)
      (by simp only [ne_eq, Except.error.injEq, reduceCtorEq, not_false_eq_true])
    have hc : NoPanic (c.eval τ) := by simp only [ne_eq, Val.eval_noPanic, not_false_eq_true]
    simp only [Loop.step]
    rcases hv : c.eval τ with e | (_ | b)
    · rw [hv] at hc
      simp only [ne_eq, Except.error.injEq] at hc ⊢
      exact hc
    · simp only [ne_eq, Except.error.injEq, reduceCtorEq, not_false_eq_true]
    · cases b
      · simp only [ne_eq, reduceCtorEq, not_false_eq_true]
      · have hb := h₁ τ
        revert hb
        cases Prog.run τ body <;> simp only [imp_self, implies_true]

theorem Prog.run_noPanic (σ : State) : (P : List (Stmt C)) → Prog.mayPanic P = false →
    NoPanic (Prog.run σ P)
  | [], _ => by simp only [Prog.run, ne_eq, NoPanic.pure, not_false_eq_true]
  | s :: P, h => by
    simp only [Prog.mayPanic, Bool.or_eq_false_iff] at h
    simp only [Prog.run]
    exact NoPanic.bind (Stmt.run_noPanic σ s h.1) fun τ _ => Prog.run_noPanic τ P h.2

end

end Solidity
