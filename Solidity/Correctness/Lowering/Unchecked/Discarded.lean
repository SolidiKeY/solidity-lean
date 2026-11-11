import Solidity.Correctness.Lowering.Unchecked.LocalUpdate
import Solidity.Correctness.Lowering.Unchecked.CompoundOne
import Solidity.Source.Eval
import Solidity.Source.Hoare

/-!
# Discarded increment results

Guards treating the old postfix value as the new prefix value when only a
statement discards that result. The value may differ, but discarded evaluation
must retain identical failures and complete poststates. These are Source
expression/statement ingredients, not raw rewriting or intrinsic model certification.
-/
namespace Solidity.Correctness.Lowering.Unchecked

/-- Discarding an increment/decrement result erases only its prefix/postfix
selection. The actual lvalue evaluation, write, failures and complete poststate
are retained at every horizon, checkedness, failure plan and calldata mode.
No operand success or no-panic premise is required. -/
theorem incDec_discarded {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (plan : Source.FailureExecution.RuntimePlan) (known : Bool)
    (source : Source.EMState E Γ) (inc pre : Bool) (l : Source.RLVal E Γ τ) :
    ((Source.evalE G F horizon (.incDec inc pre l)
      (plan := plan) (calldataKnown := known)) >>= fun _ => pure ()).run source =
    ((Source.evalE G F horizon (.incDec inc true l)
      (plan := plan) (calldataKnown := known)) >>= fun _ => pure ()).run source := by
  cases horizon <;> cases known <;> cases h : τ.containsCalldata <;>
    simp only [Source.evalE, Source.withLibraryCalldata, h, Bool.false_eq_true,
      if_false, if_true, bind_assoc, pure_bind]

/-- Statement lifting is a private proof step: a public specialization below
proves its discarded-evaluation premise, rather than assuming pass soundness. -/
private theorem expr_of_discarded {E : Source.Env} {Γ : Source.RCtx}
    {τ υ : Source.STy} {R : List Source.STy} {M : Bool} {k : Source.SCtx}
    (G : Source.Glob E) (F : Source.Fr) (horizon nps : Nat) (ph : Option (Source.Ph E))
    (plan : Source.FailureExecution.RuntimePlan) (known : Bool)
    (left : Source.RExpr E Γ τ) (right : Source.RExpr E Γ υ)
    (ls : Source.Locals E.layout Γ) (st : Source.St E)
    (same : ((Source.evalE G F horizon left (plan := plan) (calldataKnown := known))
        >>= fun _ => pure ()).run (ls, st) =
      ((Source.evalE G F horizon right (plan := plan) (calldataKnown := known))
        >>= fun _ => pure ()).run (ls, st)) :
    (Source.execS G F (horizon + 1) nps ph
      (.expr left : Source.RStmt E R M k Γ Γ) ls
      (plan := plan) (calldataKnown := known)).run (.nil, st) =
    (Source.execS G F (horizon + 1) nps ph
      (.expr right : Source.RStmt E R M k Γ Γ) ls
      (plan := plan) (calldataKnown := known)).run (.nil, st) := by
  cases hl : (Source.evalE G F horizon left (plan := plan) (calldataKnown := known)).run (ls, st) with
  | mk lr lp =>
    cases hr : (Source.evalE G F horizon right (plan := plan) (calldataKnown := known)).run (ls, st) with
    | mk rr rp =>
      have hd : (match lr with
          | .ok _ => ((.ok () : Source.R Unit), lp)
          | .error err => (.error err, lp)) =
        (match rr with
          | .ok _ => (.ok (), rp)
          | .error err => (.error err, rp)) := by
        cases lr <;> cases rr <;>
          simpa only [Source.Hoare.run_bind, hl, hr] using same
      cases lr <;> cases rr <;> cases hd <;>
        rw [Source.execS, Source.execS, Source.Hoare.run_bind, Source.Hoare.run_bind]
      all_goals
        dsimp only [ExceptT.run] at hl hr
        simp only [Source.EM.sub, ExceptT.run, ExceptT.mk, hl, hr]

/-- At the actual expression-statement boundary, prefix/postfix selection
has no effect on failures, returned locals, or any nonlocal field. This holds
for every lvalue and horizon, without assuming the increment succeeds. -/
theorem incDec_statement {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    {R : List Source.STy} {M : Bool} {k : Source.SCtx}
    (G : Source.Glob E) (F : Source.Fr) (horizon nps : Nat) (ph : Option (Source.Ph E))
    (plan : Source.FailureExecution.RuntimePlan) (known : Bool)
    (ls : Source.Locals E.layout Γ) (st : Source.St E)
    (inc pre : Bool) (l : Source.RLVal E Γ τ) :
    (Source.execS G F horizon nps ph
      (.expr (.incDec inc pre l) : Source.RStmt E R M k Γ Γ) ls
      (plan := plan) (calldataKnown := known)).run (.nil, st) =
    (Source.execS G F horizon nps ph
      (.expr (.incDec inc true l) : Source.RStmt E R M k Γ Γ) ls
      (plan := plan) (calldataKnown := known)).run (.nil, st) := by
  cases horizon with
  | zero => rfl
  | succ n =>
    exact expr_of_discarded G F n nps ph plan known _ _ ls st
      (incDec_discarded G F n plan known (ls, st) inc pre l)


/-- One Source statement law for literal-one compound assignment and every
prefix/postfix increment/decrement form, at arbitrary integer lvalues and all
horizons. No local-target, successful-read, successful-write or no-panic
premise is imposed. This does not certify the raw or intrinsic target output. -/
theorem compoundOne_statement {E : Source.Env} {Γ : Source.RCtx}
    {R : List Source.STy} {M : Bool} {k : Source.SCtx}
    (G : Source.Glob E) (F : Source.Fr) (horizon nps : Nat) (ph : Option (Source.Ph E))
    (plan : Source.FailureExecution.RuntimePlan) (known : Bool)
    (ls : Source.Locals E.layout Γ) (st : Source.St E)
    (t : Source.IntTy) (inc pre : Bool) (l : Source.RLVal E Γ (.int t))
    (fits : (if inc then Source.AssignOp.add else .sub).fits E.isBase E.mapFree
      (.rational (Source.Q.ofInt 1)) (.int t) = true) :
    (Source.execS G F horizon nps ph
      (.expr (.compound (if inc then .add else .sub) l (.const (Source.Q.ofInt 1)) fits)
        : Source.RStmt E R M k Γ Γ) ls (plan := plan) (calldataKnown := known)).run (.nil, st) =
    (Source.execS G F horizon nps ph
      (.expr (.incDec inc pre l) : Source.RStmt E R M k Γ Γ) ls
      (plan := plan) (calldataKnown := known)).run (.nil, st) := by
  cases horizon with
  | zero => rfl
  | succ n =>
    have discarded : ((Source.evalE G F n
        (.compound (if inc then .add else .sub) l (.const (Source.Q.ofInt 1)) fits)
        (plan := plan) (calldataKnown := known)) >>= fun _ => pure ()).run (ls, st) =
      ((Source.evalE G F n (.incDec inc true l)
        (plan := plan) (calldataKnown := known)) >>= fun _ => pure ()).run (ls, st) := by
      rw [compoundOne_eval G F n plan known t inc l fits]
    exact (expr_of_discarded G F n nps ph plan known _ _ ls st discarded).trans
      (incDec_statement G F (n + 1) nps ph plan known ls st inc pre l).symm

/-- The actual Source expression statements for literal-one compound
assignment and increment/decrement have equal outcomes and complete poststates.
The increment may be prefix or postfix: its value is discarded by `execS`, not
identified with the compound expression's value. No updated-value bound or
no-panic premise is imposed. Raw/model association remains a separate proof. -/
theorem literalCompound_statement {E : Source.Env} {Γ : Source.RCtx}
    {R : List Source.STy} {M : Bool} {k : Source.SCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (plan : Source.FailureExecution.RuntimePlan) (known : Bool)
    (ls : Source.Locals E.layout Γ) (st : Source.St E)
    (t : Source.IntTy) (inc pre : Bool) (i : Source.Idx Γ (.int t))
    (x : Int) (range : t.lo ≤ x ∧ x ≤ t.hi) (read : ls.get i = .int x range)
    (fits : (if inc then Source.AssignOp.add else .sub).fits E.isBase E.mapFree
      (.rational (Source.Q.ofInt 1)) (.int t) = true) :
    (Source.execS G F (fuel + 3) nps ph
      (.expr (.compound (if inc then .add else .sub) (.local i) (.const (Source.Q.ofInt 1)) fits)
        : Source.RStmt E R M k Γ Γ) ls (plan := plan) (calldataKnown := known)).run (.nil, st) =
    (Source.execS G F (fuel + 3) nps ph
      (.expr (.incDec inc pre (.local i)) : Source.RStmt E R M k Γ Γ) ls
      (plan := plan) (calldataKnown := known)).run (.nil, st) := by
  have _legacyRead := read
  exact compoundOne_statement G F (fuel + 3) nps ph plan known ls st t inc pre (.local i) fits

#print axioms incDec_discarded
#print axioms incDec_statement
#print axioms literalCompound_statement
#print axioms compoundOne_statement

end Solidity.Correctness.Lowering.Unchecked
