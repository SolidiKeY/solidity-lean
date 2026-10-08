import Solidity.Calculus.Core.Derive

/-!
# A scoped formula proved on its erasure: `sol_erase`

`Calculus/Contracts.lean`'s contract rule (`useContract`, `FunContract`)
is a derived rule over today's run, which `Proves` does not extend; a
scoped statement reaches it through its erasure.  A formula with no hidden
binder or anonymising update, whose updates and modalities are boxes and
whose programs bind fresh names (`Fml.Plain`), holds exactly where its
erasure does (`holds_erase`), so its erasure's validity proves it
(`Valid.of_erase_plain`).  `sol_erase` turns `⊨ φ` (`Core.Valid`) into
today's `⊨` of the erasure, the parameters' `∀` stripped as a leaf's are
(`Derive.stripAlls`), `Fml.Plain` proved by unfolding it (`simp only`, the
names compared by `decide`).
-/

namespace Solidity.Core

variable {C : Contract}

/-- **A plain scoped formula is valid where its erasure is.** -/
theorem Valid.of_erase_plain {φ : Fml C []} (hp : φ.Plain [])
    (h : Solidity.Valid (φ.erase [])) : Valid φ :=
  fun σ => (holds_erase φ hp (Agree.nil σ)).2 (h _)

open Lean Elab Tactic Meta in
/-- `sol_erase`: `⊨ φ` scoped, by today's `⊨` of its erasure
(`Valid.of_erase_plain`), its parameters free. -/
elab "sol_erase" : tactic => withMainContext do
  let g ← getMainGoal
  let some (C, φ) ← Symex.validGoal? g | throwError "sol_erase: expected a goal `⊨ φ`, scoped"
  let rest := (← getUnsolvedGoals).erase g
  let nilCtx := mkApp (mkConst ``List.nil [0]) (mkConst ``LTy)
  let nilVar := mkApp (mkConst ``List.nil [0]) (mkConst ``Var)
  let hpTy := mkAppN (mkConst ``Fml.Plain) #[C, nilCtx, nilVar, φ]
  let hp ← mkFreshExprSyntheticOpaqueMVar hpTy
  let tac ← `(tactic| (simp only [Fml.Plain, Prog.Fresh, Stmt.Fresh, Frames.Fresh, CallRet.names,
      Args.names, Args.erase, Arg.separatedFrom, List.not_mem_nil, not_false_eq_true,
      List.mem_cons, List.mem_append, List.cons_append, List.nil_append, List.nodup_cons,
      List.nodup_nil, Var.user.injEq, Var.fresh.injEq, String.reduceEq, Nat.succ_ne_self,
      reduceCtorEq, or_self, or_false, or_true, and_self, and_true, and_false, true_and, not_or,
      forall_eq_or_imp, forall_eq, implies_true, List.contains_eq_mem, decide_false,
      Bool.not_false, Bool.and_true, Bool.or_eq_true, List.all_eq_true] <;> decide))
  setGoals [hp.mvarId!]
  try Term.withoutErrToSorry (evalTactic tac)
  catch _ => throwError "sol_erase: the formula is not plain (`Fml.Plain`)"
  unless (← getUnsolvedGoals).isEmpty do
    throwError "sol_erase: the formula is not plain (`Fml.Plain`)"
  let erased := mkAppN (mkConst ``Fml.erase) #[C, nilCtx, nilVar, φ]
  let g' ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Solidity.Valid) C erased) (← g.getTag)
  g.assign (mkAppN (mkConst ``Valid.of_erase_plain) #[C, φ, hp, g'])
  setGoals [g'.mvarId!]
  let g'' ← Derive.stripAlls (← Solidity.normValid g'.mvarId!)
  setGoals (g'' :: rest)

end Solidity.Core
