import Solidity.SolcValidation.IrEval

/-!
# Fuel stability of the IR interpreter

Every result of `SolcValidation/IrEval.lean` other than `Fault.fuel` is final:
more fuel reproduces it exactly. So a halt, a static error or a normal end
observed at some fuel is the program's behaviour, not an artefact of the
horizon; only `Fault.fuel` is inconclusive. The machine cannot produce
`Fault.fuel` (`MachineFault` has no such case), so that verdict is always the
interpreter's own horizon.
-/
namespace Solidity.SolcValidation.IrSyntax
open Solidity.SolcValidation

/-- `r'` agrees with `r` whenever `r` is conclusive. -/
def Ext {σ α : Type} (r r' : Run σ α) : Prop := r ≠ .error .fuel → r' = r

theorem Ext.refl {σ α : Type} (r : Run σ α) : Ext r r := fun _ => rfl

theorem Ext.fuel {σ α : Type} (r' : Run σ α) : Ext (.error .fuel) r' := fun h => absurd rfl h

theorem Ext.bind {σ α β : Type} {r r' : Run σ α} {f g : α → Run σ β}
    (h : Ext r r') (hf : ∀ a, Ext (f a) (g a)) : Ext (r >>= f) (r' >>= g) := by
  intro conclusive
  cases r with
  | error e =>
      have same : r' = .error e := h (fun bad => conclusive (by rw [bad]; rfl))
      rw [same]; rfl
  | ok a =>
      have same : r' = .ok a := h (fun bad => Except.noConfusion bad)
      rw [same]
      exact hf a conclusive

section
variable {σ : Type} (M : Machine σ) (ctx : ObjectCtx)

/-- One more unit of fuel preserves every conclusive result, for all eight
mutually recursive evaluators at once. -/
theorem eval_succ (k : Nat) :
    (∀ {F L r} (env : FunEnv F) (e : Expr F L r) (vs : Vals L) (s : σ),
      Ext (evalExpr M ctx k env e vs s) (evalExpr M ctx (k + 1) env e vs s)) ∧
    (∀ {F L n} (env : FunEnv F) (args : Args F L n) (vs : Vals L) (s : σ),
      Ext (evalArgs M ctx k env args vs s) (evalArgs M ctx (k + 1) env args vs s)) ∧
    (∀ {F c L} (env : FunEnv F) (st : Stmt F c L) (vs : Vals L) (s : σ),
      Ext (evalStmt M ctx k env st vs s) (evalStmt M ctx (k + 1) env st vs s)) ∧
    (∀ {F c L} (env : FunEnv F) (lp : Loop F c L) (vs : Vals L) (s : σ),
      Ext (evalLoop M ctx k env lp vs s) (evalLoop M ctx (k + 1) env lp vs s)) ∧
    (∀ {F : List FnSig} {c : Ctl} {L : List String} (env : FunEnv F) (cond : Expr F L 1) (post : Block F ⟨c.function, false⟩ L)
        (body : Block F ⟨c.function, true⟩ L) (vs : Vals L) (s : σ),
      Ext (iterate M ctx k env cond post body vs s) (iterate M ctx (k + 1) env cond post body vs s)) ∧
    (∀ {F L} (env : FunEnv F) (xs : List String) (init : Option (Expr F L xs.length))
        (vs : Vals L) (s : σ),
      Ext (evalInit M ctx k env xs init vs s) (evalInit M ctx (k + 1) env xs init vs s)) ∧
    (∀ {F c L g} (env : FunEnv F) (items : Items F c L g) (vs : Vals L) (s : σ),
      Ext (evalItems M ctx k env items vs s) (evalItems M ctx (k + 1) env items vs s)) ∧
    (∀ {F c L} (env : FunEnv F) (b : Block F c L) (vs : Vals L) (s : σ),
      Ext (evalBlock M ctx k env b vs s) (evalBlock M ctx (k + 1) env b vs s)) := by
  induction k with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> exact Ext.fuel _
  | succ k ih =>
      obtain ⟨hE, hA, hS, hL, hI, hN, hIt, hB⟩ := ih
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro F L r env e vs s
        cases e with
        | lit l => exact Ext.refl _
        | var x m => exact Ext.refl _
        | op o args =>
            simp only [evalExpr]
            exact Ext.bind (hA env args vs s) fun _ => Ext.refl _
        | call m args =>
            simp only [evalExpr]
            refine Ext.bind (hA env args vs s) fun ⟨s, xs⟩ => ?_
            exact Ext.bind (hB _ _ _ s) fun _ => Ext.refl _
      · intro F L n env args vs s
        cases args with
        | nil => exact Ext.refl _
        | cons e rest =>
            simp only [evalArgs]
            refine Ext.bind (hA env rest vs s) fun ⟨s, tail⟩ => ?_
            exact Ext.bind (hE env e vs s) fun _ => Ext.refl _
      · intro F c L env st vs s
        cases st with
        | block b => exact hB env b vs s
        | discard e =>
            simp only [evalStmt]
            exact Ext.bind (hE env e vs s) fun _ => Ext.refl _
        | assign ts e =>
            simp only [evalStmt]
            exact Ext.bind (hE env e vs s) fun _ => Ext.refl _
        | if_ e b =>
            simp only [evalStmt]
            refine Ext.bind (hE env e vs s) fun ⟨s, v⟩ => ?_
            dsimp only
            split
            · exact Ext.refl _
            · exact hB env b vs s
        | switch e cs =>
            simp only [evalStmt]
            refine Ext.bind (hE env e vs s) fun ⟨s, v⟩ => ?_
            dsimp only
            split
            · exact hB _ _ _ _
            · exact Ext.refl _
        | switchDefault e cs d =>
            simp only [evalStmt]
            exact Ext.bind (hE env e vs s) fun ⟨s, v⟩ => hB _ _ _ _
        | for_ lp => exact hL env lp vs s
        | leave => exact Ext.refl _
        | break_ => exact Ext.refl _
        | continue_ => exact Ext.refl _
      · intro F c L env lp vs s
        cases lp with
        | stmt st rest =>
            simp only [evalLoop]
            refine Ext.bind (hS env st vs s) fun ⟨s, vs, flow⟩ => ?_
            dsimp only
            split
            · exact hL env rest vs s
            · exact Ext.refl _
        | let_ xs init rest =>
            simp only [evalLoop]
            refine Ext.bind (hN env xs init vs s) fun ⟨s, fresh⟩ => ?_
            exact Ext.bind (hL env rest _ s) fun _ => Ext.refl _
        | run cond post body => exact hI env cond post body vs s
      · intro F c L env cond post body vs s
        simp only [iterate]
        refine Ext.bind (hE env cond vs s) fun ⟨s, v⟩ => ?_
        dsimp only
        split
        · exact Ext.refl _
        · refine Ext.bind (hB env body vs s) fun ⟨s, vs, flow⟩ => ?_
          dsimp only
          split
          · exact Ext.refl _
          · exact Ext.refl _
          · exact Ext.bind (hB env post vs s) fun ⟨s, vs, flow⟩ => by
              dsimp only
              split
              · exact Ext.refl _
              · exact hI env cond post body vs s
          · exact Ext.bind (hB env post vs s) fun ⟨s, vs, flow⟩ => by
              dsimp only
              split
              · exact Ext.refl _
              · exact hI env cond post body vs s
      · intro F L env xs init vs s
        cases init with
        | none => exact Ext.refl _
        | some e =>
            simp only [evalInit]
            exact Ext.bind (hE env e vs s) fun _ => Ext.refl _
      · intro F c L g env items vs s
        cases items with
        | nil => exact Ext.refl _
        | stmt st rest =>
            simp only [evalItems]
            refine Ext.bind (hS env st vs s) fun ⟨s, vs, flow⟩ => ?_
            dsimp only
            split
            · exact hIt env rest vs s
            · exact Ext.refl _
        | let_ xs init rest =>
            simp only [evalItems]
            refine Ext.bind (hN env xs init vs s) fun ⟨s, fresh⟩ => ?_
            exact Ext.bind (hIt env rest _ s) fun _ => Ext.refl _
        | fn i rest => exact hIt env rest vs s
      · intro F c L env b vs s
        cases b with
        | mk ss bodies items => exact hIt _ items vs s

/-- Any conclusive block result at fuel `n` is the result at every larger fuel. -/
theorem evalBlock_stable {F c L} (n m : Nat) (le : n ≤ m) (env : FunEnv F) (b : Block F c L)
    (vs : Vals L) (s : σ) (conclusive : evalBlock M ctx n env b vs s ≠ .error .fuel) :
    evalBlock M ctx m env b vs s = evalBlock M ctx n env b vs s := by
  induction le with
  | refl => rfl
  | step _ ih =>
      rw [← ih]
      exact (eval_succ M ctx _).2.2.2.2.2.2.2 env b vs s (by rw [ih]; exact conclusive)

/-- Any conclusive run of an object's code at fuel `n` is its run at every larger fuel. -/
theorem runCode_stable (n m : Nat) (le : n ≤ m) (code : Code) (s : σ)
    (conclusive : runCode M ctx n code s ≠ .error .fuel) :
    runCode M ctx m code s = runCode M ctx n code s := by
  unfold runCode at conclusive ⊢
  have block : evalBlock M ctx n .nil code .nil s ≠ .error .fuel := by
    intro bad
    rw [bad] at conclusive
    exact conclusive rfl
  rw [evalBlock_stable M ctx n m le .nil code .nil s block]
end

end Solidity.SolcValidation.IrSyntax
