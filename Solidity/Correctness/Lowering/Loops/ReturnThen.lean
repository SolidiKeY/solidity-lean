import Solidity.Correctness.Lowering.Loops.Returns
import Solidity.Lowering.G19.AssignmentWhileReset

/-!
# Return leaf with a suffix: `while (i = a) return; a = false;`

The function-level output keeps the `ret` flag and runs the suffix only in
the `else` branch of `if (ret)` (`lowerReturns`, Lower.lean:300-304), so the
flag decides what runs after the loop: this leaf checks that the suffix runs
exactly when Source did not return. Source half: G19 `WhileReturn.correct`
through `Returns.whileReturn_source_run`, then two generic block lemmas; the
suffix relation uses V07's `ContextMap.related_write`.
-/
namespace Solidity.Correctness.Lowering.Loops

open Solidity.Lowering.V07
open Solidity.Lowering.G19.AssignmentReturnFlag (boolSlot)
open Solidity.Lowering.G19.AssignmentWhileReset (restore_self)

namespace ReturnThen

/-- A block whose first statement returns ends with that return. -/
theorem block_ret {E : Source.Env} {Γ : Source.RCtx} {M : Bool} {k : Source.SCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (n nps : Nat) (ph : Option (Source.Ph E))
    (W : Source.RStmt E [] M k Γ Γ) (e : Source.RExpr E Γ τ)
    (ls l1 : Source.Locals E.layout Γ) (st : Source.St E)
    (hW : (Source.execS G F n nps ph W ls).run (.nil, st) = (.ok (.ret l1), (.nil, st))) :
    (Source.execS G F (n + 2) nps ph (.block (.stmt W (.stmt (.expr e) .nil))) ls).run (.nil, st) =
      (.ok (.ret l1), (.nil, st)) := by
  rw [Source.execS, Source.Hoare.run_bind, Source.execItems, Source.Hoare.run_bind, hW]
  rfl

/-- A block whose first statement completes normally runs the expression after it. -/
theorem block_normal {E : Source.Env} {Γ : Source.RCtx} {M : Bool} {k : Source.SCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (n nps : Nat) (ph : Option (Source.Ph E))
    (W : Source.RStmt E [] M k Γ Γ) (e : Source.RExpr E Γ τ)
    (ls l1 l2 : Source.Locals E.layout Γ) (st : Source.St E) (v : Source.RVal E.layout τ)
    (hW : (Source.execS G F (n + 2) nps ph W ls).run (.nil, st) = (.ok (.normal l1), (.nil, st)))
    (he : (Source.evalE G F n e).run (l1, st) = (.ok v, (l2, st))) :
    (Source.execS G F (n + 4) nps ph (.block (.stmt W (.stmt (.expr e) .nil))) ls).run (.nil, st) =
      (.ok (.normal l2), (.nil, st)) := by
  have he' : Source.evalE G F n e none true (l1, st) = (.ok v, (l2, st)) := he
  rw [Source.execS, Source.Hoare.run_bind, Source.execItems, Source.Hoare.run_bind, hW]
  dsimp only
  rw [Source.Hoare.run_bind, Source.execItems, Source.Hoare.run_bind, Source.execS,
    Source.Hoare.run_bind]
  simp only [Source.EM.sub, ExceptT.run, ExceptT.mk, he', Source.Out.up, Source.Out.close,
    restore_self]
  rfl

/-- The converted literal reset. -/
theorem reset_run {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (ls : Source.Locals E.layout Γ) (st : Source.St E) (a : Source.Idx Γ .bool) :
    (Source.evalE G F (fuel + 3) (.assign (.local a) (.conv (.bool false) (.inl rfl)))).run (ls, st) =
      (.ok (.val (.bool false)), (ls.set a (.bool false), st)) := by
  have eq : Source.evalE G F (fuel + 3) (.assign (.local a) (.conv (.bool false) (.inl rfl))) =
      Source.evalE G F (fuel + 2) (.assign (.local a) (.bool false)) := by
    conv => lhs; rw [Source.evalE]
    rw [Checker.SourceAssociation.identity_eval]
    rfl
  rw [eq]
  exact Solidity.Lowering.G19.AssignmentWhileReset.source_literal G F fuel ls st a

theorem prog_true {C : Contract} {Γ : Ctx} (names : RetFresh) (j b : Idx Γ (.val .bool))
    (σ : State C Γ) (hv : TEnv.get b σ.env = true) :
    (whileReturnThenProg names j b).run σ =
      .ok ⟨((σ.setLocal j true).push (t := .val .bool) false).push (t := .val .bool) true,
        List.prefix_refl _⟩ := by
  have d1 : (Stmt.declLocal .bool names.first (some (.simple (.bool false))) : Stmt C Γ _).run σ =
      .ok ⟨σ.push (t := .val .bool) false, List.prefix_refl _⟩ := rfl
  have d2 : (Stmt.declLocal .bool names.second (some (.simple (.bool false))) :
      Stmt C (.val .bool :: Γ) _).run (σ.push (t := .val .bool) false) =
      .ok ⟨(σ.push (t := .val .bool) false).push (t := .val .bool) false, List.prefix_refl _⟩ := rfl
  rw [whileReturnThenProg, Prog.run_cons_ok d1, Prog.run_cons_ok d2,
    Prog.run_cons_ok (Returns.whileReturn_loop names j b σ true hv)]
  rfl

theorem prog_false {C : Contract} {Γ : Ctx} (names : RetFresh) (j b : Idx Γ (.val .bool))
    (σ : State C Γ) (hv : TEnv.get b σ.env = false) :
    (whileReturnThenProg names j b).run σ =
      .ok ⟨(((σ.setLocal j false).setLocal b false).push (t := .val .bool) true).push
        (t := .val .bool) false, List.prefix_refl _⟩ := by
  have d1 : (Stmt.declLocal .bool names.first (some (.simple (.bool false))) : Stmt C Γ _).run σ =
      .ok ⟨σ.push (t := .val .bool) false, List.prefix_refl _⟩ := rfl
  have d2 : (Stmt.declLocal .bool names.second (some (.simple (.bool false))) :
      Stmt C (.val .bool :: Γ) _).run (σ.push (t := .val .bool) false) =
      .ok ⟨(σ.push (t := .val .bool) false).push (t := .val .bool) false, List.prefix_refl _⟩ := rfl
  rw [whileReturnThenProg, Prog.run_cons_ok d1, Prog.run_cons_ok d2,
    Prog.run_cons_ok (Returns.whileReturn_loop names j b σ false hv)]
  rfl

theorem endpoint {E : Source.Env} {srcΓ : Source.RCtx} {M l u : Bool} {C : Contract}
    {Γ : Ctx} (m : ContextMap srcΓ Γ) (p : Pair m) (x : RetShape.whileReturnThen.Extra E srcΓ C Γ)
    (names : RetFresh) :
    RetEndpoint (RetShape.whileReturnThen.source (M := M) (l := l) (u := u) p x)
      RetShape.whileReturnThen.offset m (RetShape.whileReturnThen.program p x names)
      (RetShape.whileReturnThen.embedding Γ) (RetShape.whileReturnThen.witness Γ) := by
  intro G F fuel nps ph source target R aligned boolReflect falseValue
  obtain ⟨loopRun, related⟩ := Returns.whileReturn_source_run (M := M) (l := l) (u := u) G F
    (fuel + 1) nps ph m p source target (R target.H) aligned (boolReflect target.H)
  have first : m.Related (R target.H)
      (source.1.set p.i (.bool (TEnv.get (boolSlot m p.a p.ha) target.env)))
      (target.setLocal (boolSlot m p.i p.hi) (TEnv.get (boolSlot m p.a p.ha) target.env)).env :=
    fun k => related k
  cases hv : (TEnv.get (boolSlot m p.a p.ha) target.env : Bool) with
  | true =>
    rw [hv] at loopRun first
    refine ⟨_, true, _, block_ret G F (fuel + 5) nps ph _ _ _ _ source.2 loopRun,
      prog_true names _ _ target hv, rfl, ?_, rfl⟩
    intro τ k
    exact first k
  | false =>
    rw [hv] at loopRun first
    have reset := reset_run G F fuel (source.1.set p.i (.bool false)) source.2 p.a
    refine ⟨_, false, _, block_normal G F (fuel + 3) nps ph _ _ _ _ _ source.2 _ loopRun reset,
      prog_false names _ _ target hv, rfl, ?_, rfl⟩
    intro τ k
    exact ContextMap.related_write m (R target.H) _ _ first p.a (boolSlot m p.a p.ha) p.mapA
      (.bool false) false (falseValue target.H) k

end ReturnThen

end Solidity.Correctness.Lowering.Loops
