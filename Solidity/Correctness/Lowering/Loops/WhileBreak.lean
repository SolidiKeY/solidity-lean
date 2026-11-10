import Solidity.Correctness.Lowering.Loops.Family
import Solidity.Correctness.Lowering.Checker.SourceAssociation

/-!
# Loop lowering leaf: `while (i = a) break;`

Target: the actual flag lowering (`Lower.lean:493-496` moves the effectful
condition into the body as `if (!(i = a)) break;`, then `:452` turns `break`
into a flag write, `:429-431` guards the suffix, `:518` guards the
condition and `:522` declares the flag), as intrinsic elaboration emits it
(`Family.whileBreakProg`). Its run is computed generically: one iteration sets
the flag on both Boolean paths, the second guard test exits.

Source: `G19.AssignmentWhileBreak.correct` (`G19/AssignmentWhileBreak.lean:74`)
gives the bare Source run; `Checker.SourceAssociation.immediate_break_transport`
moves it across the identity conversion that Source resolution keeps. The
mapped post relation is G19's, weakened past the retained flag.
-/
namespace Solidity.Correctness.Lowering.Loops

open Solidity.Lowering.V07
open Solidity.Lowering.G19.AssignmentReturnFlag (boolSlot)

namespace WhileBreak

theorem tail_run {C : Contract} {Γ : Ctx} (j : Idx Γ (.val .bool)) (σ : State C Γ) (v : Bool) :
    (whileBreakTail j).run ((σ.push (t := .val .bool) false).push (t := .val .bool) v) =
      .ok ⟨((σ.setLocal j v).push (t := .val .bool) true).push (t := .val .bool) v,
        List.prefix_refl _⟩ := by
  cases v <;> rfl

theorem body_run {C : Contract} {Γ : Ctx} (se : Var) (j b : Idx Γ (.val .bool)) (σ : State C Γ) :
    (whileBreakBody se j b).run (σ.push (t := .val .bool) false) =
      .ok ⟨((σ.setLocal j (TEnv.get b σ.env)).push (t := .val .bool) true).push
        (t := .val .bool) (TEnv.get b σ.env), List.prefix_refl _⟩ := by
  have decl : (Stmt.declLocal .bool se (some (.simple (.local b.there))) :
      Stmt C (.val .bool :: Γ) _).run (σ.push (t := .val .bool) false) =
      .ok ⟨(σ.push (t := .val .bool) false).push (t := .val .bool) (TEnv.get b σ.env),
        List.prefix_refl _⟩ := rfl
  rw [whileBreakBody, Prog.run_cons_ok decl, tail_run]
  rfl

/-- Two guard tests and one iteration, on every Boolean path. -/
theorem loop_run {C : Contract} {Γ : Ctx} (se : Var) (j b : Idx Γ (.val .bool)) (σ : State C Γ) :
    (Stmt.loop .auto flagGuard (whileBreakBody se j b)).run (σ.push (t := .val .bool) false) =
      .ok ⟨(σ.setLocal j (TEnv.get b σ.env)).push (t := .val .bool) true, List.prefix_refl _⟩ := by
  rw [Stmt.run_loop]
  apply TLoop.run_of_iterN (n := 2)
  simp only [TLoop.iterN, TLoop.step]
  have enter : (flagGuard : Val C (.val .bool :: Γ) .bool).evalT (σ.push (t := .val .bool) false) =
      .ok true := rfl
  rw [enter]
  simp only [body_run]
  rfl

/-- The lowered program, for every context, slot pair, fresh names and state. -/
theorem prog_run {C : Contract} {Γ : Ctx} (names : Fresh) (j b : Idx Γ (.val .bool))
    (σ : State C Γ) :
    (whileBreakProg names j b).run σ =
      .ok ⟨(σ.setLocal j (TEnv.get b σ.env)).push (t := .val .bool) true, List.prefix_refl _⟩ := by
  have decl : (Stmt.declLocal .bool names.flag (some (.simple (.bool false))) :
      Stmt C Γ _).run σ = .ok ⟨σ.push (t := .val .bool) false, List.prefix_refl _⟩ := rfl
  rw [whileBreakProg, Prog.run_cons_ok decl, Prog.run_cons_ok (loop_run names.capture j b σ),
    Prog.run_nil]
  rfl

/-- Leaf soundness: the family member reaches the endpoint. -/
theorem endpoint {E : Source.Env} {srcΓ : Source.RCtx} {returns : List Source.STy}
    {M l u : Bool} {C : Contract} {Γ : Ctx} (m : ContextMap srcΓ Γ) (p : Pair m)
    (names : Fresh) :
    Endpoint (Shape.whileBreak.source (E := E) (C := C) (returns := returns) (M := M) (l := l)
        (u := u) p ())
      Shape.whileBreak.offset m
      (whileBreakProg (C := C) names (boolSlot m p.i p.hi) (boolSlot m p.a p.ha))
      (.drop .refl) := by
  intro G F fuel nps ph source target R aligned boolReflect _
  have leaf := Solidity.Lowering.G19.AssignmentWhileBreak.correct G F fuel nps ph
    (returns := returns) (M := M) (l := l) (u := u) source target m (R target.H) aligned
    (boolReflect target.H) p.i p.a p.hi p.ha p.mapI p.mapA
  obtain ⟨sourceRun, -, related, -⟩ := leaf
  refine ⟨source.1.set p.i (.bool (TEnv.get (boolSlot m p.a p.ha) target.env)), _, ?_,
    prog_run names _ _ target, ?_, rfl⟩
  · change (Source.execS G F (fuel + 4) nps ph (.whileLoop (l := l) (u := u)
      (.assign (.local p.i) (.conv (.local p.a) (.inl rfl))) .brk) source.1).run
        (.nil, source.2) = _
    rw [Checker.SourceAssociation.immediate_break_transport G F fuel nps ph _ _
      (Checker.SourceAssociation.local_assignment_identity G F fuel p.i p.a (.inl rfl))]
    exact sourceRun
  · intro τ k
    exact related k

end WhileBreak

end Solidity.Correctness.Lowering.Loops
