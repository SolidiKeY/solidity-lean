import Solidity.Correctness.Lowering.Loops.Family
import Solidity.Correctness.Lowering.Checker.SourceAssociation
import Solidity.Lowering.G19.AssignmentForBreak

/-!
# Loop lowering leaf: `for (i = a; ; post) break;`

Target: `lowerLoop` keeps the initializer in front of the loop
(`Lower.lean:486, 502, 522, 533-539`), turns `break` into a flag write (`:452`),
guards the update with the flag (`:515-517`) and the condition with it
(`:518`); elaboration flattens the outer block (`Family.forBreakProg`). The
run is computed generically in the slots, the fresh names and the never-run
update program.

Source: `G19.AssignmentForBreak.correct` (`G19/AssignmentForBreak.lean:64`)
gives the bare Source run; `init_break_transport` below moves it across the
identity conversion that Source resolution keeps in the initializer.
-/
namespace Solidity.Correctness.Lowering.Loops

open Solidity.Lowering.V07
open Solidity.Lowering.G19.AssignmentReturnFlag (boolSlot)

namespace ForBreak

/-- An immediate `break` iteration finishes normally at every horizon from two
on, whatever the update. -/
theorem iter_break {E : Source.Env} {Γ : Source.RCtx} {returns : List Source.STy}
    {modifier u : Bool} (G : Source.Glob E) (F : Source.Fr) (n nps : Nat)
    (ph : Option (Source.Ph E)) (post : Source.ROptExpr E Γ) (ls : Source.Locals E.layout Γ) :
    Source.forIter G F (n + 2) nps ph (R := returns) (M := modifier) (u := u) .none post
      (Source.RStmt.brk : Source.RStmt E returns modifier ⟨true, u⟩ Γ Γ) ls =
      pure (Source.Out.normal ls) := by
  rfl

/-- Horizon transport for an initializer whose condition equation is proved;
the immediate-break iteration does not depend on the horizon. -/
theorem init_break_transport {E : Source.Env} {Γ : Source.RCtx}
    {returns : List Source.STy} {modifier l u : Bool}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (c d : Source.RExpr E Γ .bool) (post : Source.ROptExpr E Γ)
    (condition : Source.evalE G F (fuel + 3) d = Source.evalE G F (fuel + 2) c)
    (ls : Source.Locals E.layout Γ) :
    Source.execS G F (fuel + 5) nps ph (R := returns) (M := modifier)
      (.forLoop (l := l) (u := u) (.expr d) .none post .brk) ls =
    Source.execS G F (fuel + 4) nps ph (R := returns) (M := modifier)
      (.forLoop (l := l) (u := u) (.expr c) .none post .brk) ls := by
  conv => lhs; rw [Source.execS]
  conv => rhs; rw [Source.execS]
  have initD : Source.execS G F (fuel + 4) nps ph (R := returns) (M := modifier)
      (Source.RStmt.expr d : Source.RStmt E returns modifier ⟨true, u⟩ Γ Γ) ls =
      (do let (_, l') ← Source.EM.sub ls (Source.evalE G F (fuel + 3) d)
          pure (Source.Out.normal l')) := rfl
  have initC : Source.execS G F (fuel + 3) nps ph (R := returns) (M := modifier)
      (Source.RStmt.expr c : Source.RStmt E returns modifier ⟨true, u⟩ Γ Γ) ls =
      (do let (_, l') ← Source.EM.sub ls (Source.evalE G F (fuel + 2) c)
          pure (Source.Out.normal l')) := rfl
  simp only [initD, initC, condition, iter_break]

theorem update_skipped {C : Contract} {Γ : Ctx}
    (upd : Option ((Δ : Ctx) × Prog C (.val .bool :: Γ) Δ)) (σ : State C Γ) :
    (forBreakBody upd).run (σ.push (t := .val .bool) false) =
      .ok ⟨σ.push (t := .val .bool) true, List.prefix_refl _⟩ := by
  cases upd <;> rfl

theorem loop_run {C : Contract} {Γ : Ctx}
    (upd : Option ((Δ : Ctx) × Prog C (.val .bool :: Γ) Δ)) (σ : State C Γ) :
    (Stmt.loop .auto flagGuard (forBreakBody upd)).run (σ.push (t := .val .bool) false) =
      .ok ⟨σ.push (t := .val .bool) true, List.prefix_refl _⟩ := by
  have enter : (flagGuard : Val C (.val .bool :: Γ) .bool).evalT (σ.push (t := .val .bool) false) =
      .ok true := rfl
  have body := update_skipped upd σ
  rw [Stmt.run_loop]
  apply TLoop.run_of_iterN (n := 2)
  cases upd <;>
  · simp only [TLoop.iterN, TLoop.step]
    rw [enter]
    simp only [body]
    rfl

/-- The lowered program, for every context, slot pair, fresh names, update and state. -/
theorem prog_run {C : Contract} {Γ : Ctx} (names : Fresh) (j b : Idx Γ (.val .bool))
    (upd : Option ((Δ : Ctx) × Prog C (.val .bool :: Γ) Δ)) (σ : State C Γ) :
    (forBreakProg names j b upd).run σ =
      .ok ⟨(σ.setLocal j (TEnv.get b σ.env)).push (t := .val .bool) true, List.prefix_refl _⟩ := by
  have assign : (Stmt.assignLocal j (.simple (.local b)) : Stmt C Γ Γ).run σ =
      .ok ⟨σ.setLocal j (TEnv.get b σ.env), List.prefix_refl _⟩ := rfl
  have decl : (Stmt.declLocal .bool names.flag (some (.simple (.bool false))) :
      Stmt C Γ _).run (σ.setLocal j (TEnv.get b σ.env)) =
      .ok ⟨(σ.setLocal j (TEnv.get b σ.env)).push (t := .val .bool) false, List.prefix_refl _⟩ := rfl
  rw [forBreakProg, Prog.run_cons_ok assign, Prog.run_cons_ok decl,
    Prog.run_cons_ok (loop_run upd _), Prog.run_nil]
  rfl

/-- Leaf soundness: the family member reaches the endpoint. -/
theorem endpoint {E : Source.Env} {srcΓ : Source.RCtx} {returns : List Source.STy}
    {M l u : Bool} {C : Contract} {Γ : Ctx} (m : ContextMap srcΓ Γ) (p : Pair m)
    (x : Shape.forBreak.Extra E srcΓ C Γ) (names : Fresh) :
    Endpoint (Shape.forBreak.source (returns := returns) (M := M) (l := l) (u := u) p x)
      Shape.forBreak.offset m
      (forBreakProg names (boolSlot m p.i p.hi) (boolSlot m p.a p.ha) x.2)
      (.drop .refl) := by
  intro G F fuel nps ph source target R aligned boolReflect
  have leaf := Solidity.Lowering.G19.AssignmentForBreak.correct G F fuel nps ph
    (returns := returns) (M := M) (l := l) (u := u) source target m (R target.H) aligned
    (boolReflect target.H) p.i p.a p.hi p.ha p.mapI p.mapA x.1
  obtain ⟨sourceRun, -, related, -⟩ := leaf
  refine ⟨source.1.set p.i (.bool (TEnv.get (boolSlot m p.a p.ha) target.env)), _, ?_,
    prog_run names _ _ x.2 target, ?_, rfl⟩
  · change (Source.execS G F (fuel + 5) nps ph (.forLoop (l := l) (u := u)
      (.expr (.assign (.local p.i) (.conv (.local p.a) (.inl rfl)))) .none x.1 .brk) source.1).run
        (.nil, source.2) = _
    rw [init_break_transport G F fuel nps ph _ _ x.1
      (Checker.SourceAssociation.local_assignment_identity G F fuel p.i p.a (.inl rfl))]
    exact sourceRun
  · intro τ k
    exact related k

end ForBreak

end Solidity.Correctness.Lowering.Loops
