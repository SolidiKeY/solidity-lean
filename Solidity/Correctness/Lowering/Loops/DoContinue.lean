import Solidity.Correctness.Lowering.Loops.Family
import Solidity.Correctness.Lowering.Loops.Horizon
import Solidity.Lowering.G19.AssignmentDoWhileContinue

/-!
# Loop lowering leaf: `do { i = a; continue; tail } while (false);`

Target: the first-iteration flag (`Lower.lean:507-512`), the per-iteration
continue flag (`:513`), `continue` as a flag write (`:453`) and the dropped
items after it (`:427`); with no break or return there is no guard (`:518`).
`Family.doContinueProg` runs the body once, then the literal `false` ends it.

Source: `G19.AssignmentDoWhileContinue.correct`
(`G19/AssignmentDoWhileContinue.lean:76`) through `Horizon.doWhile_below`, for
every dropped tail.
-/
namespace Solidity.Correctness.Lowering.Loops

open Solidity.Lowering.V07
open Solidity.Lowering.G19.AssignmentReturnFlag (boolSlot)

namespace DoContinue

theorem loop_run {C : Contract} {Γ : Ctx} (cnt : Var) (j b : Idx Γ (.val .bool)) (σ : State C Γ) :
    (Stmt.loop .auto (.binop .or rfl rfl (.simple (.local .here)) (.simple (.bool false)))
      (.cons (.assignLocal .here (.simple (.bool false)))
        (.cons (.declLocal .bool cnt (some (.simple (.bool false))))
          (.cons (.assignLocal j.there.there (.simple (.local b.there.there)))
            (.cons (.assignLocal .here (.simple (.bool true))) .nil)))) :
        Stmt C (.val .bool :: Γ) _).run (σ.push (t := .val .bool) true) =
      .ok ⟨(σ.setLocal j (TEnv.get b σ.env)).push (t := .val .bool) false, List.prefix_refl _⟩ := by
  rw [Stmt.run_loop]
  apply TLoop.run_of_iterN (n := 2)
  rfl

theorem prog_run {C : Contract} {Γ : Ctx} (first cnt : Var) (j b : Idx Γ (.val .bool))
    (σ : State C Γ) :
    (doContinueProg first cnt j b).run σ =
      .ok ⟨(σ.setLocal j (TEnv.get b σ.env)).push (t := .val .bool) false, List.prefix_refl _⟩ := by
  have decl : (Stmt.declLocal .bool first (some (.simple (.bool true))) : Stmt C Γ _).run σ =
      .ok ⟨σ.push (t := .val .bool) true, List.prefix_refl _⟩ := rfl
  rw [doContinueProg, Prog.run_cons_ok decl, Prog.run_cons_ok (loop_run cnt j b σ), Prog.run_nil]
  rfl

/-- Leaf soundness: the family member reaches the endpoint. -/
theorem endpoint {E : Source.Env} {srcΓ : Source.RCtx} {returns : List Source.STy}
    {M l u : Bool} {C : Contract} {Γ : Ctx} (m : ContextMap srcΓ Γ) (p : Pair m)
    (x : Shape.doContinue.Extra E returns M u srcΓ C Γ) (names : Fresh) :
    Endpoint (Shape.doContinue.source (C := C) (l := l) p x) Shape.doContinue.offset m
      (doContinueProg (C := C) names.flag x.1 (boolSlot m p.i p.hi) (boolSlot m p.a p.ha))
      (.drop .refl) := by
  intro G F fuel nps ph source target R aligned boolReflect _
  have leaf := Solidity.Lowering.G19.AssignmentDoWhileContinue.correct G F fuel nps ph
    (returns := returns) (M := M) (l := l) (u := u) source target m (R target.H) aligned
    (boolReflect target.H) p.i p.a p.hi p.ha p.mapI p.mapA x.2.2
  obtain ⟨sourceRun, -, related, -⟩ := leaf
  unfold Solidity.Lowering.G19.AssignmentDoWhileContinue.body at sourceRun
  have below := Horizon.doWhile_below (lp := l) (R := returns) (M := M) (u := u) G F nps ph
    (.bool false) _ _
    (Horizon.block_below G F nps ph _ _
      (Horizon.items_below G F nps ph _ _ (.stmt .cont x.2.2)
        (Horizon.expr_below G F nps ph _ _ (Horizon.assign_below G F p.i p.a))))
    (fuel + 6) source.1
  have sourceRun' := (Source.Below.eq_of_done below (.nil, source.2)
    (by rw [sourceRun]; intro h; cases h)).trans sourceRun
  refine ⟨_, _, sourceRun', prog_run _ _ _ _ target, ?_, rfl⟩
  intro τ k
  exact related k

end DoContinue

end Solidity.Correctness.Lowering.Loops
