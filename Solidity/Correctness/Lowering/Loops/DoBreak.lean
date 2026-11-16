import Solidity.Correctness.Lowering.Loops.Family
import Solidity.Correctness.Lowering.Loops.Horizon
import Solidity.Lowering.G19.AssignmentDoWhileBreak

/-!
# Loop lowering leaf: `do { i = a; break; } while (c);`

Target: `lowerLoop` adds the first-iteration flag and disjunction
(`Lower.lean:507-512`), turns `break` into a flag write (`:452`), guards the
condition with the break flag (`:518`) and declares it (`:522`);
`Family.doBreakProg`. Both guard tests short-circuit, so neither the lowered
nor the Source condition is evaluated: the run is computed generically in the
slots, the names and an arbitrary condition.

Source: `G19.AssignmentDoWhileBreak.correct` (`G19/AssignmentDoWhileBreak.lean:74`)
gives the bare Source run; `Horizon.doWhile_below` moves it across the identity
conversion Source typing keeps in the body's assignment.
-/
namespace Solidity.Correctness.Lowering.Loops

open Solidity.Lowering.V07
open Solidity.Lowering.G19.AssignmentReturnFlag (boolSlot)

namespace DoBreak

theorem loop_run {C : Contract} {Γ : Ctx} (j b : Idx Γ (.val .bool))
    (c : Val C (.val .bool :: .val .bool :: Γ) .bool) (σ : State C Γ) :
    (Stmt.loop .auto (.binop .and rfl rfl (notB (.simple (.local .here)))
          (.binop .or rfl rfl (.simple (.local Idx.here.there)) c))
        (.cons (.assignLocal Idx.here.there (.simple (.bool false)))
          (.cons (.assignLocal j.there.there (.simple (.local b.there.there)))
            (.cons (.assignLocal .here (.simple (.bool true))) .nil))) :
        Stmt C (.val .bool :: .val .bool :: Γ) _).run
      ((σ.push (t := .val .bool) true).push (t := .val .bool) false) =
      .ok ⟨((σ.setLocal j (TEnv.get b σ.env)).push (t := .val .bool) false).push
        (t := .val .bool) true, List.prefix_refl _⟩ := by
  rw [Stmt.run_loop]
  apply TLoop.run_of_iterN (n := 2)
  rfl

theorem prog_run {C : Contract} {Γ : Ctx} (first brk : Var) (j b : Idx Γ (.val .bool))
    (c : Val C (.val .bool :: .val .bool :: Γ) .bool) (σ : State C Γ) :
    (doBreakProg first brk j b c).run σ =
      .ok ⟨((σ.setLocal j (TEnv.get b σ.env)).push (t := .val .bool) false).push
        (t := .val .bool) true, List.prefix_refl _⟩ := by
  have d1 : (Stmt.declLocal .bool first (some (.simple (.bool true))) : Stmt C Γ _).run σ =
      .ok ⟨σ.push (t := .val .bool) true, List.prefix_refl _⟩ := rfl
  have d2 : (Stmt.declLocal .bool brk (some (.simple (.bool false))) :
      Stmt C (.val .bool :: Γ) _).run (σ.push (t := .val .bool) true) =
      .ok ⟨(σ.push (t := .val .bool) true).push (t := .val .bool) false, List.prefix_refl _⟩ := rfl
  rw [doBreakProg, Prog.run_cons_ok d1, Prog.run_cons_ok d2, Prog.run_cons_ok (loop_run j b c σ),
    Prog.run_nil]
  rfl

/-- Leaf soundness: the family member reaches the endpoint. -/
theorem endpoint {E : Source.Env} {srcΓ : Source.RCtx} {returns : List Source.STy}
    {M l u : Bool} {C : Contract} {Γ : Ctx} (m : ContextMap srcΓ Γ) (p : Pair m)
    (x : Shape.doBreak.Extra E returns M u srcΓ C Γ) (names : Fresh) :
    Endpoint (Shape.doBreak.source (returns := returns) (M := M) (l := l) (u := u) p x)
      Shape.doBreak.offset m
      (doBreakProg x.1 names.flag (boolSlot m p.i p.hi) (boolSlot m p.a p.ha) x.2.2)
      (.drop (.drop .refl)) := by
  intro G F fuel nps ph source target R aligned boolReflect _
  have leaf := Solidity.Lowering.G19.AssignmentDoWhileBreak.correct G F fuel nps ph
    (returns := returns) (M := M) (l := l) (u := u) source target m (R target.H) aligned
    (boolReflect target.H) p.i p.a p.hi p.ha p.mapI p.mapA x.2.1
  obtain ⟨sourceRun, -, related, -⟩ := leaf
  unfold Solidity.Lowering.G19.AssignmentDoWhileBreak.body at sourceRun
  have below := Horizon.doWhile_below (lp := l) (R := returns) (M := M) (u := u) G F nps ph
    x.2.1 _ _
    (Horizon.block_below G F nps ph _ _
      (Horizon.items_below G F nps ph _ _ (.stmt .brk .nil)
        (Horizon.expr_below G F nps ph _ _ (Horizon.assign_below G F p.i p.a))))
    (fuel + 6) source.1
  have sourceRun' := (Source.Below.eq_of_done below (.nil, source.2)
    (by rw [sourceRun]; intro h; cases h)).trans sourceRun
  refine ⟨_, _, sourceRun', prog_run _ _ _ _ x.2.2 target, ?_, rfl⟩
  intro τ k
  exact related k

end DoBreak

end Solidity.Correctness.Lowering.Loops
