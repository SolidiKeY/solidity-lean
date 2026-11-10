import Solidity.Correctness.Lowering.Loops.Family
import Solidity.Correctness.Lowering.Loops.Horizon
import Solidity.Lowering.G19.AssignmentWhileContinue

/-!
# Loop lowering leaf: `while (i = a) { a = false; continue; tail }`

Target: the condition moves into the body (`Lower.lean:493-496`), `continue`
becomes a flag write (`:453`), the items after it are dropped (`:427`), the
continue flag is reset per iteration (`:513`) and the condition is guarded by
the break flag (`:518`); `Family.whileContinueProg`. A true right-hand side
runs two iterations (the reset makes the second test false), a false one runs
one. Computed generically in the slots and fresh names.

Source: `G19.AssignmentWhileContinue.correct`
(`G19/AssignmentWhileContinue.lean:86`) gives the bare Source run;
`Horizon.while_below` moves it across the identity conversions Source typing
keeps in the condition and in `a = false`, for every dropped tail.
-/
namespace Solidity.Correctness.Lowering.Loops

open Solidity.Lowering.V07
open Solidity.Lowering.G19.AssignmentReturnFlag (boolSlot)

namespace WhileContinue

/-- Iteration tail on a true capture: the reset runs, no break. -/
theorem tail_true {C : Contract} {Γ : Ctx} (j b : Idx Γ (.val .bool)) (σ : State C Γ) :
    (whileContinueTail j b).run (((σ.push (t := .val .bool) false).push (t := .val .bool) false).push
      (t := .val .bool) true) =
      .ok ⟨(((((σ.setLocal j true).setLocal b false).push (t := .val .bool) false).push
        (t := .val .bool) true).push (t := .val .bool) true), List.prefix_refl _⟩ := by
  rfl

/-- Iteration tail on a false capture: break. -/
theorem tail_false {C : Contract} {Γ : Ctx} (j b : Idx Γ (.val .bool)) (σ : State C Γ) :
    (whileContinueTail j b).run (((σ.push (t := .val .bool) false).push (t := .val .bool) false).push
      (t := .val .bool) false) =
      .ok ⟨((((σ.setLocal j false).push (t := .val .bool) true).push
        (t := .val .bool) false).push (t := .val .bool) false), List.prefix_refl _⟩ := by
  rfl

theorem body_prefix {C : Contract} {Γ : Ctx} (cnt se : Var) (j b : Idx Γ (.val .bool))
    (σ : State C Γ) :
    (whileContinueBody cnt se j b).run (σ.push (t := .val .bool) false) =
      (whileContinueTail j b).run (((σ.push (t := .val .bool) false).push (t := .val .bool) false).push
        (t := .val .bool) (TEnv.get b σ.env)) := by
  have decl1 : (Stmt.declLocal .bool cnt (some (.simple (.bool false))) :
      Stmt C (.val .bool :: Γ) _).run (σ.push (t := .val .bool) false) =
      .ok ⟨(σ.push (t := .val .bool) false).push (t := .val .bool) false, List.prefix_refl _⟩ := rfl
  have decl2 : (Stmt.declLocal .bool se (some (.simple (.local b.there.there))) :
      Stmt C (.val .bool :: .val .bool :: Γ) _).run
        ((σ.push (t := .val .bool) false).push (t := .val .bool) false) =
      .ok ⟨((σ.push (t := .val .bool) false).push (t := .val .bool) false).push
        (t := .val .bool) (TEnv.get b σ.env), List.prefix_refl _⟩ := rfl
  rw [whileContinueBody, Prog.run_cons_ok decl1, Prog.run_cons_ok decl2]
  cases (whileContinueTail j b).run (((σ.push (t := .val .bool) false).push
    (t := .val .bool) false).push (t := .val .bool) (TEnv.get b σ.env)) <;> rfl

theorem loop_false {C : Contract} {Γ : Ctx} (cnt se : Var) (j b : Idx Γ (.val .bool))
    (σ : State C Γ) (hv : TEnv.get b σ.env = false) :
    (Stmt.loop .auto flagGuard (whileContinueBody cnt se j b)).run (σ.push (t := .val .bool) false) =
      .ok ⟨(σ.setLocal j false).push (t := .val .bool) true, List.prefix_refl _⟩ := by
  have enter : (flagGuard : Val C (.val .bool :: Γ) .bool).evalT
      (σ.push (t := .val .bool) false) = .ok true := rfl
  rw [Stmt.run_loop]
  apply TLoop.run_of_iterN (n := 2)
  simp only [TLoop.iterN, TLoop.step]
  rw [enter, body_prefix, hv, tail_false]
  rfl

theorem loop_true {C : Contract} {Γ : Ctx} (cnt se : Var) (j b : Idx Γ (.val .bool))
    (σ : State C Γ) (hv : TEnv.get b σ.env = true) :
    (Stmt.loop .auto flagGuard (whileContinueBody cnt se j b)).run (σ.push (t := .val .bool) false) =
      .ok ⟨(((σ.setLocal j true).setLocal b false).setLocal j false).push (t := .val .bool) true,
        List.prefix_refl _⟩ := by
  have enter (τ : State C Γ) : (flagGuard : Val C (.val .bool :: Γ) .bool).evalT
      (τ.push (t := .val .bool) false) = .ok true := rfl
  have hv2 : TEnv.get b ((σ.setLocal j true).setLocal b false).env = false := TEnv.get_set ..
  have second := loop_false cnt se j b ((σ.setLocal j true).setLocal b false) hv2
  rw [Stmt.run_loop] at second ⊢
  rw [TLoop.run_unfold]
  simp only [TLoop.step]
  rw [enter, body_prefix, hv, tail_true]
  exact second

theorem prog_false {C : Contract} {Γ : Ctx} (brk cnt se : Var) (j b : Idx Γ (.val .bool))
    (σ : State C Γ) (hv : TEnv.get b σ.env = false) :
    (whileContinueProg brk cnt se j b).run σ =
      .ok ⟨(σ.setLocal j false).push (t := .val .bool) true, List.prefix_refl _⟩ := by
  have decl : (Stmt.declLocal .bool brk (some (.simple (.bool false))) : Stmt C Γ _).run σ =
      .ok ⟨σ.push (t := .val .bool) false, List.prefix_refl _⟩ := rfl
  rw [whileContinueProg, Prog.run_cons_ok decl, Prog.run_cons_ok (loop_false cnt se j b σ hv),
    Prog.run_nil]
  rfl

theorem prog_true {C : Contract} {Γ : Ctx} (brk cnt se : Var) (j b : Idx Γ (.val .bool))
    (σ : State C Γ) (hv : TEnv.get b σ.env = true) :
    (whileContinueProg brk cnt se j b).run σ =
      .ok ⟨(((σ.setLocal j true).setLocal b false).setLocal j false).push (t := .val .bool) true,
        List.prefix_refl _⟩ := by
  have decl : (Stmt.declLocal .bool brk (some (.simple (.bool false))) : Stmt C Γ _).run σ =
      .ok ⟨σ.push (t := .val .bool) false, List.prefix_refl _⟩ := rfl
  rw [whileContinueProg, Prog.run_cons_ok decl, Prog.run_cons_ok (loop_true cnt se j b σ hv),
    Prog.run_nil]
  rfl

/-- The converted Source loop completes as G19's bare loop, one horizon later. -/
theorem source_below {E : Source.Env} {srcΓ tailΓ : Source.RCtx} {returns : List Source.STy}
    {M l u : Bool} (G : Source.Glob E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph E))
    (i a : Source.Idx srcΓ .bool) (tail : Source.RItems E returns M ⟨true, u⟩ srcΓ tailΓ) (n : Nat)
    (ls : Source.Locals E.layout srcΓ) :
    Source.Below
      (Source.execS G F n nps ph (Solidity.Lowering.G19.AssignmentWhileContinue.statement
        (l := l) i a tail) ls)
      (Source.execS G F (n + 1) nps ph (R := returns) (M := M)
        (.whileLoop (l := l) (.assign (.local i) (.conv (.local a) (.inl rfl)))
          (.block (.stmt (.expr (.assign (.local a) (.conv (.bool false) (.inl rfl))))
            (.stmt .cont tail)))) ls) :=
  Horizon.while_below G F nps ph _ _ _ _ (Horizon.assign_below G F i a)
    (Horizon.block_below G F nps ph _ _
      (Horizon.items_below G F nps ph _ _ _
        (Horizon.expr_below G F nps ph _ _ (Horizon.assign_lit_below G F a false (.inl rfl))))) n ls

/-- Leaf soundness: the family member reaches the endpoint. -/
theorem endpoint {E : Source.Env} {srcΓ : Source.RCtx} {returns : List Source.STy}
    {M l u : Bool} {C : Contract} {Γ : Ctx} (m : ContextMap srcΓ Γ) (p : Pair m)
    (x : Shape.whileContinue.Extra E returns M u srcΓ C Γ) (names : Fresh) :
    Endpoint (Shape.whileContinue.source (l := l) p x) Shape.whileContinue.offset m
      (whileContinueProg (C := C) names.flag x.1 names.capture (boolSlot m p.i p.hi)
        (boolSlot m p.a p.ha))
      (.drop .refl) := by
  intro G F fuel nps ph source target R aligned boolReflect falseValue
  have leaf := Solidity.Lowering.G19.AssignmentWhileContinue.correct G F fuel nps ph
    (returns := returns) (M := M) (l := l) (u := u) source target m (R target.H) aligned
    (boolReflect target.H) (falseValue target.H) p.i p.a p.hi p.ha p.mapI p.mapA x.2.2
  dsimp only at leaf
  obtain ⟨sourceRun, -, related, -⟩ := leaf
  have sourceRun' := (Source.Below.eq_of_done
    (source_below (l := l) G F nps ph p.i p.a x.2.2 (fuel + 8) source.1) (.nil, source.2)
    (by rw [sourceRun]; intro h; cases h)).trans sourceRun
  cases hv : (TEnv.get (boolSlot m p.a p.ha) target.env : Bool) with
  | false =>
    refine ⟨_, _, sourceRun', prog_false _ _ _ _ _ target hv, ?_, rfl⟩
    intro τ k
    have r := related k
    revert r
    unfold Solidity.Lowering.G19.AssignmentWhileReset.targetAfter
    dsimp only
    rw [hv]
    exact id
  | true =>
    refine ⟨_, _, sourceRun', prog_true _ _ _ _ _ target hv, ?_, rfl⟩
    intro τ k
    have r := related k
    revert r
    unfold Solidity.Lowering.G19.AssignmentWhileReset.targetAfter
    dsimp only
    rw [hv]
    exact id

end WhileContinue

end Solidity.Correctness.Lowering.Loops
