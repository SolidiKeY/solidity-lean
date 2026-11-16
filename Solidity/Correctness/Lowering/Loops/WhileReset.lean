import Solidity.Correctness.Lowering.Loops.Family
import Solidity.Correctness.Lowering.Loops.Horizon
import Solidity.Lowering.G19.AssignmentWhileReset

/-!
# Loop lowering leaf: `while (i = a) a = false;`

Target: the condition moves into the body (`Lower.lean:493-496`), the old body
runs under `!brk` (`:429-431`), the condition is guarded (`:518`) and the flag
declared (`:522`); `Family.whileResetProg`. A true right-hand side runs two
iterations (the reset makes the second capture false), a false one runs one.

Source: `G19.AssignmentWhileReset.correct` (`G19/AssignmentWhileReset.lean:205`)
through `Horizon.while_below`.
-/
namespace Solidity.Correctness.Lowering.Loops

open Solidity.Lowering.V07
open Solidity.Lowering.G19.AssignmentReturnFlag (boolSlot)

namespace WhileReset

/-- Body after the capture declaration. -/
def tail {C : Contract} {Γ : Ctx} (j b : Idx Γ (.val .bool)) :
    Prog C (.val .bool :: .val .bool :: Γ) (.val .bool :: .val .bool :: Γ) :=
  .cons (.assignLocal j.there.there (.simple (.local .here)))
    (.cons (.ite (notB (.simple (.local .here)))
        (.cons (.assignLocal Idx.here.there (.simple (.bool true))) .nil) .nil)
      (.cons (.ite (notB (.simple (.local Idx.here.there)))
          (.cons (.assignLocal b.there.there (.simple (.bool false))) .nil) .nil)
        .nil))

def body {C : Contract} {Γ : Ctx} (se : Var) (j b : Idx Γ (.val .bool)) :
    Prog C (.val .bool :: Γ) (.val .bool :: .val .bool :: Γ) :=
  .cons (.declLocal .bool se (some (.simple (.local b.there)))) (tail j b)

theorem prog_eq {C : Contract} {Γ : Ctx} (brk se : Var) (j b : Idx Γ (.val .bool)) :
    (whileResetProg brk se j b : Prog C Γ _) =
      .cons (.declLocal .bool brk (some (.simple (.bool false))))
        (.cons (.loop .auto flagGuard (body se j b)) .nil) := rfl

theorem tail_true {C : Contract} {Γ : Ctx} (j b : Idx Γ (.val .bool)) (σ : State C Γ) :
    (tail j b).run ((σ.push (t := .val .bool) false).push (t := .val .bool) true) =
      .ok ⟨((((σ.setLocal j true).setLocal b false).push (t := .val .bool) false).push
        (t := .val .bool) true), List.prefix_refl _⟩ := by
  rfl

theorem tail_false {C : Contract} {Γ : Ctx} (j b : Idx Γ (.val .bool)) (σ : State C Γ) :
    (tail j b).run ((σ.push (t := .val .bool) false).push (t := .val .bool) false) =
      .ok ⟨(((σ.setLocal j false).push (t := .val .bool) true).push (t := .val .bool) false),
        List.prefix_refl _⟩ := by
  rfl

theorem body_prefix {C : Contract} {Γ : Ctx} (se : Var) (j b : Idx Γ (.val .bool))
    (σ : State C Γ) :
    (body se j b).run (σ.push (t := .val .bool) false) =
      (tail j b).run ((σ.push (t := .val .bool) false).push (t := .val .bool) (TEnv.get b σ.env)) := by
  have decl : (Stmt.declLocal .bool se (some (.simple (.local b.there))) :
      Stmt C (.val .bool :: Γ) _).run (σ.push (t := .val .bool) false) =
      .ok ⟨(σ.push (t := .val .bool) false).push (t := .val .bool) (TEnv.get b σ.env),
        List.prefix_refl _⟩ := rfl
  rw [body, Prog.run_cons_ok decl]
  cases (tail j b).run ((σ.push (t := .val .bool) false).push
    (t := .val .bool) (TEnv.get b σ.env)) <;> rfl

theorem loop_false {C : Contract} {Γ : Ctx} (se : Var) (j b : Idx Γ (.val .bool))
    (σ : State C Γ) (hv : TEnv.get b σ.env = false) :
    (Stmt.loop .auto flagGuard (body se j b)).run (σ.push (t := .val .bool) false) =
      .ok ⟨(σ.setLocal j false).push (t := .val .bool) true, List.prefix_refl _⟩ := by
  have enter : (flagGuard : Val C (.val .bool :: Γ) .bool).evalT
      (σ.push (t := .val .bool) false) = .ok true := rfl
  rw [Stmt.run_loop]
  apply TLoop.run_of_iterN (n := 2)
  simp only [TLoop.iterN, TLoop.step]
  rw [enter, body_prefix, hv, tail_false]
  rfl

theorem loop_true {C : Contract} {Γ : Ctx} (se : Var) (j b : Idx Γ (.val .bool))
    (σ : State C Γ) (hv : TEnv.get b σ.env = true) :
    (Stmt.loop .auto flagGuard (body se j b)).run (σ.push (t := .val .bool) false) =
      .ok ⟨(((σ.setLocal j true).setLocal b false).setLocal j false).push (t := .val .bool) true,
        List.prefix_refl _⟩ := by
  have enter (τ : State C Γ) : (flagGuard : Val C (.val .bool :: Γ) .bool).evalT
      (τ.push (t := .val .bool) false) = .ok true := rfl
  have hv2 : TEnv.get b ((σ.setLocal j true).setLocal b false).env = false := TEnv.get_set ..
  have second := loop_false se j b ((σ.setLocal j true).setLocal b false) hv2
  rw [Stmt.run_loop] at second ⊢
  rw [TLoop.run_unfold]
  simp only [TLoop.step]
  rw [enter, body_prefix, hv, tail_true]
  exact second

theorem prog_false {C : Contract} {Γ : Ctx} (brk se : Var) (j b : Idx Γ (.val .bool))
    (σ : State C Γ) (hv : TEnv.get b σ.env = false) :
    (whileResetProg brk se j b).run σ =
      .ok ⟨(σ.setLocal j false).push (t := .val .bool) true, List.prefix_refl _⟩ := by
  have decl : (Stmt.declLocal .bool brk (some (.simple (.bool false))) : Stmt C Γ _).run σ =
      .ok ⟨σ.push (t := .val .bool) false, List.prefix_refl _⟩ := rfl
  rw [prog_eq, Prog.run_cons_ok decl, Prog.run_cons_ok (loop_false se j b σ hv), Prog.run_nil]
  rfl

theorem prog_true {C : Contract} {Γ : Ctx} (brk se : Var) (j b : Idx Γ (.val .bool))
    (σ : State C Γ) (hv : TEnv.get b σ.env = true) :
    (whileResetProg brk se j b).run σ =
      .ok ⟨(((σ.setLocal j true).setLocal b false).setLocal j false).push (t := .val .bool) true,
        List.prefix_refl _⟩ := by
  have decl : (Stmt.declLocal .bool brk (some (.simple (.bool false))) : Stmt C Γ _).run σ =
      .ok ⟨σ.push (t := .val .bool) false, List.prefix_refl _⟩ := rfl
  rw [prog_eq, Prog.run_cons_ok decl, Prog.run_cons_ok (loop_true se j b σ hv), Prog.run_nil]
  rfl

/-- Leaf soundness: the family member reaches the endpoint. -/
theorem endpoint {E : Source.Env} {srcΓ : Source.RCtx} {returns : List Source.STy}
    {M l u : Bool} {C : Contract} {Γ : Ctx} (m : ContextMap srcΓ Γ) (p : Pair m)
    (x : Shape.whileReset.Extra E returns M u srcΓ C Γ) (names : Fresh) :
    Endpoint (Shape.whileReset.source (C := C) (returns := returns) (M := M) (l := l) (u := u) p x)
      Shape.whileReset.offset m
      (whileResetProg (C := C) names.flag names.capture (boolSlot m p.i p.hi) (boolSlot m p.a p.ha))
      (.drop .refl) := by
  intro G F fuel nps ph source target R aligned boolReflect falseValue
  have leaf := Solidity.Lowering.G19.AssignmentWhileReset.correct G F fuel nps ph
    (returns := returns) (M := M) (l := l) (u := u) source target m (R target.H) aligned
    (boolReflect target.H) (falseValue target.H) p.i p.a p.hi p.ha p.mapI p.mapA
  dsimp only at leaf
  obtain ⟨sourceRun, -, related, -⟩ := leaf
  have below := Horizon.while_below (lp := l) (R := returns) (M := M) (u := u) G F nps ph _ _ _ _
    (Horizon.assign_below G F p.i p.a)
    (Horizon.expr_below G F nps ph _ _ (Horizon.assign_lit_below G F p.a false (.inl rfl)))
    (fuel + 4) source.1
  have sourceRun' := (Source.Below.eq_of_done below (.nil, source.2)
    (by rw [sourceRun]; intro h; cases h)).trans sourceRun
  cases hv : (TEnv.get (boolSlot m p.a p.ha) target.env : Bool) with
  | false =>
    refine ⟨_, _, sourceRun', prog_false _ _ _ _ target hv, ?_, rfl⟩
    intro τ k
    have r := related k
    revert r
    unfold Solidity.Lowering.G19.AssignmentWhileReset.targetAfter
    dsimp only
    rw [hv]
    exact id
  | true =>
    refine ⟨_, _, sourceRun', prog_true _ _ _ _ target hv, ?_, rfl⟩
    intro τ k
    have r := related k
    revert r
    unfold Solidity.Lowering.G19.AssignmentWhileReset.targetAfter
    dsimp only
    rw [hv]
    exact id

end WhileReset

end Solidity.Correctness.Lowering.Loops
