import Solidity.Correctness.Lowering.Loops.ReturnFamily
import Solidity.Correctness.Lowering.Loops.Horizon
import Solidity.Lowering.G19.WhileReturn
import Solidity.Lowering.G19.AssignmentDoWhileReturn

/-!
# Loop lowering leaves with `return` (function level, H497)

Each leaf proves `RetEndpoint` for its `ReturnFamily` member: the target run is
computed generically (slots, names, states, an arbitrary never-run `do`
condition), and the Source half is the matching G19 `correct`
(`G19/WhileReturn.lean:43`, `G19/AssignmentDoWhileReturn.lean:94`,
`G19/AssignmentReturnFlag.lean:69`) moved across the identity conversion by
`Horizon`. The target witness equals the Source "returned" observation.
-/
namespace Solidity.Correctness.Lowering.Loops

open Solidity.Lowering.V07
open Solidity.Lowering.G19.AssignmentReturnFlag (boolSlot)

namespace Returns

/-! ### `while (i = a) return;` -/

theorem tail_run {C : Contract} {Γ : Ctx} (j : Idx Γ (.val .bool)) (σ : State C Γ) (v : Bool) :
    (whileReturnTail j).run (((σ.push (t := .val .bool) false).push (t := .val .bool) false).push
      (t := .val .bool) v) =
      .ok ⟨((((σ.setLocal j v).push (t := .val .bool) (!v)).push (t := .val .bool) v).push
        (t := .val .bool) v), List.prefix_refl _⟩ := by
  cases v <;> rfl

theorem body_prefix {C : Contract} {Γ : Ctx} (se : Var) (j b : Idx Γ (.val .bool)) (σ : State C Γ) :
    (Prog.cons (.declLocal .bool se (some (.simple (.local b.there.there)))) (whileReturnTail j) :
      Prog C (.val .bool :: .val .bool :: Γ) _).run ((σ.push (t := .val .bool) false).push
        (t := .val .bool) false) =
      (whileReturnTail j).run (((σ.push (t := .val .bool) false).push (t := .val .bool) false).push
        (t := .val .bool) (TEnv.get b σ.env)) := by
  have decl : (Stmt.declLocal .bool se (some (.simple (.local b.there.there))) :
      Stmt C (.val .bool :: .val .bool :: Γ) _).run ((σ.push (t := .val .bool) false).push
        (t := .val .bool) false) =
      .ok ⟨((σ.push (t := .val .bool) false).push (t := .val .bool) false).push
        (t := .val .bool) (TEnv.get b σ.env), List.prefix_refl _⟩ := rfl
  rw [Prog.run_cons_ok decl]
  cases (whileReturnTail j).run (((σ.push (t := .val .bool) false).push (t := .val .bool) false).push
    (t := .val .bool) (TEnv.get b σ.env)) <;> rfl

/-- The loop of the lowered `while (i = a) return;`: one iteration sets `ret`
(true right-hand side) or `brk` (false). -/
theorem whileReturn_loop {C : Contract} {Γ : Ctx} (names : RetFresh) (j b : Idx Γ (.val .bool))
    (σ : State C Γ) (v : Bool) (hv : TEnv.get b σ.env = v) :
    (Stmt.loop .auto brkRetGuard
      (.cons (.declLocal .bool names.third (some (.simple (.local b.there.there))))
        (whileReturnTail j)) : Stmt C (.val .bool :: .val .bool :: Γ) _).run
        ((σ.push (t := .val .bool) false).push (t := .val .bool) false) =
      .ok ⟨((σ.setLocal j v).push (t := .val .bool) (!v)).push (t := .val .bool) v,
        List.prefix_refl _⟩ := by
  have enter : (brkRetGuard : Val C (.val .bool :: .val .bool :: Γ) .bool).evalT
      ((σ.push (t := .val .bool) false).push (t := .val .bool) false) = .ok true := rfl
  rw [Stmt.run_loop]
  apply TLoop.run_of_iterN (n := 2)
  simp only [TLoop.iterN, TLoop.step]
  rw [enter, body_prefix, hv, tail_run]
  cases v <;> rfl

theorem whileReturn_run {C : Contract} {Γ : Ctx} (names : RetFresh) (j b : Idx Γ (.val .bool))
    (σ : State C Γ) (v : Bool) (hv : TEnv.get b σ.env = v) :
    (whileReturnProg names j b).run σ =
      .ok ⟨((σ.setLocal j v).push (t := .val .bool) (!v)).push (t := .val .bool) v,
        List.prefix_refl _⟩ := by
  have d1 : (Stmt.declLocal .bool names.first (some (.simple (.bool false))) : Stmt C Γ _).run σ =
      .ok ⟨σ.push (t := .val .bool) false, List.prefix_refl _⟩ := rfl
  have d2 : (Stmt.declLocal .bool names.second (some (.simple (.bool false))) :
      Stmt C (.val .bool :: Γ) _).run (σ.push (t := .val .bool) false) =
      .ok ⟨(σ.push (t := .val .bool) false).push (t := .val .bool) false, List.prefix_refl _⟩ := rfl
  rw [whileReturnProg, Prog.run_cons_ok d1, Prog.run_cons_ok d2,
    Prog.run_cons_ok (whileReturn_loop names j b σ v hv)]
  cases v <;> rfl

/-- The converted Source loop runs as G19's bare `while (i = a) return;`. -/
theorem whileReturn_source_run {E : Source.Env} {srcΓ : Source.RCtx} {M l u : Bool} {C : Contract}
    {Γ : Ctx} (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    (m : ContextMap srcΓ Γ) (p : Pair m) (source : Source.EMState E srcΓ) (target : State C Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool), R .bool (.val .bool) v b → v = .bool b) :
    (Source.execS G F (fuel + 4) nps ph (R := []) (M := M)
      (.whileLoop (l := l) (u := u) (.assign (.local p.i) (.conv (.local p.a) (.inl rfl))) (.ret rfl))
        source.1).run (.nil, source.2) =
      (.ok (if (TEnv.get (boolSlot m p.a p.ha) target.env : Bool) = true then
        Source.Out.ret (source.1.set p.i (.bool (TEnv.get (boolSlot m p.a p.ha) target.env)))
        else Source.Out.normal (source.1.set p.i (.bool (TEnv.get (boolSlot m p.a p.ha) target.env)))),
        (.nil, source.2)) ∧
    (m.wk (Thin.drop (t := .val .bool) .refl)).Related R
      (source.1.set p.i (.bool (TEnv.get (boolSlot m p.a p.ha) target.env)))
      (Solidity.Lowering.G19.AssignmentReturnFlag.reached m p.i p.a p.hi p.ha target).env := by
  have leaf := Solidity.Lowering.G19.WhileReturn.correct G F fuel nps ph (M := M) (l := l) (u := u)
    source target m R aligned boolReflect p.i p.a p.hi p.ha p.mapI p.mapA
  obtain ⟨sourceRun, -, related, -, -⟩ := leaf
  have below := Horizon.while_below (lp := l) (R := []) (M := M) (u := u) G F nps ph _ _ _ _
    (Horizon.assign_below G F p.i p.a) (Horizon.same_below G F nps ph (.ret rfl)) (fuel + 3) source.1
  exact ⟨(Source.Below.eq_of_done below (.nil, source.2)
    (by rw [sourceRun]; intro h; cases h)).trans sourceRun, related⟩

/-! ### `do { i = a; return; } while (c);` -/

theorem doReturn_run {C : Contract} {Γ : Ctx} (names : RetFresh) (j b : Idx Γ (.val .bool))
    (c : Val C (.val .bool :: .val .bool :: Γ) .bool) (σ : State C Γ) :
    (doReturnProg names j b c).run σ =
      .ok ⟨((σ.setLocal j (TEnv.get b σ.env)).push (t := .val .bool) false).push
        (t := .val .bool) true, List.prefix_refl _⟩ := by
  have d1 : (Stmt.declLocal .bool names.first (some (.simple (.bool true))) : Stmt C Γ _).run σ =
      .ok ⟨σ.push (t := .val .bool) true, List.prefix_refl _⟩ := rfl
  have d2 : (Stmt.declLocal .bool names.second (some (.simple (.bool false))) :
      Stmt C (.val .bool :: Γ) _).run (σ.push (t := .val .bool) true) =
      .ok ⟨(σ.push (t := .val .bool) true).push (t := .val .bool) false, List.prefix_refl _⟩ := rfl
  have loop : (Stmt.loop .auto (.binop .and rfl rfl (notB (.simple (.local .here)))
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
  rw [doReturnProg, Prog.run_cons_ok d1, Prog.run_cons_ok d2, Prog.run_cons_ok loop]
  rfl

/-! ### `if (i = a) return;` -/

theorem returnFlag_run {C : Contract} {Γ : Ctx} (names : RetFresh) (j b : Idx Γ (.val .bool))
    (σ : State C Γ) (v : Bool) (hv : TEnv.get b σ.env = v) :
    (returnFlagProg names j b).run σ =
      .ok ⟨(σ.setLocal j v).push (t := .val .bool) v, List.prefix_refl _⟩ := by
  have d : (Stmt.declLocal .bool names.first (some (.simple (.local b))) : Stmt C Γ _).run σ =
      .ok ⟨σ.push (t := .val .bool) (TEnv.get b σ.env), List.prefix_refl _⟩ := rfl
  rw [returnFlagProg, Prog.run_cons_ok d, hv]
  cases v <;> rfl

/-! ### Leaf endpoints -/

theorem whileReturn_endpoint {E : Source.Env} {srcΓ : Source.RCtx} {M l u : Bool} {C : Contract}
    {Γ : Ctx} (m : ContextMap srcΓ Γ) (p : Pair m) (x : RetShape.whileReturn.Extra E srcΓ C Γ)
    (names : RetFresh) :
    RetEndpoint (RetShape.whileReturn.source (M := M) (l := l) (u := u) p x)
      RetShape.whileReturn.offset m (RetShape.whileReturn.program p x names)
      (RetShape.whileReturn.embedding Γ) (RetShape.whileReturn.witness Γ) := by
  intro G F fuel nps ph source target R aligned boolReflect _
  obtain ⟨sourceRun, related⟩ := whileReturn_source_run (M := M) (l := l) (u := u) G F fuel nps ph
    m p source target (R target.H) aligned (boolReflect target.H)
  refine ⟨_, TEnv.get (boolSlot m p.a p.ha) target.env, _, sourceRun,
    whileReturn_run names _ _ target _ rfl, rfl, ?_, rfl⟩
  intro τ k
  exact related k

theorem doReturn_endpoint {E : Source.Env} {srcΓ : Source.RCtx} {M l u : Bool} {C : Contract}
    {Γ : Ctx} (m : ContextMap srcΓ Γ) (p : Pair m) (x : RetShape.doReturn.Extra E srcΓ C Γ)
    (names : RetFresh) :
    RetEndpoint (RetShape.doReturn.source (M := M) (l := l) (u := u) p x)
      RetShape.doReturn.offset m (RetShape.doReturn.program p x names)
      (RetShape.doReturn.embedding Γ) (RetShape.doReturn.witness Γ) := by
  intro G F fuel nps ph source target R aligned boolReflect _
  have leaf := Solidity.Lowering.G19.AssignmentDoWhileReturn.correct G F fuel nps ph
    (M := M) (l := l) (u := u) source target m (R target.H) aligned (boolReflect target.H)
    p.i p.a p.hi p.ha p.mapI p.mapA x.1
  obtain ⟨sourceRun, -, related, -, -⟩ := leaf
  unfold Solidity.Lowering.G19.AssignmentDoWhileReturn.body at sourceRun
  have below := Horizon.doWhile_below (lp := l) (R := []) (M := M) (u := u) G F nps ph x.1 _ _
    (Horizon.block_below G F nps ph _ _
      (Horizon.items_below G F nps ph _ _ (.stmt (.ret rfl) .nil)
        (Horizon.expr_below G F nps ph _ _ (Horizon.assign_below G F p.i p.a))))
    (fuel + 6) source.1
  have sourceRun' := (Source.Below.eq_of_done below (.nil, source.2)
    (by rw [sourceRun]; intro h; cases h)).trans sourceRun
  refine ⟨_, true, _, sourceRun', doReturn_run names _ _ x.2 target, rfl, ?_, rfl⟩
  intro τ k
  exact related k

theorem returnFlag_endpoint {E : Source.Env} {srcΓ : Source.RCtx} {M l u : Bool} {C : Contract}
    {Γ : Ctx} (m : ContextMap srcΓ Γ) (p : Pair m) (x : RetShape.returnFlag.Extra E srcΓ C Γ)
    (names : RetFresh) :
    RetEndpoint (RetShape.returnFlag.source (M := M) (l := l) (u := u) p x)
      RetShape.returnFlag.offset m (RetShape.returnFlag.program p x names)
      (RetShape.returnFlag.embedding Γ) (RetShape.returnFlag.witness Γ) := by
  intro G F fuel nps ph source target R aligned boolReflect _
  have leaf := Solidity.Lowering.G19.AssignmentReturnFlag.correct G F fuel nps ph
    (M := M) (k := ⟨l, u⟩) source target m (R target.H) aligned (boolReflect target.H)
    p.i p.a p.hi p.ha p.mapI p.mapA
  obtain ⟨sourceRun, -, related, -, -⟩ := leaf
  have below := Horizon.ifThen_below (R := []) (M := M) (k := ⟨l, u⟩) G F nps ph _ _ (.ret rfl)
    (Horizon.assign_below G F p.i p.a) (fuel + 3) source.1
  have sourceRun' := (Source.Below.eq_of_done below (.nil, source.2)
    (by rw [sourceRun]; intro h; cases h)).trans sourceRun
  refine ⟨_, TEnv.get (boolSlot m p.a p.ha) target.env, _, sourceRun',
    returnFlag_run names _ _ target _ rfl, rfl, ?_, rfl⟩
  intro τ k
  exact related k

end Returns

end Solidity.Correctness.Lowering.Loops
