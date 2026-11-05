import Solidity.Backend.PrimitivePackets.Comparisons.Agreement

/-! Bare require over signed/unsigned full-width local relational comparisons.
The comparison selector and operand simulation are the published primitive
packet. This module proves actual Source statement execution and public memory
statement selection, retaining the full initial StateRepr and saved machine.
It supplies no automatic Source lowering, payload encoder or bytecode relation. -/
namespace Solidity.Backend.FailurePaths.RelationalGuard
open Evm Evm.Memory Lowering.V07 PrimitivePackets.Comparisons

def statement {E : Source.Env} {Γ : Source.RCtx} (o : Order) (signed : Bool)
    (a b : Source.Idx Γ (.int (ty signed))) : Source.RStmt E [] false .body Γ Γ :=
  .expr (.builtin .require (.cons (expression o signed a b) .nil) rfl)

def target {C : Contract} {Γ : Ctx} (o : Order) (signed : Bool)
    (a b : Idx Γ (.val (prim signed))) : Stmt C Γ Γ :=
  .require (value o signed a b)

def selected {C : Contract} {Γ : Ctx} (base : Nat) (F : Frag Γ) (o : Order) (signed : Bool)
    (a b : Idx Γ (.val (prim signed))) : CompiledStmt base F (target (C:=C) o signed a b) :=
  let condition := PrimitivePackets.Comparisons.selected (C:=C) base F o signed a b
  ⟨F,_,.require F _ _ condition.cert⟩

theorem public_selection {C : Contract} {Γ : Ctx} (base : Nat) (F : Frag Γ)
    (o : Order) (signed : Bool) (a b : Idx Γ (.val (prim signed))) :
    compileStmt base F (target (C:=C) o signed a b) = some (selected base F o signed a b) := by
  cases o <;> cases signed <;> rfl

theorem exact_code {C : Contract} {Γ : Ctx} (base : Nat) (F : Frag Γ)
    (o : Order) (signed : Bool) (a b : Idx Γ (.val (prim signed))) :
    (selected (C:=C) base F o signed a b).code =
      (PrimitivePackets.Comparisons.selected (C:=C) base F o signed a b).code ++ assertTop := rfl

theorem selected_run {C : Contract} {Γ : Ctx} (state : State C Γ)
    (o : Order) (signed : Bool) (a b : Idx Γ (.val (prim signed)))
    (x y : Int) (hx : (ty signed).lo ≤ x ∧ x ≤ (ty signed).hi)
    (hy : (ty signed).lo ≤ y ∧ y ≤ (ty signed).hi)
    (left : TEnv.get a state.env = integerValue (ty signed) x hx)
    (right : TEnv.get b state.env = integerValue (ty signed) y hy)
    {L base frame : Nat} {F : Frag Γ} {addresses : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L base frame F state addresses machine) :
    run (selected (C:=C) base F o signed a b).code machine =
      if result o x y then .ok machine 0 else .revert := by
  rw [exact_code,run_append_skip
    (PrimitivePackets.Comparisons.selected_run state o signed a b x y hx hy left right represented)]
  cases result o x y <;> rfl

theorem source_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (locals : Source.Locals E.layout Γ)
    (state : Source.St E) (o : Order) (signed : Bool)
    (a b : Source.Idx Γ (.int (ty signed))) (x y : Int)
    (hx : (ty signed).lo ≤ x ∧ x ≤ (ty signed).hi)
    (hy : (ty signed).lo ≤ y ∧ y ≤ (ty signed).hi)
    (left : locals.get a = .int x hx) (right : locals.get b = .int y hy) :
    (Source.execS G F (n+7) 0 none (statement o signed a b) locals).run (Source.L0 E,state) =
      if result o x y then (.ok (.normal locals),(Source.L0 E,state))
      else (.error (.revert []),(Source.L0 E,state)) := by
  have comparison := PrimitivePackets.Comparisons.source_run G F n (locals,state)
    o signed a b x y hx hy left right
  have argsRun : (Source.evalArgs G F (n+4)
      (.cons (expression o signed a b) .nil)).run (locals,state) =
      (.ok (.cons (.val (.bool (result o x y))) .nil),(locals,state)) := by
    rw [Source.evalArgs,Source.Hoare.run_bind,comparison]
    rfl
  have exprRun : (Source.evalE G F (n+6)
      (.builtin .require (.cons (expression o signed a b) .nil) rfl :
        Source.RExpr E Γ (.tuple []))).run (locals,state) =
      if result o x y then (.ok Source.RVal.unit,(locals,state))
      else (.error (.revert []),(locals,state)) := by
    rw [Source.evalE,Source.evalBuiltin]
    simp only [reduceCtorEq,decide_false,Bool.false_or,Bool.false_and,
      Bool.false_eq_true,if_false]
    rw [Source.Hoare.run_bind,argsRun]
    cases result o x y <;> rfl
  simp only [statement,Source.execS]
  rw [Source.Hoare.run_bind]
  simp only [ExceptT.run] at exprRun
  simp only [Source.EM.sub,ExceptT.run,ExceptT.mk,exprRun]
  cases result o x y <;> rfl

theorem agreement {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (locals : Source.Locals E.layout srcΓ)
    (source : Source.St E) (state : State C Γ) (o : Order) (signed : Bool)
    (sa sb : Source.Idx srcΓ (.int (ty signed))) (a b : Idx Γ (.val (prim signed)))
    (x y : Int) (hx : (ty signed).lo ≤ x ∧ x ≤ (ty signed).hi)
    (hy : (ty signed).lo ≤ y ∧ y ≤ (ty signed).hi)
    (sourceLeft : locals.get sa = .int x hx) (sourceRight : locals.get sb = .int y hy)
    (targetLeft : TEnv.get a state.env = integerValue (ty signed) x hx)
    (targetRight : TEnv.get b state.env = integerValue (ty signed) y hy)
    {L base frame : Nat} {fragment : Frag Γ} {addresses : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L base frame fragment state addresses machine) :
    (Source.execS G F (n+7) 0 none (statement o signed sa sb) locals).run (Source.L0 E,source) =
      (if result o x y then (.ok (.normal locals),(Source.L0 E,source))
       else (.error (.revert []),(Source.L0 E,source))) ∧
    compileStmt base fragment (target (C:=C) o signed a b) = some (selected base fragment o signed a b) ∧
    run (selected (C:=C) base fragment o signed a b).code machine =
      (if result o x y then .ok machine 0 else .revert) :=
  ⟨source_run G F n locals source o signed sa sb x y hx hy sourceLeft sourceRight,
    public_selection base fragment o signed a b,
    selected_run state o signed a b x y hx hy targetLeft targetRight represented⟩

#print axioms public_selection
#print axioms exact_code
#print axioms selected_run
#print axioms source_run
#print axioms agreement
end Solidity.Backend.FailurePaths.RelationalGuard
