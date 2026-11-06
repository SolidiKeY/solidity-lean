import Solidity.Backend.PrimitivePackets.Comparisons.Agreement

/-! Runtime bare require over a Boolean local. Selection is through the public
checked memory statement compiler. The physical relation is the full StateRepr;
no target run is assumed. This instruction machine exposes bare revert only,
so this family deliberately excludes assert and message-bearing require. -/
namespace Solidity.Backend.FailurePaths.RuntimeGuard
open Evm Evm.Memory

def statement {E : Source.Env} {Γ : Source.RCtx} (i : Source.Idx Γ .bool) :
    Source.RStmt E [] false .body Γ Γ :=
  .expr (.builtin .require (.cons (.local i) .nil) rfl)

def target {C : Contract} {Γ : Ctx} (i : Idx Γ (.val .bool)) : Stmt C Γ Γ :=
  .require (.simple (.local i))

def selected {C : Contract} {Γ : Ctx} (b : Nat) (F : Frag Γ)
    (i : Idx Γ (.val .bool)) : CompiledStmt b F (target (C:=C) i) :=
  ⟨F,_,.require F _ _ (.core _ rfl)⟩

theorem public_selection {C : Contract} {Γ : Ctx} (b : Nat) (F : Frag Γ)
    (i : Idx Γ (.val .bool)) :
    compileStmt b F (target (C:=C) i) = some (selected b F i) := rfl

theorem exact_code {C : Contract} {Γ : Ctx} (b : Nat) (F : Frag Γ)
    (i : Idx Γ (.val .bool)) :
    (selected (C:=C) b F i).code = [.mload (cellOf b i)] ++ assertTop := rfl

theorem selected_run {C : Contract} {Γ : Ctx} (state : State C Γ)
    (i : Idx Γ (.val .bool)) (value : Bool)
    (read : TEnv.get i state.env = value)
    {L b frame : Nat} {F : Frag Γ} {addresses : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state addresses machine) :
    run (selected (C:=C) b F i).code machine =
      if value then .ok machine 0 else .revert := by
  have simulation := (ValFrag.core (b:=b) (F:=F)
    (e:=Val.simple (C:=C) (.local i)) rfl).correct represented
  have evaluated : (Val.simple (C:=C) (.local i)).evalT state = .ok value := by
    simp only [Val.evalT,Simple.evalT,read]
  rw [evaluated] at simulation
  rcases simulation with ⟨v,w,same,word,executed⟩ | ⟨impossible,_⟩
  · cases same
    have codeRun := word ▸ executed
    change run (compileVal b (.simple (.local i)) ++ assertTop) machine = _
    rw [run_append_skip codeRun]
    cases value <;> rfl
  · cases impossible

theorem source_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (i : Source.Idx Γ .bool) (value : Bool) (locals : Source.Locals E.layout Γ)
    (state : Source.St E) (read : locals.get i = .bool value) :
    (Source.execS G F (n+7) 0 none (statement i) locals).run (Source.L0 E,state) =
      if value then (.ok (.normal locals),(Source.L0 E,state))
      else (.error (.revert []),(Source.L0 E,state)) := by
  have argsRun : (Source.evalArgs G F (n+4)
      (.cons (.local i) .nil : Source.RArgs E Γ [.bool])).run (locals,state) =
      (.ok (.cons (.val (.bool value)) .nil),(locals,state)) := by
    change (Except.ok (Source.RVals.cons (.val (locals.get i)) .nil),(locals,state)) = _
    rw [read]
  have exprRun : (Source.evalE G F (n+6)
      (.builtin .require (.cons (.local i) .nil) rfl : Source.RExpr E Γ (.tuple []))).run
      (locals,state) = if value then (.ok Source.RVal.unit,(locals,state))
      else (.error (.revert []),(locals,state)) := by
    rw [Source.evalE,Source.evalBuiltin]
    simp only [reduceCtorEq,decide_false,Bool.false_or,Bool.false_and,
      Bool.false_eq_true,if_false]
    rw [Source.Hoare.run_bind,argsRun]
    cases value <;> rfl
  simp only [statement,Source.execS]
  rw [Source.Hoare.run_bind]
  simp only [ExceptT.run] at exprRun
  simp only [Source.EM.sub,ExceptT.run,ExceptT.mk,exprRun]
  cases value <;> rfl

theorem agreement {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (si : Source.Idx srcΓ .bool) (i : Idx Γ (.val .bool)) (value : Bool)
    (locals : Source.Locals E.layout srcΓ) (source : Source.St E) (state : State C Γ)
    (sourceRead : locals.get si = .bool value) (targetRead : TEnv.get i state.env = value)
    {L b frame : Nat} {fragment : Frag Γ} {addresses : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame fragment state addresses machine) :
    (Source.execS G F (n+7) 0 none (statement si) locals).run (Source.L0 E,source) =
      (if value then (.ok (.normal locals),(Source.L0 E,source))
       else (.error (.revert []),(Source.L0 E,source))) ∧
    compileStmt b fragment (target (C:=C) i) = some (selected b fragment i) ∧
    run (selected (C:=C) b fragment i).code machine =
      (if value then .ok machine 0 else .revert) :=
  ⟨source_run G F n si value locals source sourceRead,
    public_selection b fragment i,selected_run state i value targetRead represented⟩

theorem source_zero {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (i : Source.Idx Γ .bool)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.execS G F 0 0 none (statement i) locals).run (Source.L0 E,state) =
      (.error .timeout,(Source.L0 E,state)) := rfl

#print axioms agreement
#print axioms source_zero
#print axioms source_run
#print axioms public_selection
#print axioms exact_code
#print axioms selected_run
end Solidity.Backend.FailurePaths.RuntimeGuard
