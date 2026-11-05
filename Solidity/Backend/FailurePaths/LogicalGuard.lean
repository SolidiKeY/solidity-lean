import Solidity.Evm.MemoryCompile
import Solidity.Source.Hoare
import Solidity.Source.Eval

/-! Bare require over two Boolean locals, using the existing short-circuit
Source evaluator and public checked memory statement compiler. Initial operand
reads and the full StateRepr are explicit. This does not supply automatic
frontend lowering, a revert payload/post-machine or bytecode adequacy. -/
namespace Solidity.Backend.FailurePaths.LogicalGuard
open Evm Evm.Memory

def sourceOp (disjunction : Bool) : Source.BinOp := if disjunction then .or else .and
def targetOp (disjunction : Bool) : BinOp := if disjunction then .or else .and
def result (disjunction x y : Bool) : Bool := if disjunction then x || y else x && y

def expression {E : Source.Env} {Γ : Source.RCtx} (disjunction : Bool)
    (a b : Source.Idx Γ .bool) : Source.RExpr E Γ .bool :=
  .binary (sourceOp disjunction) (.local a) (.local b)
def statement {E : Source.Env} {Γ : Source.RCtx} (disjunction : Bool)
    (a b : Source.Idx Γ .bool) : Source.RStmt E [] false .body Γ Γ :=
  .expr (.builtin .require (.cons (expression disjunction a b) .nil) rfl)

def value {C : Contract} {Γ : Ctx} (disjunction : Bool)
    (a b : Idx Γ (.val .bool)) : Val C Γ .bool :=
  .binop (targetOp disjunction) (by cases disjunction <;> rfl)
    (by cases disjunction <;> rfl) (.simple (.local a)) (.simple (.local b))
def target {C : Contract} {Γ : Ctx} (disjunction : Bool)
    (a b : Idx Γ (.val .bool)) : Stmt C Γ Γ := .require (value disjunction a b)

def condition {C : Contract} {Γ : Ctx} (base : Nat) (F : Frag Γ)
    (disjunction : Bool) (a b : Idx Γ (.val .bool)) : CompiledVal base F (value (C:=C) disjunction a b) := by
  cases disjunction <;> exact ⟨_,.binary _ rfl rfl _ _ _ _ (.core _ rfl) (.core _ rfl)⟩
def selected {C : Contract} {Γ : Ctx} (base : Nat) (F : Frag Γ)
    (disjunction : Bool) (a b : Idx Γ (.val .bool)) : CompiledStmt base F (target (C:=C) disjunction a b) :=
  ⟨F,_,.require F _ _ (condition base F disjunction a b).cert⟩

theorem public_selection {C : Contract} {Γ : Ctx} (base : Nat) (F : Frag Γ)
    (disjunction : Bool) (a b : Idx Γ (.val .bool)) :
    compileStmt base F (target (C:=C) disjunction a b) = some (selected base F disjunction a b) := by
  cases disjunction <;> rfl

theorem exact_code {C : Contract} {Γ : Ctx} (base : Nat) (F : Frag Γ)
    (disjunction : Bool) (a b : Idx Γ (.val .bool)) :
    (selected (C:=C) base F disjunction a b).code =
      binaryCode .bool (targetOp disjunction) [.mload (cellOf base a)] [.mload (cellOf base b)] ++ assertTop := by
  cases disjunction <;> rfl

theorem intrinsic_run {C : Contract} {Γ : Ctx} (state : State C Γ)
    (disjunction : Bool) (a b : Idx Γ (.val .bool)) (x y : Bool)
    (left : TEnv.get a state.env = x) (right : TEnv.get b state.env = y) :
    (value disjunction a b).evalT state = .ok (result disjunction x y) := by
  cases disjunction <;> cases x <;> cases y <;>
    simp only [value,targetOp,result,Val.evalT,Simple.evalT,left,right,
      BinOp.shortT,BinOp.evalT,bind,Except.bind] <;> rfl

theorem selected_run {C : Contract} {Γ : Ctx} (state : State C Γ)
    (disjunction : Bool) (a b : Idx Γ (.val .bool)) (x y : Bool)
    (left : TEnv.get a state.env = x) (right : TEnv.get b state.env = y)
    {L base frame : Nat} {F : Frag Γ} {addresses : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L base frame F state addresses machine) :
    run (selected (C:=C) base F disjunction a b).code machine =
      if result disjunction x y then .ok machine 0 else .revert := by
  have simulation := (condition (C:=C) base F disjunction a b).cert.correct represented
  rw [intrinsic_run state disjunction a b x y left right] at simulation
  rcases simulation with ⟨v,w,same,word,executed⟩ | ⟨impossible,_⟩
  · cases same
    have codeRun := word ▸ executed
    change run ((condition base F disjunction a b).code ++ assertTop) machine = _
    rw [run_append_skip codeRun]
    cases result disjunction x y <;> rfl
  · cases impossible

theorem source_expression {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (locals : Source.Locals E.layout Γ)
    (state : Source.St E) (disjunction : Bool) (a b : Source.Idx Γ .bool) (x y : Bool)
    (left : locals.get a = .bool x) (right : locals.get b = .bool y) :
    (Source.evalE G F (n+3) (expression disjunction a b)).run (locals,state) =
      (.ok (.val (.bool (result disjunction x y))),(locals,state)) := by
  have localRun (i : Source.Idx Γ .bool) (v : Bool) (read : locals.get i = .bool v) :
      (Source.evalE G F (n+2) (.local i)).run (locals,state) =
        (.ok (.val (.bool v)),(locals,state)) := by
    change (Except.ok (Source.RVal.val (locals.get i)),(locals,state)) = _
    rw [read]
  have plainRun (v : Bool) :
      (Source.getV (.val (.bool v)) : Source.EM E Γ _).run (locals,state) =
        (.ok (.bool v),(locals,state)) := rfl
  rw [expression,Source.evalE]
  cases disjunction <;> cases x <;> cases y <;>
    simp only [sourceOp,result,reduceCtorEq,decide_true,decide_false,
      Bool.true_or,Bool.false_or,Bool.true_and,Bool.false_and,
      Bool.false_eq_true,Int.reduceEq,
      if_true,if_false,Source.Hoare.run_bind,plainRun,Source.Val.key,
      localRun a _ left,localRun b _ right] <;> rfl

theorem source_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (locals : Source.Locals E.layout Γ)
    (state : Source.St E) (disjunction : Bool) (a b : Source.Idx Γ .bool) (x y : Bool)
    (left : locals.get a = .bool x) (right : locals.get b = .bool y) :
    (Source.execS G F (n+7) 0 none (statement disjunction a b) locals).run (Source.L0 E,state) =
      if result disjunction x y then (.ok (.normal locals),(Source.L0 E,state))
      else (.error (.revert []),(Source.L0 E,state)) := by
  have argsRun : (Source.evalArgs G F (n+4) (.cons (expression disjunction a b) .nil)).run
      (locals,state) = (.ok (.cons (.val (.bool (result disjunction x y))) .nil),(locals,state)) := by
    rw [Source.evalArgs,Source.Hoare.run_bind,source_expression G F n locals state disjunction a b x y left right]
    rfl
  have exprRun : (Source.evalE G F (n+6)
      (.builtin .require (.cons (expression disjunction a b) .nil) rfl :
        Source.RExpr E Γ (.tuple []))).run (locals,state) =
      if result disjunction x y then (.ok Source.RVal.unit,(locals,state))
      else (.error (.revert []),(locals,state)) := by
    rw [Source.evalE,Source.evalBuiltin]
    simp only [reduceCtorEq,decide_false,Bool.false_or,Bool.false_and,Bool.false_eq_true,if_false]
    rw [Source.Hoare.run_bind,argsRun]
    cases result disjunction x y <;> rfl
  simp only [statement,Source.execS]
  rw [Source.Hoare.run_bind]
  simp only [ExceptT.run] at exprRun
  simp only [Source.EM.sub,ExceptT.run,ExceptT.mk,exprRun]
  cases result disjunction x y <;> rfl

theorem agreement {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (locals : Source.Locals E.layout srcΓ)
    (source : Source.St E) (state : State C Γ) (disjunction : Bool)
    (sa sb : Source.Idx srcΓ .bool) (a b : Idx Γ (.val .bool)) (x y : Bool)
    (sourceLeft : locals.get sa = .bool x) (sourceRight : locals.get sb = .bool y)
    (targetLeft : TEnv.get a state.env = x) (targetRight : TEnv.get b state.env = y)
    {L base frame : Nat} {fragment : Frag Γ} {addresses : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L base frame fragment state addresses machine) :
    (Source.execS G F (n+7) 0 none (statement disjunction sa sb) locals).run (Source.L0 E,source) =
      (if result disjunction x y then (.ok (.normal locals),(Source.L0 E,source))
       else (.error (.revert []),(Source.L0 E,source))) ∧
    compileStmt base fragment (target (C:=C) disjunction a b) = some (selected base fragment disjunction a b) ∧
    run (selected (C:=C) base fragment disjunction a b).code machine =
      (if result disjunction x y then .ok machine 0 else .revert) :=
  ⟨source_run G F n locals source disjunction sa sb x y sourceLeft sourceRight,
    public_selection base fragment disjunction a b,
    selected_run state disjunction a b x y targetLeft targetRight represented⟩

/-- info: 'Solidity.Backend.FailurePaths.LogicalGuard.public_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms public_selection
/-- info: 'Solidity.Backend.FailurePaths.LogicalGuard.exact_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exact_code
/-- info: 'Solidity.Backend.FailurePaths.LogicalGuard.intrinsic_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intrinsic_run
/-- info: 'Solidity.Backend.FailurePaths.LogicalGuard.selected_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms selected_run
/-- info: 'Solidity.Backend.FailurePaths.LogicalGuard.source_expression' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_expression
/-- info: 'Solidity.Backend.FailurePaths.LogicalGuard.source_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_run
/-- info: 'Solidity.Backend.FailurePaths.LogicalGuard.agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms agreement
end Solidity.Backend.FailurePaths.LogicalGuard
