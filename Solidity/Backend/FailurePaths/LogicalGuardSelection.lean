import Solidity.Backend.FailurePaths.LocalGuardSelection
import Solidity.Backend.FailurePaths.LogicalGuard

/-! Executable indexed-Source selection for bare require of Boolean-local
conjunction/disjunction. Views retain actual source syntax/type/context evidence;
the existing local recognizer and public checked memory compiler are reused.
Context-map construction and whole-program/bytecode adequacy remain separate. -/
namespace Solidity.Backend.FailurePaths.LogicalGuardSelection
open Evm Evm.Memory

structure ExpressionView {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (expr : Source.RExpr E Γ τ) where
  type : τ = .bool
  disjunction : Bool
  left : Source.Idx Γ .bool
  right : Source.Idx Γ .bool
  same : type ▸ expr = LogicalGuard.expression disjunction left right

def expressionView {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy} :
    (expr : Source.RExpr E Γ τ) → Option (ExpressionView expr)
  | .binary op left right =>
      match LocalGuardSelection.boolLocal left, LocalGuardSelection.boolLocal right with
      | some lhs, some rhs =>
          match op with
          | .and => some ⟨lhs.type,false,lhs.index,rhs.index,by
              cases lhs with
              | mk type i same =>
                cases type; cases same
                cases rhs with
                | mk type j same => cases type; cases same; rfl⟩
          | .or => some ⟨lhs.type,true,lhs.index,rhs.index,by
              cases lhs with
              | mk type i same =>
                cases type; cases same
                cases rhs with
                | mk type j same => cases type; cases same; rfl⟩
          | _ => none
      | _, _ => none
  | _ => none

structure View {E : Source.Env} {Γ Ξ : Source.RCtx}
    (stmt : Source.RStmt E [] false .body Γ Ξ) where
  disjunction : Bool
  left : Source.Idx Γ .bool
  right : Source.Idx Γ .bool
  contexts : Ξ = Γ
  same : HEq stmt (LogicalGuard.statement (E:=E) disjunction left right)

def view {E : Source.Env} {Γ Ξ : Source.RCtx} :
    (stmt : Source.RStmt E [] false .body Γ Ξ) → Option (View stmt)
  | .expr (.builtin .require (.cons head .nil) typed) =>
      match expressionView head with
      | none => none
      | some witness => some ⟨witness.disjunction,witness.left,witness.right,rfl,by
          cases witness with
          | mk type disjunction left right same => cases type; cases same; cases typed; rfl⟩
  | _ => none

def compile {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (map : Source.Idx Γ .bool → Idx Δ (.val .bool)) (base : Nat) (fragment : Frag Δ)
    (stmt : Source.RStmt E [] false .body Γ Γ) : Option (List Evm.Instr) := do
  let recognized ← view stmt
  let checked ← compileStmt base fragment
    (LogicalGuard.target (C:=C) recognized.disjunction (map recognized.left) (map recognized.right))
  pure checked.code

theorem accepts_logical {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (map : Source.Idx Γ .bool → Idx Δ (.val .bool)) (base : Nat) (fragment : Frag Δ)
    (disjunction : Bool) (a b : Source.Idx Γ .bool) :
    compile (C:=C) map base fragment (LogicalGuard.statement (E:=E) disjunction a b) =
      some (LogicalGuard.selected (C:=C) base fragment disjunction (map a) (map b)).code := by
  cases disjunction <;> rfl

theorem selected_correct {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (map : Source.Idx Γ .bool → Idx Δ (.val .bool)) (base : Nat) (fragment : Frag Δ)
    (stmt : Source.RStmt E [] false .body Γ Γ) (code : List Evm.Instr)
    (selected : compile (C:=C) map base fragment stmt = some code)
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (locals : Source.Locals E.layout Γ)
    (source : Source.St E) (state : State C Δ)
    (localRelation : ∀ (i : Source.Idx Γ .bool) (value : Bool),
      locals.get i = .bool value → TEnv.get (map i) state.env = value)
    {L frame : Nat} {addresses : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L base frame fragment state addresses machine) :
    ∃ (disjunction : Bool) (a b : Source.Idx Γ .bool) (x y : Bool),
      locals.get a = .bool x ∧ locals.get b = .bool y ∧
      compileStmt base fragment (LogicalGuard.target (C:=C) disjunction (map a) (map b)) =
        some (LogicalGuard.selected base fragment disjunction (map a) (map b)) ∧
      (Source.execS G F (n+7) 0 none stmt locals).run (Source.L0 E,source) =
        (if LogicalGuard.result disjunction x y then (.ok (.normal locals),(Source.L0 E,source))
         else (.error (.revert []),(Source.L0 E,source))) ∧
      run code machine = (if LogicalGuard.result disjunction x y then .ok machine 0 else .revert) := by
  cases found : view stmt with
  | none =>
      simp only [compile,found,bind,Option.bind] at selected
      cases selected
  | some witness =>
      have codeEq : (LogicalGuard.selected (C:=C) base fragment witness.disjunction
          (map witness.left) (map witness.right)).code = code := by
        simpa only [compile,found,bind,Option.bind,LogicalGuard.public_selection,pure,Option.some.injEq] using selected
      cases leftRead : locals.get witness.left with
      | bool x =>
        cases rightRead : locals.get witness.right with
        | bool y =>
          have actual := LogicalGuard.agreement G F n locals source state witness.disjunction
            witness.left witness.right (map witness.left) (map witness.right) x y
            leftRead rightRead (localRelation _ _ leftRead) (localRelation _ _ rightRead) represented
          refine ⟨witness.disjunction,witness.left,witness.right,x,y,leftRead,rightRead,actual.2.1,?_,?_⟩
          · exact (congrArg (fun chosen : Source.RStmt E [] false .body Γ Γ =>
              (Source.execS G F (n+7) 0 none chosen locals).run (Source.L0 E,source))
              (eq_of_heq witness.same)).trans actual.1
          · rw [←codeEq]
            exact actual.2.2
        | memRef impossible _ => cases impossible
        | storRef impossible _ => cases impossible
        | cdRef impossible _ _ => cases impossible
      | memRef impossible _ => cases impossible
      | storRef impossible _ => cases impossible
      | cdRef impossible _ _ => cases impossible

#print axioms accepts_logical
#print axioms selected_correct
end Solidity.Backend.FailurePaths.LogicalGuardSelection
