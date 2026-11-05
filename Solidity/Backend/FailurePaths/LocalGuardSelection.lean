import Solidity.Backend.FailurePaths.RuntimeGuard

/-! Executable selection from actual indexed Source statements for a bare
require of a Boolean local. The context map is explicit; compilation invokes
the public checked memory statement compiler. Every successful decision derives
both actual runs from initial local correspondence and full StateRepr.
This does not construct a whole-program context map or a bytecode relation. -/
namespace Solidity.Backend.FailurePaths.LocalGuardSelection
open Evm Evm.Memory

structure View {E : Source.Env} {Γ Ξ : Source.RCtx}
    (stmt : Source.RStmt E [] false .body Γ Ξ) where
  index : Source.Idx Γ .bool
  contexts : Ξ = Γ
  same : HEq stmt (RuntimeGuard.statement (E:=E) index)

structure BoolLocalView {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (expr : Source.RExpr E Γ τ) where
  type : τ = .bool
  index : Source.Idx Γ .bool
  same : type ▸ expr = .local index

def boolLocal {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy} :
    (expr : Source.RExpr E Γ τ) → Option (BoolLocalView expr)
  | .local i => if h : τ = .bool then some ⟨h,h ▸ i,by cases h; rfl⟩ else none
  | _ => none

def view {E : Source.Env} {Γ Ξ : Source.RCtx} :
    (stmt : Source.RStmt E [] false .body Γ Ξ) → Option (View stmt)
  | .expr (.builtin .require (.cons head .nil) typed) =>
      match boolLocal head with
      | none => none
      | some witness => some ⟨witness.index,rfl,by
          cases witness with
          | mk type i same => cases type; cases same; cases typed; rfl⟩
  | _ => none

def compile {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (map : Source.Idx Γ .bool → Idx Δ (.val .bool)) (base : Nat) (fragment : Frag Δ)
    (stmt : Source.RStmt E [] false .body Γ Γ) : Option (List Evm.Instr) := do
  let recognized ← view stmt
  let checked ← compileStmt base fragment (RuntimeGuard.target (C:=C) (map recognized.index))
  pure checked.code

theorem accepts_local {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (map : Source.Idx Γ .bool → Idx Δ (.val .bool)) (base : Nat) (fragment : Frag Δ)
    (i : Source.Idx Γ .bool) :
    compile (E:=E) (C:=C) map base fragment (RuntimeGuard.statement (E:=E) i) =
      some (RuntimeGuard.selected (C:=C) base fragment (map i)).code := by
  simp only [compile,view,boolLocal,RuntimeGuard.statement,RuntimeGuard.public_selection,↓reduceDIte,
    bind,Option.bind,pure]

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
    ∃ (i : Source.Idx Γ .bool) (value : Bool),
      locals.get i = .bool value ∧
      compileStmt base fragment (RuntimeGuard.target (C:=C) (map i)) =
        some (RuntimeGuard.selected base fragment (map i)) ∧
      (Source.execS G F (n+7) 0 none stmt locals).run (Source.L0 E,source) =
        (if value then (.ok (.normal locals),(Source.L0 E,source))
         else (.error (.revert []),(Source.L0 E,source))) ∧
      run code machine = (if value then .ok machine 0 else .revert) := by
  cases found : view stmt with
  | none =>
      simp only [compile,found,bind,Option.bind] at selected
      cases selected
  | some witness =>
      have codeEq : (RuntimeGuard.selected (C:=C) base fragment (map witness.index)).code = code := by
        simpa only [compile,found,bind,Option.bind,RuntimeGuard.public_selection,pure,Option.some.injEq] using selected
      cases read : locals.get witness.index with
      | bool value =>
          have actual := RuntimeGuard.agreement G F n witness.index (map witness.index) value
            locals source state read (localRelation _ _ read) represented
          refine ⟨witness.index,value,read,actual.2.1,?_,?_⟩
          · rw [eq_of_heq witness.same]
            exact actual.1
          · rw [←codeEq]
            exact actual.2.2
      | memRef impossible _ => cases impossible
      | storRef impossible _ => cases impossible
      | cdRef impossible _ _ => cases impossible

#print axioms accepts_local
#print axioms selected_correct
end Solidity.Backend.FailurePaths.LocalGuardSelection
