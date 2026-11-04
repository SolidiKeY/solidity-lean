import Solidity.Backend.FailurePaths.CheckedGuards

/-! Computable lowering from admitted indexed Source guards to the existing
intrinsic statement type. This is neither a new IR nor extraction from an
existential proof. Compilation invokes public Memory.compileStmt once and is
proved equal to the previously checked dispatch entry point. -/
namespace Solidity.Backend.FailurePaths.GuardLowering
open Evm Evm.Memory CheckedGuards

def lower {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (maps : Maps Γ Δ) (stmt : Source.RStmt E [] false .body Γ Γ) : Option (Stmt C Δ Δ) :=
  match LocalGuardSelection.view stmt with
  | some witness => some (RuntimeGuard.target (maps.booleans witness.index))
  | none => match LogicalGuardSelection.view stmt with
    | some witness => some (LogicalGuard.target witness.disjunction
        (maps.booleans witness.left) (maps.booleans witness.right))
    | none => match RelationalGuardSelection.view stmt with
      | some witness => some (RelationalGuard.target witness.order witness.signed
          (maps.integers witness.signed witness.left) (maps.integers witness.signed witness.right))
      | none => none

def compile {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (maps : Maps Γ Δ) (base : Nat) (fragment : Frag Δ)
    (stmt : Source.RStmt E [] false .body Γ Γ) : Option (List Evm.Instr) := do
  let target ← lower (C:=C) maps stmt
  let checked ← compileStmt base fragment target
  pure checked.code

theorem compile_eq_checked {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (maps : Maps Γ Δ) (base : Nat) (fragment : Frag Δ) (stmt : Source.RStmt E [] false .body Γ Γ) :
    compile (C:=C) maps base fragment stmt = CheckedGuards.compile (C:=C) maps base fragment stmt := by
  cases localView : LocalGuardSelection.view stmt with
  | some witness =>
    simp only [compile,lower,CheckedGuards.compile,LocalGuardSelection.compile,localView,
      bind,Option.bind,RuntimeGuard.public_selection,pure]
  | none =>
    cases logicalView : LogicalGuardSelection.view stmt with
    | some witness =>
      simp only [compile,lower,CheckedGuards.compile,LocalGuardSelection.compile,LogicalGuardSelection.compile,
        localView,logicalView,bind,Option.bind,LogicalGuard.public_selection,pure]
    | none =>
      cases relationalView : RelationalGuardSelection.view stmt with
      | some witness =>
        simp only [compile,lower,CheckedGuards.compile,LocalGuardSelection.compile,LogicalGuardSelection.compile,
          RelationalGuardSelection.compile,localView,logicalView,relationalView,bind,Option.bind,
          RelationalGuard.public_selection,pure]
      | none =>
        simp only [compile,lower,CheckedGuards.compile,LocalGuardSelection.compile,LogicalGuardSelection.compile,
          RelationalGuardSelection.compile,localView,logicalView,relationalView,bind,Option.bind]

theorem lowered_require {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (maps : Maps Γ Δ) (stmt : Source.RStmt E [] false .body Γ Γ) (target : Stmt C Δ Δ)
    (lowered : lower maps stmt = some target) :
    ∃ condition : Val C Δ .bool, target = .require condition := by
  cases localView : LocalGuardSelection.view stmt with
  | some witness =>
    simp only [lower,localView,Option.some.injEq] at lowered
    cases lowered
    exact ⟨_,rfl⟩
  | none =>
    cases logicalView : LogicalGuardSelection.view stmt with
    | some witness =>
      simp only [lower,localView,logicalView,Option.some.injEq] at lowered
      cases lowered
      exact ⟨_,rfl⟩
    | none =>
      cases relationalView : RelationalGuardSelection.view stmt with
      | some witness =>
        simp only [lower,localView,logicalView,relationalView,Option.some.injEq] at lowered
        cases lowered
        exact ⟨_,rfl⟩
      | none => simp only [lower,localView,logicalView,relationalView,reduceCtorEq] at lowered

theorem lowered_compiles {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (maps : Maps Γ Δ) (base : Nat) (fragment : Frag Δ)
    (stmt : Source.RStmt E [] false .body Γ Γ) (target : Stmt C Δ Δ)
    (lowered : lower maps stmt = some target) :
    ∃ checked : CompiledStmt base fragment target, compileStmt base fragment target = some checked := by
  cases localView : LocalGuardSelection.view stmt with
  | some witness =>
    simp only [lower,localView,Option.some.injEq] at lowered
    cases lowered
    exact ⟨_,RuntimeGuard.public_selection base fragment _⟩
  | none =>
    cases logicalView : LogicalGuardSelection.view stmt with
    | some witness =>
      simp only [lower,localView,logicalView,Option.some.injEq] at lowered
      cases lowered
      exact ⟨_,LogicalGuard.public_selection base fragment _ _ _⟩
    | none =>
      cases relationalView : RelationalGuardSelection.view stmt with
      | some witness =>
        simp only [lower,localView,logicalView,relationalView,Option.some.injEq] at lowered
        cases lowered
        exact ⟨_,RelationalGuard.public_selection base fragment _ _ _ _⟩
      | none => simp only [lower,localView,logicalView,relationalView,reduceCtorEq] at lowered

theorem selected_correct {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (maps : Maps Γ Δ) (base : Nat) (fragment : Frag Δ)
    (stmt : Source.RStmt E [] false .body Γ Γ) (code : List Evm.Instr)
    (selected : compile (C:=C) maps base fragment stmt = some code)
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (locals : Source.Locals E.layout Γ)
    (source : Source.St E) (state : State C Δ) (related : Related maps locals state)
    {L frame : Nat} {addresses : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L base frame fragment state addresses machine) :
    ∃ value : Bool,
      (Source.execS G F (n+7) 0 none stmt locals).run (Source.L0 E,source) =
        (if value then (.ok (.normal locals),(Source.L0 E,source))
         else (.error (.revert []),(Source.L0 E,source))) ∧
      run code machine = (if value then .ok machine 0 else .revert) := by
  rw [compile_eq_checked] at selected
  exact CheckedGuards.selected_correct maps base fragment stmt code selected G F n locals source state related represented

theorem lowered_correct {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (maps : Maps Γ Δ) (base : Nat) (fragment : Frag Δ)
    (stmt : Source.RStmt E [] false .body Γ Γ) (target : Stmt C Δ Δ)
    (lowered : lower maps stmt = some target) (checked : CompiledStmt base fragment target)
    (compiled : compileStmt base fragment target = some checked)
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (locals : Source.Locals E.layout Γ)
    (source : Source.St E) (state : State C Δ) (related : Related maps locals state)
    {L frame : Nat} {addresses : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L base frame fragment state addresses machine) :
    ∃ value : Bool,
      (Source.execS G F (n+7) 0 none stmt locals).run (Source.L0 E,source) =
        (if value then (.ok (.normal locals),(Source.L0 E,source))
         else (.error (.revert []),(Source.L0 E,source))) ∧
      run checked.code machine = (if value then .ok machine 0 else .revert) := by
  have selected : compile (C:=C) maps base fragment stmt = some checked.code := by
    simp only [compile,lowered,bind,Option.bind,compiled,pure]
  exact selected_correct maps base fragment stmt checked.code selected G F n locals source state related represented

#print axioms lowered_compiles
#print axioms compile_eq_checked
#print axioms lowered_require
#print axioms selected_correct
#print axioms lowered_correct
end Solidity.Backend.FailurePaths.GuardLowering
