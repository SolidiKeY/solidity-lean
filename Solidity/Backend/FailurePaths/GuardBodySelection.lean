import Solidity.Backend.FailurePaths.GuardSequences

/-! Direct admission of existing indexed Source items into the finite guard
compiler. The computed view contains only existing statements and a structural
reconstruction equality. It assumes neither compilation nor execution. -/
namespace Solidity.Backend.FailurePaths.GuardBodySelection
open Evm Evm.Memory CheckedGuards

def rebuild {E : Source.Env} {R : List Source.STy} {M : Bool} {k : Source.SCtx} {Γ : Source.RCtx} :
    List (Source.RStmt E R M k Γ Γ) → Source.RItems E R M k Γ Γ
  | [] => .nil
  | head :: tail => .stmt head (rebuild tail)

theorem rebuild_body {E : Source.Env} {Γ : Source.RCtx}
    (statements : List (Source.RStmt E [] false .body Γ Γ)) :
    rebuild statements = GuardSequences.items statements := by
  induction statements with
  | nil => rfl
  | cons head tail ih => simp only [rebuild,GuardSequences.items,ih]

structure View {E : Source.Env} {R : List Source.STy} {M : Bool} {k : Source.SCtx} {Γ Δ : Source.RCtx}
    (body : Source.RItems E R M k Γ Δ) where
  same : Δ = Γ
  statements : List (Source.RStmt E R M k Γ Γ)
  reconstruct : cast (congrArg (fun output => Source.RItems E R M k Γ output) same) body =
    rebuild statements

def view {E : Source.Env} {R : List Source.STy} {M : Bool} {k : Source.SCtx} {Γ Δ : Source.RCtx} :
    (body : Source.RItems E R M k Γ Δ) → Option (View body)
  | .nil => some ⟨rfl,[],rfl⟩
  | .stmt (.expr expression) rest =>
    match view rest with
    | none => none
    | some ⟨same,statements,reconstructed⟩ =>
      some ⟨same,.expr expression :: statements,by
        cases same
        exact congrArg (Source.RItems.stmt (.expr expression)) reconstructed⟩
  | _ => none
termination_by structural body => body


def compile {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (maps : Maps Γ Δ) (base : Nat) (fragment : Frag Δ)
    (body : Source.RItems E [] false .body Γ Γ) : Option (List Evm.Instr) := do
  let selected ← view body
  GuardSequences.compile (C:=C) maps base fragment selected.statements

theorem selected_public {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (maps : Maps Γ Δ) (base : Nat) (fragment : Frag Δ)
    (body : Source.RItems E [] false .body Γ Γ) (code : List Evm.Instr)
    (selected : compile (C:=C) maps base fragment body = some code) :
    ∃ (admitted : View body) (target : Prog C Δ Δ) (checked : CompiledProg base fragment target),
      view body = some admitted ∧ GuardSequences.lower maps admitted.statements = some target ∧
      Memory.compileProg base fragment target = some checked ∧ checked.frag = fragment ∧
      checked.code = code := by
  cases found : view body with
  | none => simp only [compile,found,bind,Option.bind,reduceCtorEq] at selected
  | some admitted =>
    simp only [compile,found,bind,Option.bind] at selected
    cases lowered : GuardSequences.lower (C:=C) maps admitted.statements with
    | none => simp only [GuardSequences.compile,lowered,bind,Option.bind,reduceCtorEq] at selected
    | some target =>
      obtain ⟨checked,compiled,same⟩ := GuardSequences.lowered_public maps base fragment
        admitted.statements target lowered
      simp only [GuardSequences.compile,lowered,bind,Option.bind,compiled,pure,Option.some.injEq] at selected
      exact ⟨admitted,target,checked,rfl,lowered,compiled,same,selected⟩

theorem selected_correct {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (maps : Maps Γ Δ) (base : Nat) (fragment : Frag Δ)
    (body : Source.RItems E [] false .body Γ Γ) (code : List Evm.Instr)
    (selected : compile (C:=C) maps base fragment body = some code)
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (locals : Source.Locals E.layout Γ)
    (source : Source.St E) (state : State C Δ) (related : Related maps locals state)
    {L frame : Nat} {addresses : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L base frame fragment state addresses machine) :
    ∃ (admitted : View body) (value : Bool),
      view body = some admitted ∧
      (Source.execItems G F (n+admitted.statements.length+7) 0 none body locals).run
        (Source.L0 E,source) =
        (if value then (.ok (.normal locals),(Source.L0 E,source))
         else (.error (.revert []),(Source.L0 E,source))) ∧
      run code machine = (if value then .ok machine 0 else .revert) := by
  cases found : view body with
  | none => simp only [compile,found,bind,Option.bind,reduceCtorEq] at selected
  | some admitted =>
    simp only [compile,found,bind,Option.bind] at selected
    obtain ⟨value,sourceRun,targetRun⟩ := GuardSequences.selected_correct maps base fragment
      admitted.statements code selected G F n locals source state related represented
    have reconstructed : GuardSequences.items admitted.statements = body :=
      (rebuild_body admitted.statements).symm.trans admitted.reconstruct.symm
    rw [reconstructed] at sourceRun
    exact ⟨admitted,value,rfl,sourceRun,targetRun⟩

#print axioms rebuild_body
#print axioms selected_public
#print axioms selected_correct
end Solidity.Backend.FailurePaths.GuardBodySelection
