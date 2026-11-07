import Solidity.Backend.FailurePaths.GuardBodySelection

/-! Root Source block selection through the public checked memory statement
compiler. The existing structural body view proves scope equality; the actual
Source close operation restores locals. No evaluator or compiler is changed. -/
namespace Solidity.Backend.FailurePaths.GuardBlockSelection
open Evm Evm.Memory CheckedGuards

structure View {E : Source.Env} {R : List Source.STy} {M : Bool} {k : Source.SCtx}
    {Γ Δ : Source.RCtx} (statement : Source.RStmt E R M k Γ Δ) where
  same : Δ = Γ
  output : Source.RCtx
  body : Source.RItems E R M k Γ output
  admitted : GuardBodySelection.View body
  reconstruct : cast (congrArg (fun result => Source.RStmt E R M k Γ result) same) statement = .block body

def view {E : Source.Env} {R : List Source.STy} {M : Bool} {k : Source.SCtx} {Γ Δ : Source.RCtx} :
    (statement : Source.RStmt E R M k Γ Δ) → Option (View statement)
  | .block body => (GuardBodySelection.view body).map (fun admitted => ⟨rfl,_,body,admitted,rfl⟩)
  | _ => none

def lower {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (maps : Maps Γ Δ) (statement : Source.RStmt E [] false .body Γ Γ) : Option (Stmt C Δ Δ) := do
  let admitted ← view statement
  let program ← GuardSequences.lower maps admitted.admitted.statements
  pure (.block program)

def compile {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (maps : Maps Γ Δ) (base : Nat) (fragment : Frag Δ)
    (statement : Source.RStmt E [] false .body Γ Γ) : Option (List Evm.Instr) := do
  let target ← lower (C:=C) maps statement
  let checked ← Memory.compileStmt base fragment target
  pure checked.code

def blockChecked {C : Contract} {Δ : Ctx} {base : Nat} {fragment : Frag Δ}
    {program : Prog C Δ Δ} (checked : CompiledProg base fragment program) :
    CompiledStmt base fragment (.block program) :=
  ⟨checked.frag.restrict Δ,checked.code,.block program checked.code checked.cert⟩

theorem block_public {C : Contract} {Δ : Ctx} (base : Nat) (fragment : Frag Δ)
    (program : Prog C Δ Δ) (checked : CompiledProg base fragment program)
    (selected : Memory.compileProg base fragment program = some checked) :
    Memory.compileStmt base fragment (.block program) = some (blockChecked checked) := by
  change (do
    let inner ← Memory.compileProg base fragment program
    pure (blockChecked inner)) = some (blockChecked checked)
  rw [selected]
  rfl

theorem selected_public {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (maps : Maps Γ Δ) (base : Nat) (fragment : Frag Δ)
    (statement : Source.RStmt E [] false .body Γ Γ) (code : List Evm.Instr)
    (selected : compile (C:=C) maps base fragment statement = some code) :
    ∃ (admitted : View statement) (program : Prog C Δ Δ) (checked : CompiledProg base fragment program),
      view statement = some admitted ∧
      GuardSequences.lower maps admitted.admitted.statements = some program ∧
      Memory.compileProg base fragment program = some checked ∧
      Memory.compileStmt base fragment (.block program) = some (blockChecked checked) ∧
      (blockChecked checked).code = code := by
  cases found : view statement with
  | none => simp only [compile,lower,found,bind,Option.bind,reduceCtorEq] at selected
  | some admitted =>
    cases lowered : GuardSequences.lower (C:=C) maps admitted.admitted.statements with
    | none => simp only [compile,lower,found,lowered,bind,Option.bind,reduceCtorEq] at selected
    | some program =>
      obtain ⟨checked,compiled,_⟩ := GuardSequences.lowered_public maps base fragment
        admitted.admitted.statements program lowered
      have publicChoice := block_public base fragment program checked compiled
      simp only [compile,lower,found,lowered,bind,Option.bind,pure,publicChoice,Option.some.injEq] at selected
      exact ⟨admitted,program,checked,rfl,lowered,compiled,publicChoice,selected⟩

theorem compile_of_view {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (maps : Maps Γ Δ) (base : Nat) (fragment : Frag Δ)
    (statement : Source.RStmt E [] false .body Γ Γ) (admitted : View statement)
    (found : view statement = some admitted) :
    compile (C:=C) maps base fragment statement =
      GuardSequences.compile (C:=C) maps base fragment admitted.admitted.statements := by
  cases lowered : GuardSequences.lower (C:=C) maps admitted.admitted.statements with
  | none => simp only [compile,lower,found,GuardSequences.compile,lowered,bind,Option.bind]
  | some program =>
    obtain ⟨checked,compiled,_⟩ := GuardSequences.lowered_public maps base fragment
      admitted.admitted.statements program lowered
    have publicChoice := block_public base fragment program checked compiled
    simp only [compile,lower,found,GuardSequences.compile,lowered,bind,Option.bind,pure,publicChoice,compiled]
    rfl

theorem restore_self {D : Source.Layout} {Γ : Source.RCtx} (locals : Source.Locals D Γ) :
    locals.restore Γ = .ok locals := by
  unfold Source.Locals.restore
  split
  next h =>
    have dropped (n : Nat) (same : Γ.drop n = Γ) (zero : n = 0) :
        (same ▸ locals.drop n : Source.Locals D Γ) = locals := by
      cases zero
      rfl
    rw [dropped _ h (Nat.sub_self _)]
    rfl
  next absent => exact (absent (by rw [Nat.sub_self,List.drop_zero])).elim

theorem close_normal {D : Source.Layout} {Γ : Source.RCtx} (locals : Source.Locals D Γ) :
    (Source.Out.normal locals : Source.Out D Γ Γ).close = .ok (.normal locals) := by
  change (do let restored ← locals.restore Γ; pure (Source.Out.normal restored : Source.Out D Γ Γ)) = .ok (.normal locals)
  rw [restore_self]
  rfl

theorem body_correct {E : Source.Env} {Γ Ξ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (maps : Maps Γ Δ) (base : Nat) (fragment : Frag Δ)
    (body : Source.RItems E [] false .body Γ Ξ) (admitted : GuardBodySelection.View body)
    (program : Prog C Δ Δ)
    (lowered : GuardSequences.lower maps admitted.statements = some program)
    (checked : CompiledProg base fragment program)
    (compiled : Memory.compileProg base fragment program = some checked)
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (locals : Source.Locals E.layout Γ)
    (source : Source.St E) (state : State C Δ) (related : Related maps locals state)
    {L frame : Nat} {addresses : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L base frame fragment state addresses machine) :
    ∃ value : Bool,
      (Source.execS G F (n+admitted.statements.length+8) 0 none (.block body) locals).run
        (Source.L0 E,source) =
        (if value then (.ok (.normal locals),(Source.L0 E,source))
         else (.error (.revert []),(Source.L0 E,source))) ∧
      run checked.code machine = (if value then .ok machine 0 else .revert) := by
  rcases admitted with ⟨same,statements,reconstructed⟩
  cases same
  have sourceItems : GuardSequences.items statements = body :=
    (GuardBodySelection.rebuild_body statements).symm.trans reconstructed.symm
  obtain ⟨value,sourceRun,targetRun⟩ := GuardSequences.lowered_correct maps base fragment
    statements program lowered checked compiled G F n locals source state related represented
  rw [sourceItems] at sourceRun
  refine ⟨value,?_,targetRun⟩
  have fuel : n+statements.length+8 = (n+statements.length+7)+1 := by omega
  rw [fuel,Source.execS,Source.Hoare.run_bind,sourceRun]
  cases value with
  | false => rfl
  | true =>
    change (Source.EM.lift ((Source.Out.normal locals : Source.Out E.layout Γ Γ).close)).run
      (Source.L0 E,source) = _
    rw [close_normal]
    rfl

theorem selected_correct {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (maps : Maps Γ Δ) (base : Nat) (fragment : Frag Δ)
    (statement : Source.RStmt E [] false .body Γ Γ) (code : List Evm.Instr)
    (selected : compile (C:=C) maps base fragment statement = some code)
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (locals : Source.Locals E.layout Γ)
    (source : Source.St E) (state : State C Δ) (related : Related maps locals state)
    {L frame : Nat} {addresses : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L base frame fragment state addresses machine) :
    ∃ (admitted : View statement) (value : Bool),
      view statement = some admitted ∧
      (Source.execS G F (n+admitted.admitted.statements.length+8) 0 none statement locals).run
        (Source.L0 E,source) =
        (if value then (.ok (.normal locals),(Source.L0 E,source))
         else (.error (.revert []),(Source.L0 E,source))) ∧
      run code machine = (if value then .ok machine 0 else .revert) := by
  obtain ⟨admitted,program,checked,found,lowered,compiled,_,sameCode⟩ :=
    selected_public maps base fragment statement code selected
  obtain ⟨value,sourceRun,targetRun⟩ := body_correct maps base fragment admitted.body
    admitted.admitted program lowered checked compiled G F n locals source state related represented
  rw [← admitted.reconstruct] at sourceRun
  refine ⟨admitted,value,found,sourceRun,?_⟩
  rw [← sameCode]
  exact targetRun

#print axioms block_public
#print axioms selected_public
#print axioms compile_of_view
#print axioms restore_self
#print axioms close_normal
#print axioms body_correct
#print axioms selected_correct
end Solidity.Backend.FailurePaths.GuardBlockSelection
