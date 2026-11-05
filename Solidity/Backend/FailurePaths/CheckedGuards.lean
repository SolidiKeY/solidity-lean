import Solidity.Backend.FailurePaths.LocalGuardSelection
import Solidity.Backend.FailurePaths.LogicalGuardSelection
import Solidity.Backend.FailurePaths.RelationalGuardSelection

/-! One executable indexed-Source guard entry point, dispatching to the three
proved public-memory-compiler selectors. Maps and initial typed reads remain
explicit. No new AST, evaluator, target compiler or whole-program admission is
introduced; every successful dispatch has actual Source and target runs. -/
namespace Solidity.Backend.FailurePaths.CheckedGuards
open Evm Evm.Memory Lowering.V07 PrimitivePackets.Comparisons

structure Maps (Γ : Source.RCtx) (Δ : Ctx) where
  booleans : Source.Idx Γ .bool → Idx Δ (.val .bool)
  integers : ∀ signed, Source.Idx Γ (.int (ty signed)) → Idx Δ (.val (prim signed))

structure Related {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (maps : Maps Γ Δ) (locals : Source.Locals E.layout Γ) (state : State C Δ) : Prop where
  booleans : ∀ (i : Source.Idx Γ .bool) (value : Bool),
    locals.get i = .bool value → TEnv.get (maps.booleans i) state.env = value
  integers : ∀ signed (i : Source.Idx Γ (.int (ty signed))) (x : Int)
    (range : (ty signed).lo ≤ x ∧ x ≤ (ty signed).hi),
    locals.get i = .int x range →
      TEnv.get (maps.integers signed i) state.env = integerValue (ty signed) x range

def compile {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (maps : Maps Γ Δ) (base : Nat) (fragment : Frag Δ)
    (stmt : Source.RStmt E [] false .body Γ Γ) : Option (List Evm.Instr) :=
  match LocalGuardSelection.compile (C:=C) maps.booleans base fragment stmt with
  | some code => some code
  | none => match LogicalGuardSelection.compile (C:=C) maps.booleans base fragment stmt with
    | some code => some code
    | none => RelationalGuardSelection.compile (C:=C) maps.integers base fragment stmt

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
  cases localChoice : LocalGuardSelection.compile (C:=C) maps.booleans base fragment stmt with
  | some localCode =>
    have same : localCode = code := by simpa only [compile,localChoice,Option.some.injEq] using selected
    cases same
    obtain ⟨i,value,read,publicChoice,sourceRun,targetRun⟩ :=
      LocalGuardSelection.selected_correct maps.booleans base fragment stmt code localChoice
        G F n locals source state related.booleans represented
    exact ⟨value,sourceRun,targetRun⟩
  | none =>
    cases logicalChoice : LogicalGuardSelection.compile (C:=C) maps.booleans base fragment stmt with
    | some logicalCode =>
      have same : logicalCode = code := by
        simpa only [compile,localChoice,logicalChoice,Option.some.injEq] using selected
      cases same
      obtain ⟨disjunction,a,b,x,y,leftRead,rightRead,publicChoice,sourceRun,targetRun⟩ :=
        LogicalGuardSelection.selected_correct maps.booleans base fragment stmt code logicalChoice
          G F n locals source state related.booleans represented
      exact ⟨LogicalGuard.result disjunction x y,sourceRun,targetRun⟩
    | none =>
      have relationalChoice : RelationalGuardSelection.compile (C:=C) maps.integers base fragment stmt = some code := by
        simpa only [compile,localChoice,logicalChoice] using selected
      obtain ⟨o,signed,a,b,x,y,hx,hy,leftRead,rightRead,publicChoice,sourceRun,targetRun⟩ :=
        RelationalGuardSelection.selected_correct maps.integers base fragment stmt code relationalChoice
          G F n locals source state related.integers represented
      exact ⟨result o x y,sourceRun,targetRun⟩

/-- Every dispatched code list is the actual result of the public checked
memory statement compiler, with its existing intrinsic target/certificate. -/
theorem selected_public_compiler {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (maps : Maps Γ Δ) (base : Nat) (fragment : Frag Δ)
    (stmt : Source.RStmt E [] false .body Γ Γ) (code : List Evm.Instr)
    (selected : compile (C:=C) maps base fragment stmt = some code) :
    ∃ (target : Stmt C Δ Δ) (checked : CompiledStmt base fragment target),
      compileStmt base fragment target = some checked ∧ checked.code = code := by
  cases localChoice : LocalGuardSelection.compile (C:=C) maps.booleans base fragment stmt with
  | some chosen =>
    have same : chosen = code := by simpa only [compile,localChoice,Option.some.injEq] using selected
    have choice : LocalGuardSelection.compile (C:=C) maps.booleans base fragment stmt = some code :=
      localChoice.trans (congrArg some same)
    cases found : LocalGuardSelection.view stmt with
    | none => simp only [LocalGuardSelection.compile,found,bind,Option.bind,reduceCtorEq] at choice
    | some witness =>
      refine ⟨RuntimeGuard.target (maps.booleans witness.index),
        RuntimeGuard.selected base fragment (maps.booleans witness.index),
        RuntimeGuard.public_selection base fragment (maps.booleans witness.index),?_⟩
      simpa only [LocalGuardSelection.compile,found,bind,Option.bind,RuntimeGuard.public_selection,
        pure,Option.some.injEq] using choice
  | none =>
    cases logicalChoice : LogicalGuardSelection.compile (C:=C) maps.booleans base fragment stmt with
    | some chosen =>
      have same : chosen = code := by
        simpa only [compile,localChoice,logicalChoice,Option.some.injEq] using selected
      have choice : LogicalGuardSelection.compile (C:=C) maps.booleans base fragment stmt = some code :=
        logicalChoice.trans (congrArg some same)
      cases found : LogicalGuardSelection.view stmt with
      | none => simp only [LogicalGuardSelection.compile,found,bind,Option.bind,reduceCtorEq] at choice
      | some witness =>
        refine ⟨LogicalGuard.target witness.disjunction (maps.booleans witness.left) (maps.booleans witness.right),
          LogicalGuard.selected base fragment witness.disjunction (maps.booleans witness.left) (maps.booleans witness.right),
          LogicalGuard.public_selection base fragment witness.disjunction (maps.booleans witness.left) (maps.booleans witness.right),?_⟩
        simpa only [LogicalGuardSelection.compile,found,bind,Option.bind,LogicalGuard.public_selection,
          pure,Option.some.injEq] using choice
    | none =>
      have choice : RelationalGuardSelection.compile (C:=C) maps.integers base fragment stmt = some code := by
        simpa only [compile,localChoice,logicalChoice] using selected
      cases found : RelationalGuardSelection.view stmt with
      | none => simp only [RelationalGuardSelection.compile,found,bind,Option.bind,reduceCtorEq] at choice
      | some witness =>
        refine ⟨RelationalGuard.target witness.order witness.signed
            (maps.integers witness.signed witness.left) (maps.integers witness.signed witness.right),
          RelationalGuard.selected base fragment witness.order witness.signed
            (maps.integers witness.signed witness.left) (maps.integers witness.signed witness.right),
          RelationalGuard.public_selection base fragment witness.order witness.signed
            (maps.integers witness.signed witness.left) (maps.integers witness.signed witness.right),?_⟩
        simpa only [RelationalGuardSelection.compile,found,bind,Option.bind,RelationalGuard.public_selection,
          pure,Option.some.injEq] using choice

#print axioms selected_public_compiler
#print axioms selected_correct
end Solidity.Backend.FailurePaths.CheckedGuards
