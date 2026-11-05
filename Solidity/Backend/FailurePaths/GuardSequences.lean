import Solidity.Backend.FailurePaths.GuardLowering

/-! Finite sequences of the existing indexed guard leaves. Both the Source
items and intrinsic program use their existing representations. Selection is
through the public memory program compiler; no leaf execution is assumed. -/
namespace Solidity.Backend.FailurePaths.GuardSequences
open Evm Evm.Memory CheckedGuards

def items {E : Source.Env} {Γ : Source.RCtx} :
    List (Source.RStmt E [] false .body Γ Γ) → Source.RItems E [] false .body Γ Γ
  | [] => .nil
  | head :: tail => .stmt head (items tail)

def lower {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (maps : Maps Γ Δ) : List (Source.RStmt E [] false .body Γ Γ) → Option (Prog C Δ Δ)
  | [] => some .nil
  | head :: tail => do
    let first ← GuardLowering.lower maps head
    let rest ← lower maps tail
    pure (.cons first rest)

def compile {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (maps : Maps Γ Δ) (base : Nat) (fragment : Frag Δ)
    (statements : List (Source.RStmt E [] false .body Γ Γ)) : Option (List Evm.Instr) := do
  let target ← lower (C:=C) maps statements
  let checked ← Memory.compileProg base fragment target
  pure checked.code

theorem require_frag {C : Contract} {Δ : Ctx} (base : Nat) (fragment : Frag Δ)
    (condition : Val C Δ .bool) (checked : CompiledStmt base fragment (.require condition))
    (selected : Memory.compileStmt base fragment (.require condition) = some checked) :
    checked.frag = fragment := by
  change (do
    let value ← Memory.compileVal base fragment condition
    pure (⟨fragment,value.code ++ assertTop,.require fragment condition value.code value.cert⟩ :
      CompiledStmt base fragment (.require condition))) = some checked at selected
  cases found : Memory.compileVal base fragment condition with
  | none => simp only [found,bind,Option.bind,reduceCtorEq] at selected
  | some value =>
    simp only [found,bind,Option.bind,pure,Option.some.injEq] at selected
    cases selected
    rfl

theorem leaf_frag {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (maps : Maps Γ Δ) (base : Nat) (fragment : Frag Δ)
    (source : Source.RStmt E [] false .body Γ Γ) (target : Stmt C Δ Δ)
    (lowered : GuardLowering.lower maps source = some target)
    (checked : CompiledStmt base fragment target)
    (selected : Memory.compileStmt base fragment target = some checked) : checked.frag = fragment := by
  obtain ⟨condition,same⟩ := GuardLowering.lowered_require maps source target lowered
  cases same
  exact require_frag base fragment condition checked selected

theorem lowered_public {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (maps : Maps Γ Δ) (base : Nat) (fragment : Frag Δ)
    (statements : List (Source.RStmt E [] false .body Γ Γ)) (target : Prog C Δ Δ)
    (lowered : lower maps statements = some target) :
    ∃ checked : CompiledProg base fragment target,
      Memory.compileProg base fragment target = some checked ∧ checked.frag = fragment := by
  induction statements generalizing target with
  | nil =>
    simp only [lower,Option.some.injEq] at lowered
    cases lowered
    exact ⟨⟨fragment,[],.nil fragment⟩,rfl,rfl⟩
  | cons head tail ih =>
    cases headChoice : GuardLowering.lower (C:=C) maps head with
    | none => simp only [lower,headChoice,bind,Option.bind,reduceCtorEq] at lowered
    | some first =>
      cases tailChoice : lower (C:=C) maps tail with
      | none => simp only [lower,headChoice,tailChoice,bind,Option.bind,reduceCtorEq] at lowered
      | some rest =>
        simp only [lower,headChoice,tailChoice,bind,Option.bind,pure,Option.some.injEq] at lowered
        cases lowered
        obtain ⟨hc,hs⟩ := GuardLowering.lowered_compiles maps base fragment head first headChoice
        have hf := leaf_frag maps base fragment head first headChoice hc hs
        obtain ⟨tc,ts,tf⟩ := ih rest tailChoice
        cases hc with
        | mk output code cert =>
          change output = fragment at hf
          cases hf
          exact ⟨⟨tc.frag,code ++ tc.code,.cons cert tc.cert⟩,
            by simp only [Memory.compileProg,hs,bind,Option.bind,ts,pure],tf⟩

theorem lowered_correct {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (maps : Maps Γ Δ) (base : Nat) (fragment : Frag Δ)
    (statements : List (Source.RStmt E [] false .body Γ Γ)) (target : Prog C Δ Δ)
    (lowered : lower maps statements = some target)
    (checked : CompiledProg base fragment target)
    (compiled : Memory.compileProg base fragment target = some checked)
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (locals : Source.Locals E.layout Γ)
    (source : Source.St E) (state : State C Δ) (related : Related maps locals state)
    {L frame : Nat} {addresses : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L base frame fragment state addresses machine) :
    ∃ value : Bool,
      (Source.execItems G F (n+statements.length+7) 0 none (items statements) locals).run
        (Source.L0 E,source) =
        (if value then (.ok (.normal locals),(Source.L0 E,source))
         else (.error (.revert []),(Source.L0 E,source))) ∧
      run checked.code machine = (if value then .ok machine 0 else .revert) := by
  induction statements generalizing target with
  | nil =>
    simp only [lower,Option.some.injEq] at lowered
    cases lowered
    change some (⟨fragment,[],.nil fragment⟩ : CompiledProg base fragment .nil) = some checked at compiled
    cases compiled
    exact ⟨true,rfl,rfl⟩
  | cons head tail ih =>
    cases headChoice : GuardLowering.lower (C:=C) maps head with
    | none => simp only [lower,headChoice,bind,Option.bind,reduceCtorEq] at lowered
    | some first =>
      cases tailChoice : lower (C:=C) maps tail with
      | none => simp only [lower,headChoice,tailChoice,bind,Option.bind,reduceCtorEq] at lowered
      | some rest =>
        simp only [lower,headChoice,tailChoice,bind,Option.bind,pure,Option.some.injEq] at lowered
        cases lowered
        obtain ⟨hc,hs⟩ := GuardLowering.lowered_compiles maps base fragment head first headChoice
        have hf := leaf_frag maps base fragment head first headChoice hc hs
        cases hc with
        | mk output code cert =>
          change output = fragment at hf
          cases hf
          obtain ⟨tc,ts,_⟩ := lowered_public maps base fragment tail rest tailChoice
          simp only [Memory.compileProg,hs,bind,Option.bind,ts,pure,Option.some.injEq] at compiled
          cases compiled
          obtain ⟨left,sourceHead,targetHead⟩ := GuardLowering.lowered_correct maps base fragment
            head first headChoice ⟨fragment,code,cert⟩ hs G F (n+tail.length) locals source state related represented
          obtain ⟨right,sourceTail,targetTail⟩ := ih rest tailChoice tc ts
          refine ⟨left && right,?_,?_⟩
          · have fuel : n+(head::tail).length+7 = (n+tail.length+7)+1 := by simp only [List.length_cons]; omega
            rw [fuel]
            simp only [items]
            rw [Source.execItems]
            rw [Source.Hoare.run_bind,sourceHead]
            cases left <;> cases right <;>
              simp only [Bool.false_and,Bool.true_and,Bool.false_eq_true,if_false,if_true] at sourceTail ⊢
            all_goals first | rfl | (rw [Source.Hoare.run_bind,sourceTail] <;> rfl)
          · cases left with
            | false => exact run_append_revert targetHead
            | true =>
              rw [run_append_skip targetHead]
              exact targetTail

theorem selected_correct {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (maps : Maps Γ Δ) (base : Nat) (fragment : Frag Δ)
    (statements : List (Source.RStmt E [] false .body Γ Γ)) (code : List Evm.Instr)
    (selected : compile (C:=C) maps base fragment statements = some code)
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (locals : Source.Locals E.layout Γ)
    (source : Source.St E) (state : State C Δ) (related : Related maps locals state)
    {L frame : Nat} {addresses : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L base frame fragment state addresses machine) :
    ∃ value : Bool,
      (Source.execItems G F (n+statements.length+7) 0 none (items statements) locals).run
        (Source.L0 E,source) =
        (if value then (.ok (.normal locals),(Source.L0 E,source))
         else (.error (.revert []),(Source.L0 E,source))) ∧
      run code machine = (if value then .ok machine 0 else .revert) := by
  cases found : lower (C:=C) maps statements with
  | none => simp only [compile,found,bind,Option.bind,reduceCtorEq] at selected
  | some target =>
    obtain ⟨checked,compiled,_⟩ := lowered_public maps base fragment statements target found
    simp only [compile,found,bind,Option.bind,compiled,pure,Option.some.injEq] at selected
    cases selected
    exact lowered_correct maps base fragment statements target found checked compiled G F n locals source state related represented

#print axioms selected_correct
#print axioms lowered_correct
#print axioms require_frag
#print axioms leaf_frag
#print axioms lowered_public
end Solidity.Backend.FailurePaths.GuardSequences
