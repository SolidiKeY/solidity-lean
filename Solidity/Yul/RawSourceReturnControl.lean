import Solidity.Yul.RawSourceVoidReturn

/-! Source control wrappers whose void return precedes every skipped condition
or tail. Outcomes use the explicit stored-clean projection and retain raw state.
This does not implement ordinary dirty reads or general loop/return composition. -/
namespace Solidity.Yul.RawSourceReturnControl

def doWhile {ctx : Solidity.Source.Ctx} (fuel : Nat) (state : RawFrame.State ctx) :=
  RawSourceVoidReturn.items (output := ctx.tys) fuel state

def unchecked {ctx : Solidity.Source.Ctx} {output : Solidity.Source.RCtx}
    (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R (Solidity.Source.Out ctx.env.layout ctx.tys output) × RawFrame.State ctx :=
  match fuel with
  | 0 => RawSourceVoidReturn.run 0 state
  | n+1 => RawSourceVoidReturn.items n state

def whileLiteral {ctx : Solidity.Source.Ctx} (choice : Bool) (fuel : Nat)
    (state : RawFrame.State ctx) :
    Solidity.Source.R (Solidity.Source.Out ctx.env.layout ctx.tys ctx.tys) × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 => match n with
    | 0 => (.error .timeout,state)
    | _+1 => (if choice then .ok (.ret state.clean) else .ok (.normal state.clean),state)

theorem doWhile_correct : ∀ (ctx : Solidity.Source.Ctx) (modifier l u : Bool)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph ctx.env)) (state : Solidity.Yul.RawFrame.State ctx)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool),
 (Solidity.Yul.RawSourceReturnControl.doWhile fuel state).2 = state ∧
 (Solidity.Source.execS glob frame fuel nps ph (.doWhile (l := l) (Solidity.Source.RStmt.ret (E := ctx.env) (R := []) (M := modifier) (k := ⟨true,u⟩) (Γ := ctx.tys) rfl) condition) state.clean).run
 (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawSourceVoidReturn.project (Solidity.Yul.RawSourceReturnControl.doWhile fuel state) := by
  intro ctx modifier l u glob frame fuel nps ph state condition
  cases fuel with
  | zero => exact ⟨rfl,rfl⟩
  | succ fuel => cases fuel <;> exact ⟨rfl,rfl⟩

theorem unchecked_correct : ∀ (ctx : Solidity.Source.Ctx) (modifier l : Bool)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph ctx.env)) (state : Solidity.Yul.RawFrame.State ctx)
 (innerOutput output : Solidity.Source.RCtx)
 (innerTail : Solidity.Source.RItems ctx.env [] modifier ⟨l,true⟩ ctx.tys innerOutput)
 (outerTail : Solidity.Source.RItems ctx.env [] modifier ⟨l,false⟩ ctx.tys output),
 (Solidity.Yul.RawSourceReturnControl.unchecked (output := output) fuel state).2 = state ∧
 (Solidity.Source.execItems glob frame fuel nps ph (.unchecked
   (.stmt (Solidity.Source.RStmt.ret (E := ctx.env) (R := []) (M := modifier) (k := ⟨l,true⟩) (Γ := ctx.tys) rfl) innerTail)
   outerTail) state.clean).run (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawSourceVoidReturn.project (Solidity.Yul.RawSourceReturnControl.unchecked (output := output) fuel state) := by
  intro ctx modifier l glob frame fuel nps ph state innerOutput output innerTail outerTail
  cases fuel with
  | zero => exact ⟨rfl,rfl⟩
  | succ fuel =>
    cases fuel with
    | zero => exact ⟨rfl,rfl⟩
    | succ fuel => cases fuel <;> exact ⟨rfl,rfl⟩

theorem whileLiteral_correct : ∀ (ctx : Solidity.Source.Ctx) (modifier l u : Bool)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph ctx.env)) (state : Solidity.Yul.RawFrame.State ctx)
 (choice : Bool),
 (Solidity.Yul.RawSourceReturnControl.whileLiteral choice fuel state).2 = state ∧
 (Solidity.Source.execS glob frame fuel nps ph (.whileLoop (l := l) (.bool choice)
   (Solidity.Source.RStmt.ret (E := ctx.env) (R := []) (M := modifier) (k := ⟨true,u⟩) (Γ := ctx.tys) rfl)) state.clean).run
 (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawSourceVoidReturn.project (Solidity.Yul.RawSourceReturnControl.whileLiteral choice fuel state) := by
  intro ctx modifier l u glob frame fuel nps ph state choice
  cases fuel with
  | zero => exact ⟨rfl,rfl⟩
  | succ fuel =>
    cases fuel with
    | zero => exact ⟨rfl,rfl⟩
    | succ fuel => cases choice <;> exact ⟨rfl,rfl⟩

theorem initializer_refused_correct : ∀ (ctx : Solidity.Source.Ctx) (modifier l u : Bool)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph ctx.env)) (state : Solidity.Yul.RawFrame.State ctx)
 (output : Solidity.Source.RCtx) (condition : Solidity.Source.ROptBool ctx.env ctx.tys)
 (post : Solidity.Source.ROptExpr ctx.env ctx.tys)
 (body : Solidity.Source.RStmt ctx.env [] modifier ⟨true,u⟩ ctx.tys output),
 (Solidity.Source.execS glob frame (fuel+2) nps ph
  (.forLoop (l := l) (Solidity.Source.RStmt.ret (E := ctx.env) (R := []) (M := modifier) (k := ⟨true,u⟩) (Γ := ctx.tys) rfl) condition post body) state.clean).run
  (Solidity.Source.L0 ctx.env,state.world) =
  (.error (.stuck "for initializer"),(Solidity.Source.L0 ctx.env,state.world)) := by
  intro ctx modifier l u glob frame fuel nps ph state output condition post body
  rfl

end Solidity.Yul.RawSourceReturnControl
