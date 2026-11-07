import Solidity.Backend.Aggregates.BoolArrayEntry

/-! G18.04/.05 actual typed conversion-expression and scoped argument client.
All budgets below are the existing Source interpreter budget, not EVM gas. -/
namespace Solidity.Backend.Aggregates.BoolArrayExpression
open Solidity BoolArrays BoolArrayEntry

abbrev argumentTy : Source.STy := .array .calldata .bool none

def expr {E : Source.Env} {caller : Source.RCtx} :
    Source.RExpr E (argumentTy :: caller) sourceTy :=
  .conv (.local .here) (.inl rfl)

theorem eval_expr_run {E : Source.Env} {caller : Source.RCtx} (G : Source.Glob E)
    (frame : Source.Fr) (n offset length : Nat) (tail : Source.Locals E.layout caller) (state : Source.St E) :
    let before : Source.EMState E (argumentTy :: caller) :=
      (.cons (.cdRef rfl offset length) tail,state)
    (Source.evalE G frame (n+2) expr).run before =
      (Source.cdToMem frame sourceTy offset length).run before := by
  dsimp only
  unfold expr
  change ((Source.evalE G frame (n+1) (.local .here)) >>= fun argument =>
    Source.convRV frame (n+1) sourceTy argument).run _ = _
  rw [Source.Hoare.run_bind,Source.eval_local_run]
  change (Source.convRV frame (n+1) sourceTy
    (.val (.cdRef (τ := argumentTy) rfl offset length))).run _ = _
  rw [Source.convRV_cdArray]

theorem eval_expr_zero {E : Source.Env} {caller : Source.RCtx} (G : Source.Glob E)
    (frame : Source.Fr) (before : Source.EMState E (argumentTy :: caller)) :
    (Source.evalE G frame 0 expr).run before = (.error .timeout,before) := rfl

theorem eval_expr_one {E : Source.Env} {caller : Source.RCtx} (G : Source.Glob E)
    (frame : Source.Fr) (before : Source.EMState E (argumentTy :: caller)) :
    (Source.evalE G frame 1 expr).run before = (.error .timeout,before) := rfl

/-- Decode an actual argument, bind it in a typed local extension, evaluate
existing RExpr.conv, then drop only that extension with actual EM.sub. -/
def scopedCopy {E : Source.Env} {caller : Source.RCtx} (G : Source.Glob E)
    (frame : Source.Fr) (budget : Nat) (data : Roadmap.Bytes) (index : Nat) :
    Source.EM E caller (Source.RVal E.layout sourceTy) := do
  let argument ← Source.decodeArg data index argumentTy
  let tail ← Source.EM.locals
  let (result,_) ← Source.EM.sub (.cons argument tail) (Source.evalE G frame budget expr)
  pure result

/-- Complete scoped-expression transport to the real decoder/converter
client; actual extended locals are dropped on both success and error. -/
theorem scopedCopy_run {E : Source.Env} {caller : Source.RCtx} (G : Source.Glob E)
    (frame : Source.Fr) (n : Nat) (data : Roadmap.Bytes) (index : Nat)
    (source : Source.EMState E caller) :
    (scopedCopy G frame (n+2) data index).run source =
      (sourceCopy frame data index).run source := by
  rcases source with ⟨tail,state⟩
  rw [sourceCopy_run]
  unfold scopedCopy
  rw [Source.Hoare.run_bind,Source.decodeArg_cdArray_run data index .bool rfl,
    Source.cdHeadBytes_of_word (τ := .bool) rfl]
  unfold Source.cdArg
  cases entry : Source.cdTail data index 32 with
  | error halt => rfl
  | ok pair =>
    rcases pair with ⟨offset,length⟩
    change ((Source.EM.sub (.cons (.cdRef (τ := argumentTy) rfl offset length) tail)
      (Source.evalE G frame (n+2) expr)) >>= fun result => pure result.1).run (tail,state) = _
    rw [Source.Hoare.run_bind]
    unfold Source.EM.sub
    dsimp only [ExceptT.run,ExceptT.mk]
    have evaluation := eval_expr_run G frame n offset length tail state
    dsimp only [ExceptT.run,ExceptT.mk] at evaluation
    rw [evaluation]
    have inside := Source.cdToMem_array_run frame .bool offset length
      ((.cons (.cdRef (τ := argumentTy) rfl offset length) tail,state) : Source.EMState E (argumentTy :: caller))
    have outside := Source.cdToMem_array_run frame .bool offset length ((tail,state) : Source.EMState E caller)
    dsimp only [ExceptT.run,ExceptT.mk] at inside outside
    rw [inside,outside]
    cases (List.range length).mapM (fun j =>
      Source.decodeWord E.layout (Source.cdWordAt frame (offset+32*j)) .bool) <;> rfl

/-- Actual low-budget ordering: argument entry errors precede expression
exhaustion; a successful entry reaches timeout without validating elements
or allocating memory. No exhausted case is hidden by a fuel premise. -/
theorem scopedCopy_low_run {E : Source.Env} {caller : Source.RCtx} (G : Source.Glob E)
    (frame : Source.Fr) (budget : Nat) (small : budget ≤ 1) (data : Roadmap.Bytes) (index : Nat)
    (source : Source.EMState E caller) :
    (scopedCopy G frame budget data index).run source =
      match Source.cdTail data index 32 with
      | .error halt => (.error halt,source)
      | .ok _ => (.error .timeout,source) := by
  rcases source with ⟨tail,state⟩
  unfold scopedCopy
  rw [Source.Hoare.run_bind,Source.decodeArg_cdArray_run data index .bool rfl,
    Source.cdHeadBytes_of_word (τ := .bool) rfl]
  unfold Source.cdArg
  cases Source.cdTail data index 32 with
  | error halt => rfl
  | ok pair =>
    rcases pair with ⟨offset,length⟩
    cases budget with
    | zero => rfl
    | succ budget =>
      have zero : budget = 0 := by omega
      subst budget
      rfl

/-- The value/frame phase agrees with actual scoped typed expression errors
when that expression has its exact two-layer minimum. This is not a gas or
machine-failure theorem; low budgets are covered separately above. -/
theorem scoped_error_iff {E : Source.Env} {caller : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (n : Nat) (source : Source.EMState E caller) (target : State C Γ)
    (frame : Source.Fr) (selector data : Roadmap.Bytes) (selector_length : selector.length = 4)
    (input : frame.cd = selector ++ data) (index : Nat) (halt : Source.Halt) :
    lowerEntry (E := E) target frame selector data selector_length input index = .error halt ↔
      (scopedCopy G frame (n+2) data index).run source = (.error halt,source) := by
  rw [scopedCopy_run]
  exact entry_error_iff_source_error source target frame selector data selector_length input index halt

end Solidity.Backend.Aggregates.BoolArrayExpression
