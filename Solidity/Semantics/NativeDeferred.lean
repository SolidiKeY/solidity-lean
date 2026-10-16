import Solidity.Semantics.DeferredSource

/-!
# Native deferred receiver execution

`Stmt.callReceiverPush` retains an operand prefix and the source typed in its
final context. Its ordinary interpreter agrees with the earlier independent
deferred semantics and actual getter/capture/prefix/push program, for arbitrary
typed callees and prefixes. Getter and operand heap extensions compose; caller
writes survive and prefix locals end after the value has been read.

This module supplies ordinary execution agreement. Exact callback capture is in
`Semantics/NativeDeferredCallback.lean`; the ordinary and callback calculi use
these laws for the upstream receiver-capture taclet. Source elaboration retains
the operand's private prefix until that taclet fires.
-/

namespace Solidity.NativeDeferred

open Solidity.DeferredSource

variable {C : Contract} {Γ : Ctx}

/-- `f().push(i++)`: the native prefix snapshots its result before dropping temporaries. -/
theorem pushAfterPrefix_eq {E : Ty} (e : Operand C Γ E)
    (ref : SRef C (.ref (.array E))) (σ : State C Γ) :
    TRun.pushAfterPrefix e.code.ext e.code.runR e.value ref σ = e.pushAt ref σ := by
  unfold TRun.pushAfterPrefix Operand.pushAt Operand.run
  dsimp only [Prog.run]
  cases hc : e.code.runR σ with
  | error err => rfl
  | ok a =>
    dsimp only [bind, Except.bind]
    cases e.value.valueT a.st <;> rfl

/-- An unset result of `f()` reverts before an effectful push operand runs. -/
theorem afterReceiverPrefix_eq {E : Ty} (e : Operand C Γ E)
    (σ : State C (.alias (.array E) :: Γ)) :
    TRun.afterReceiverPrefix e.code.ext e.code.runR e.value σ = afterReturnedAlias e σ := by
  unfold TRun.afterReceiverPrefix afterReturnedAlias
  simp only [pushAfterPrefix_eq]
  cases hr : SPath.resolveT σ (.alias (.here : Idx _ (.alias (.array E)))) with
  | error err => rfl
  | ok ref =>
    dsimp only [bind, Except.bind]
    have hp : (e.wk (.drop .refl)).pushAt ref σ =
        (e.pushAt ref (σ.drop (.push .refl))).map
          (fun x => ⟨x.st.push (t := .alias (.array E)) σ.env.1, x.ext⟩) :=
      Operand.pushAt_afterAlias e (σ.drop (.push .refl)) σ.env.1 ref
    rw [hp]
    cases e.pushAt ref (σ.drop (.push .refl)) <;> rfl

/-- `f().push(e)` runs its getter once, then the deferred operand in the caller. -/
theorem native_runCall {ps Γf : Ctx} {E : Ty} (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf) (e : Operand C Γ E) (σ : State C Γ) :
    (Stmt.callReceiverPush f args r body e.code e.value).run σ = runCall args r body e σ := by
  change TRun.callReceiverPush args r body.ext body.runR e.code.ext e.code.runR e.value σ = _
  unfold TRun.callReceiverPush runCall
  simp only [afterReceiverPrefix_eq]
  cases TRun.call args (.storage _ r) body.ext body.runR σ with
  | error err => rfl
  | ok a =>
    dsimp only [bind, Except.bind]
    cases afterReturnedAlias e a.st <;> rfl

/-- Expanding `f().push(e)` to two captured aliases preserves its complete typed result. -/
theorem native_capture_run {ps Γf : Ctx} {E : Ty} (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf) (e : Operand C Γ E) (σ : State C Γ) :
    ((callProgram f args r body e).run σ).map (Out.drop (.push (.push .refl))) =
      (Stmt.callReceiverPush f args r body e.code e.value).run σ :=
  (callProgram_sound f args r body e σ).trans (native_runCall f args r body e σ).symm

/-- The taclet's fresh name in `f().push(i++)` has no effect on execution. -/
theorem capture_run {ps Γf Γv : Ctx} {E : Ty} (k : Nat) (f : Name)
    (args : Args C Γ ps) (r : Var) (body : Prog C ([.alias (.array E)] ++ ps) Γf)
    (code : Prog C Γ Γv) (value : Src C Γv E) (σ : State C Γ) :
    ((callReceiverPushCapture k f args r body code value).run σ).map
      (Out.drop (.push (.push .refl))) =
        (Stmt.callReceiverPush f args r body code value).run σ := by
  exact native_capture_run f args r body ⟨Γv, code, value⟩ σ

end Solidity.NativeDeferred
