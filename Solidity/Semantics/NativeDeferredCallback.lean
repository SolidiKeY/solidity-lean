import Solidity.Semantics.NativeDeferred
import Solidity.Semantics.DeferredCorrespondence

/-! Native receiver callbacks agree exactly with the explicit capture program. -/

namespace Solidity.NativeDeferred

open Solidity.DeferredSource Solidity.DeferredSource.Callback

variable {C : Contract} {Γ : Ctx} {J : StateInv C}

/-- The native final source of `f().push(e)` is the direct deferred final source. -/
theorem pushPrefix_eq {E : Ty} {H : HTy} (e : Operand C Γ E)
    (ref : SRef C (.array E)) (u : COut C H e.tailCtx) :
    u.pushPrefix e.code.ext e.value ref = finishAt e ref u := by
  cases u <;> rfl

/-- Native `f().push(e)` admits exactly the independent getter-then-operand callback runs. -/
theorem native_direct_iff {ps Γf : Ctx} {E : Ty} {σ : State C Γ}
    (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf) (e : Operand C Γ E)
    {o : COut C σ.H Γ} :
    ExecS J σ (.callReceiverPush f args r body e.code e.value) o ↔
      DirectCall J σ f args r body e o := by
  constructor
  · intro h
    cases h with
    | det hf => cases hf
    | callReceiverPush hc hp hu =>
      exact .next hc (by
        simp only [DirectAfterGetter, hp]
        exact ⟨_, hu, pushPrefix_eq e _ _⟩)
    | callReceiverPushUnset hc hp =>
      exact DirectCall.next (o := .halt .revert) hc (by
        simp only [DirectAfterGetter, hp])
    | callReceiverPushHalt hc => exact .halt hc
    | callReceiverPushViolated hc => exact .violated hc
  · intro h
    cases h with
    | @next a u hc hp =>
      cases hr : a.st.env.1 with
      | none =>
        simp only [DirectAfterGetter, hr] at hp
        cases hp
        exact .callReceiverPushUnset hc hr
      | some ref =>
        simp only [DirectAfterGetter, hr] at hp
        obtain ⟨v, hv, rfl⟩ := hp
        simpa only [pushPrefix_eq] using
          (ExecS.callReceiverPush (code := e.code) (value := e.value) hc hr hv)
    | halt hc => exact .callReceiverPushHalt hc
    | violated hc => exact .callReceiverPushViolated hc

/-- The complete capture program of `f().push(e)` has exactly the native callback outcomes. -/
theorem native_capture_iff {ps Γf : Ctx} {E : Ty} {σ : State C Γ}
    (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf) (e : Operand C Γ E)
    {o : COut C σ.H Γ} :
    (∃ u, ExecP J σ (callProgram f args r body e) u ∧
      o = u.map (Out.drop (.push (.push .refl)))) ↔
        ExecS J σ (.callReceiverPush f args r body e.code e.value) o :=
  (callProgram_direct_iff f args r body e).trans (native_direct_iff f args r body e).symm

/-- Renaming the fresh `sp` in a receiver capture preserves its callback executions. -/
theorem declStorage_name_iff {R : RefTy} (σ : State C Γ) (x y : Var)
    (init : Option (ARhs C Γ R)) {o : COut C σ.H (.alias R :: Γ)} :
    ExecS J σ (.declStorage R x init) o ↔ ExecS J σ (.declStorage R y init) o := by
  constructor <;> intro h <;> cases h <;> exact .det rfl

/-- Equivalent heads and tails preserve the executions of `s; tail`. -/
theorem cons_congr {Γ₁ Γ₂ : Ctx} {σ : State C Γ} {s t : Stmt C Γ Γ₁}
    {P Q : Prog C Γ₁ Γ₂}
    (hs : ∀ o, ExecS J σ s o ↔ ExecS J σ t o)
    (hP : ∀ (τ : State C Γ₁) o, ExecP J τ P o ↔ ExecP J τ Q o)
    {o : COut C σ.H Γ₂} : ExecP J σ (.cons s P) o ↔ ExecP J σ (.cons t Q) o := by
  constructor
  · intro h
    cases h with
    | cons a b => exact .cons ((hs _).mp a) ((hP _ _).mp b)
    | halt a => exact .halt ((hs _).mp a)
    | violated a => exact .violated ((hs _).mp a)
  · intro h
    cases h with
    | cons a b => exact .cons ((hs _).mpr a) ((hP _ _).mpr b)
    | halt a => exact .halt ((hs _).mpr a)
    | violated a => exact .violated ((hs _).mpr a)

/-- The actual taclet's fresh name in `f().push(e)` preserves exact callback outcomes. -/
theorem capture_iff {ps Γf Γv : Ctx} {E : Ty} {σ : State C Γ}
    (k : Nat) (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf)
    (code : Prog C Γ Γv) (value : Src C Γv E) {o : COut C σ.H Γ} :
    (∃ u, ExecP J σ (callReceiverPushCapture k f args r body code value) u ∧
      o = u.map (Out.drop (.push (.push .refl)))) ↔
        ExecS J σ (.callReceiverPush f args r body code value) o := by
  have hn : ∀ u, ExecP J σ (callReceiverPushCapture k f args r body code value) u ↔
      ExecP J σ (callProgram f args r body ⟨Γv, code, value⟩) u := by
    intro u
    apply cons_congr (fun _ => Iff.rfl)
    intro τ v
    exact cons_congr (fun _ => declStorage_name_iff τ _ _ _) (fun _ _ => Iff.rfl)
  constructor
  · intro ⟨u, hu, ho⟩
    exact (native_capture_iff f args r body ⟨Γv, code, value⟩).mp ⟨u, (hn u).mp hu, ho⟩
  · intro h
    obtain ⟨u, hu, ho⟩ := (native_capture_iff f args r body ⟨Γv, code, value⟩).mpr h
    exact ⟨u, (hn u).mpr hu, ho⟩

end Solidity.NativeDeferred
