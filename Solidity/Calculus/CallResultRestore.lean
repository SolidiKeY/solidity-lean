import Solidity.Calculus.CallResultCapture

/-! # Restoring a caller after fresh logical call locals
Copy a returning primitive value to an old target and drop an arbitrary
fresh prefix. Contexts, values, states and updates remain intrinsic.
-/
namespace Solidity.CallResultRestore
variable {C : Contract} {Γ Δ : Ctx} {p : PrimTy}

/-- One copy followed by the existing typed bulk scope end. -/
def copyDrop (h : Ext Γ Δ) (j : Idx Γ (.val p)) (r : Idx Δ (.val p)) : Upd C Δ Γ :=
  (Upd.nil.snoc (.local (j.ext h) (.val (.pvV r)))).pop h

/-- Every old local is transported through an arbitrary fresh context prefix. -/
theorem env_drop_set {H : HTy} {t : LTy} (h : Ext Γ Δ) (j : Idx Γ t)
    (v : t.TDenote C H) (e : TEnv C H Δ) :
    TEnv.drop h (TEnv.set (j.ext h) v e) = TEnv.set j v (TEnv.drop h e) := by
  induction h with
  | refl => rfl
  | push h ih => exact ih e.2

/-- The exact typed state, including every global and the heap, is restored. -/
theorem state_drop_set (h : Ext Γ Δ) (j : Idx Γ (.val p))
    (v : p.Denote) (τ : State C Δ) :
    (τ.setLocal (j.ext h) v).drop h = (τ.drop h).setLocal j v := by
  simp only [State.drop, State.setLocal, env_drop_set]

/-- Virtual locals agree with the exact state restoration. -/
theorem locals_drop_set (h : Ext Γ Δ) (j : Idx Γ (.val p))
    (v : p.Denote) (τ : State C Δ) :
    (τ.locV.set (j.ext h) v).drop h = (τ.locV.drop h).set j v := by
  have hs : (τ.setLocal (j.ext h) v).drop h = (τ.drop h).setLocal j v :=
    state_drop_set h j v τ
  have hl : ((τ.setLocal (j.ext h) v).drop h).locV =
      ((τ.drop h).setLocal j v).locV := congrArg State.locV hs
  simpa only [State.locV_drop, State.locV_setLocal] using hl

/-- The actual returning value is copied once; all fresh locals are removed. -/
theorem copyDrop_applyV (h : Ext Γ Δ) (j : Idx Γ (.val p))
    (r : Idx Δ (.val p)) (τ : State C Δ) :
    (copyDrop h j r).applyV τ =
      some (τ.globG, (τ.locV.drop h).set j (τ.getV r)) := by
  change some (τ.globG, (τ.locV.set (j.ext h) (τ.getV r)).drop h) = _
  rw [locals_drop_set]

/-- Exact postcondition transport for both modalities, without an extra
validity, totality or heap premise. -/
theorem holds_copyDrop (m : Modality) (h : Ext Γ Δ) (j : Idx Γ (.val p))
    (r : Idx Δ (.val p)) (φ : Fml C Γ) (τ : State C Δ) :
    holds τ (.upd m (copyDrop h j r) φ) ↔
      holds ((τ.drop h).setLocal j (τ.getV r)) φ := by
  change Upd.afterT m τ (copyDrop h j r) (holds · φ) ↔ _
  rw [Upd.afterT_applyV, copyDrop_applyV]
  constructor
  · intro hp
    apply hp ((τ.drop h).setLocal j (τ.getV r)) rfl
    intro u i
    show ((τ.drop h).setLocal j (τ.getV r)).locV u i = _
    rw [State.locV_setLocal, State.locV_drop]
    rfl
  · intro hp υ hg hl
    have he : υ = (τ.drop h).setLocal j (τ.getV r) := by
      apply State.eq_of_readsAs
      refine ⟨hg, ?_⟩
      intro u i
      show υ.locV u i = ((τ.drop h).setLocal j (τ.getV r)).locV u i
      rw [State.locV_setLocal, State.locV_drop]
      exact hl i
    rw [he]
    exact hp

/-- The local copy and scope end introduce no exhaustion. -/
theorem copyDrop_exh (h : Ext Γ Δ) (j : Idx Γ (.val p))
    (r : Idx Δ (.val p)) (τ : State C Δ) : (copyDrop h j r).exh τ = false := rfl

/-- Evaluate once in the extended context, then restore the exact caller. -/
def leaf (m : Modality) (name : Var) (h : Ext Γ Δ) (j : Idx Γ (.val p))
    (t : Tm C Δ (.val p)) (φ : Fml C Γ) : Fml C Δ :=
  .upd m (CallResultCapture.capture name t)
    (.upd m (copyDrop (.push h) j .here) φ)

/-- The actual returned value flows from capture into the caller update.
The premise is the checked evaluation fact for this branch. -/
theorem holds_leaf_of_eval (m : Modality) (name : Var) (h : Ext Γ Δ)
    (j : Idx Γ (.val p)) (t : Tm C Δ (.val p)) (φ : Fml C Γ)
    (τ : State C Δ) (v : p.Denote) (ht : t.eval τ = some v) :
    holds τ (leaf m name h j t φ) ↔ holds ((τ.drop h).setLocal j v) φ := by
  change Upd.afterT m τ (CallResultCapture.capture name t)
    (fun υ => holds υ (.upd m (copyDrop (.push h) j .here) φ)) ↔ _
  rw [Upd.afterT_applyV, CallResultCapture.capture_applyV, ht]
  constructor
  · intro hp
    have hc : holds (τ.push (t := .val p) v) (.upd m (copyDrop (.push h) j .here) φ) :=
      hp (τ.push (t := .val p) v) rfl (fun {u} i => by
        show (τ.push (t := .val p) v).locV u i = _
        rw [State.locV_push]
        rfl)
    rw [holds_copyDrop] at hc
    exact hc
  · intro hp υ hg hl
    have he : υ = τ.push (t := .val p) v := by
      apply State.eq_of_readsAs
      refine ⟨hg, ?_⟩
      intro u i
      show υ.locV u i = (τ.push (t := .val p) v).locV u i
      rw [State.locV_push]
      exact hl i
    rw [he, holds_copyDrop]
    exact hp

/-- Nonreturn retains the exact old modality/exhaustion condition. -/
theorem holds_leaf_of_none (m : Modality) (name : Var) (h : Ext Γ Δ)
    (j : Idx Γ (.val p)) (t : Tm C Δ (.val p)) (φ : Fml C Γ)
    (τ : State C Δ) (ht : t.eval τ = none) :
    holds τ (leaf m name h j t φ) ↔
      (m.onHalt ∨ (CallResultCapture.capture name t).exh τ = true) := by
  change Upd.afterT m τ (CallResultCapture.capture name t) _ ↔ _
  rw [Upd.afterT_applyV, CallResultCapture.capture_applyV, ht]
  rfl

/-- The full capture/copy/drop formula contains t once, plus five nodes. -/
theorem leaf_size (m : Modality) (name : Var) (h : Ext Γ Δ) (j : Idx Γ (.val p))
    (t : Tm C Δ (.val p)) (φ : Fml C Γ) :
    (leaf m name h j t φ).tmSize = t.size + φ.tmSize + 5 := by
  simp only [leaf, CallResultCapture.capture, copyDrop, Fml.tmSize, Upd.tmSize,
    UpdElem.size, Rhs.size, Tm.size]
  omega

/-- Even after arbitrary logical locals, the old target is apart from
an additionally pushed result head, regardless of display names. -/
theorem target_fresh (h : Ext Γ Δ) (j : Idx Γ (.val p)) :
    (j.ext h).there ≠ (.here : Idx (.val p :: Δ) (.val p)) := by
  intro he
  cases he

/-- The update contains its one read/copy and one typed scope end. -/
theorem copyDrop_size (h : Ext Γ Δ) (j : Idx Γ (.val p)) (r : Idx Δ (.val p)) :
    (copyDrop (C := C) h j r).tmSize = 2 := rfl

end Solidity.CallResultRestore
