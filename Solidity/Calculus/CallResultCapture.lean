import Solidity.Calculus.LeafShare
import Solidity.Calculus.TermSize

/-! # Capturing a complete primitive call result

The complete result term occurs once, in a fresh intrinsic declaration.
The continuation copies its head value into an old target and pops the head.
These local transport laws do not claim compression of an expanded call family.
-/
namespace Solidity.CallResultCapture
variable {C : Contract} {Γ : Ctx} {p : PrimTy}

/-- Evaluate the result before introducing its fresh positional name. -/
def capture (name : Var) (t : Tm C Γ (.val p)) : Upd C Γ (.val p :: Γ) :=
  Upd.nil.decl name (.val t)

/-- Copy the fresh result into an old target, then restore the old context. -/
def restore (j : Idx Γ (.val p)) : Upd C (.val p :: Γ) Γ :=
  (Upd.nil.snoc (.local j.there (.val (.pvV .here)))).pop (.push .refl)

/-- The old-context postcondition is never weakened or substituted. -/
def leaf (m : Modality) (name : Var) (j : Idx Γ (.val p))
    (t : Tm C Γ (.val p)) (φ : Fml C Γ) : Fml C Γ :=
  .upd m (capture name t) (.upd m (restore j) φ)

/-- The complete result is evaluated exactly once by the capture update. -/
theorem capture_applyV (name : Var) (t : Tm C Γ (.val p)) (σ : State C Γ) :
    (capture name t).applyV σ =
      (t.eval σ).bind (fun v => some (σ.globG, σ.locV.push v)) := rfl

/-- Dropping a fresh head after an old-target write preserves every old local. -/
theorem restore_locals (σ : State C Γ) (v : p.Denote) (j : Idx Γ (.val p)) :
    (((σ.push (t := .val p) v).locV.set j.there v).drop (.push .refl)) =
      σ.locV.set j v := by
  funext u i
  change (σ.push (t := .val p) v).locV.set j.there v u i.there = σ.locV.set j v u i
  by_cases hj : j.toNat = i.toNat
  · obtain rfl := Idx.ty_eq_of_toNat hj
    obtain rfl := Idx.toNat_inj j i hj
    rw [LocsV.set_same, LocsV.set_same]
  · rw [LocsV.set_ne _ _ _ (by show j.toNat + 1 ≠ i.toNat + 1; omega),
      LocsV.set_ne _ _ _ hj]
    rfl

/-- Exact state restoration retains the heap and all global observations. -/
theorem restore_state (σ : State C Γ) (v : p.Denote) (j : Idx Γ (.val p)) :
    ((σ.push (t := .val p) v).setLocal j.there v).drop (.push .refl) =
      σ.setLocal j v := rfl

/-- An old target cannot alias the fresh result slot, even at the same type. -/
theorem target_fresh (j : Idx Γ (.val p)) :
    j.there ≠ (.here : Idx (.val p :: Γ) (.val p)) := by
  intro h
  cases h

/-- A successful capture restores the same typed globals and old locals as
assigning the result directly; the fresh slot cannot escape. -/
theorem restore_applyV (σ : State C Γ) (v : p.Denote) (j : Idx Γ (.val p)) :
    (restore j).applyV (σ.push (t := .val p) v) =
      some (σ.globG, σ.locV.set j v) := by
  change some ((σ.push (t := .val p) v).globG,
    ((σ.push (t := .val p) v).locV.set j.there v).drop (.push .refl)) = _
  rw [restore_locals]
  rfl

/-- Capture and direct assignment retain the identical exhaustion predicate. -/
theorem capture_exh (name : Var) (t : Tm C Γ (.val p))
    (j : Idx Γ (.val p)) (σ : State C Γ) :
    (capture name t).exh σ = (Upd.nil.snoc (.local j (.val t))).exh σ := rfl

/-- Whole-result capture is sound for both modalities, including failure and
exhaustion, without a push-free or totality premise. -/
theorem sound {m : Modality} (name : Var) (j : Idx Γ (.val p))
    (t : Tm C Γ (.val p)) (φ : Fml C Γ) (σ : State C Γ)
    (hh : holds σ (leaf m name j t φ)) :
    holds σ (.upd m (Upd.nil.snoc (.local j (.val t))) φ) := by
  change Upd.afterT m σ (capture name t)
    (fun τ => Upd.afterT m τ (restore j) (holds · φ)) at hh
  change Upd.afterT m σ _ (holds · φ)
  rw [Upd.afterT_applyV] at hh ⊢
  rw [capture_applyV] at hh
  have e : (Upd.nil.snoc (.local j (.val t))).applyV σ =
      (t.eval σ).bind (fun v => some (σ.globG, σ.locV.set j v)) := rfl
  rw [e]
  cases ht : t.eval σ with
  | none =>
    rw [ht] at hh
    rw [← capture_exh name t j σ]
    exact hh
  | some v =>
    rw [ht] at hh
    have hτ : Upd.afterT m (σ.push (t := .val p) v) (restore j) (holds · φ) :=
      hh (σ.push (t := .val p) v) rfl (fun i => by
        show (σ.push (t := .val p) v).locV _ i = _
        rw [State.locV_push]
        rfl)
    rw [Upd.afterT_applyV, restore_applyV] at hτ
    exact hτ

/-- Direct assignment also establishes its captured form. Arbitrary typed
intermediate states are transported by globals and every indexed local. -/
theorem complete {m : Modality} (name : Var) (j : Idx Γ (.val p))
    (t : Tm C Γ (.val p)) (φ : Fml C Γ) (σ : State C Γ)
    (hh : holds σ (.upd m (Upd.nil.snoc (.local j (.val t))) φ)) :
    holds σ (leaf m name j t φ) := by
  change Upd.afterT m σ _ (holds · φ) at hh
  change Upd.afterT m σ (capture name t)
    (fun τ => Upd.afterT m τ (restore j) (holds · φ))
  rw [Upd.afterT_applyV] at hh ⊢
  rw [capture_applyV]
  have e : (Upd.nil.snoc (.local j (.val t))).applyV σ =
      (t.eval σ).bind (fun v => some (σ.globG, σ.locV.set j v)) := rfl
  rw [e] at hh
  cases ht : t.eval σ with
  | none =>
    rw [ht] at hh
    rw [capture_exh name t j σ]
    exact hh
  | some v =>
    rw [ht] at hh
    intro τ hg hl
    rw [Upd.afterT_applyV]
    have hv : τ.getV (.here : Idx (.val p :: Γ) (.val p)) = v := hl .here
    have hl' : τ.locV = σ.locV.push v := by
      funext u i
      exact hl i
    have er : (restore j).applyV τ = some (τ.globG, σ.locV.set j v) := by
      change some (τ.globG,
        (τ.locV.set j.there (τ.getV .here)).drop (.push .refl)) = _
      have ep : (σ.push (t := .val p) v).locV = σ.locV.push v :=
        State.locV_push (t := .val p) σ v
      rw [hv, hl', ← ep, restore_locals]
    rw [er]
    intro υ hglob hlocals
    exact hh υ (hglob.trans hg) hlocals

/-- Exact observable equivalence, for every postcondition and both modalities. -/
theorem holds_iff (m : Modality) (name : Var) (j : Idx Γ (.val p))
    (t : Tm C Γ (.val p)) (φ : Fml C Γ) (σ : State C Γ) :
    holds σ (leaf m name j t φ) ↔
      holds σ (.upd m (Upd.nil.snoc (.local j (.val t))) φ) :=
  ⟨sound name j t φ σ, complete name j t φ σ⟩

/-- Structural syntax count includes both updates, the declaration, copy and pop.
It counts the result term once; it does not bound the size of that term. -/
theorem leaf_size (m : Modality) (name : Var) (j : Idx Γ (.val p))
    (t : Tm C Γ (.val p)) (φ : Fml C Γ) :
    (leaf m name j t φ).tmSize = t.size + φ.tmSize + 5 := by
  simp only [leaf, capture, restore, Fml.tmSize, Upd.tmSize, UpdElem.size, Rhs.size, Tm.size]
  omega

end Solidity.CallResultCapture
