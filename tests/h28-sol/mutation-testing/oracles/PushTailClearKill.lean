import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

namespace H28.PushTailClearKill
open Solidity

def arrayName : Name := String.singleton 'a'
def E : Ty := .ref (.array (.prim .uint))
def C : Contract := { vars := [(arrayName, .ref (.array E))] }
def path : SPath C [] (.array E) := .loc (.root arrayName rfl)
def clean : State C [] := .init C
def dirty : State C [] := clean.withStorage (.cons (.array .nil
  (.cons (.array (.cons (.prim ⟨7, rfl⟩) .nil) .nil (by decide +kernel)) .nil)
  (by decide +kernel)) .nil)
def σ (b : Bool) : State C [] := if b then dirty else clean
def statement : Stmt C [] [] := .push path none rfl

def afterClean : State C [] := clean.withStorage (.cons (.array
  (.cons (.array .nil .nil (by decide +kernel)) .nil) .nil (by decide +kernel)) .nil)
def afterActual : State C [] := clean.withStorage (.cons (.array
  (.cons (.array (.cons (.prim ⟨7, rfl⟩) .nil) .nil (by decide +kernel)) .nil)
  .nil (by decide +kernel)) .nil)
def afterCleared : State C [] := clean.withStorage (.cons (.array
  (.cons (.array .nil (.cons (.prim ⟨0, rfl⟩) .nil) (by decide +kernel)) .nil)
  .nil (by decide +kernel)) .nil)

def nextPath : Tm C [] (.path E) := .app1 .next path.lower
def pushed : Tm C [] .st := .app2 .pushSlot (.app0 .storage) path.lower
def update : Upd C [] [] := .snoc .nil (.storage (.app2 .delAt pushed nextPath))
def premise : Premise C [] [] := .update update

theorem source_link : Taclet C 0 .diamond statement premise := .storagePushLengthSaveReferenceElement (rarr := path) (hd := rfl) rfl rfl rfl

def innerPath : Tm C [] (.path E) := .app2 (.at (.arr .dyn)) path.lower (.app0 (.lit (p := .uint) ⟨0, rfl⟩))
def innerLength : Tm C [] (.val .uint) := .app2 .len (.app0 .storage) innerPath
def zero : Tm C [] (.val .uint) := .app0 (.lit (p := .uint) ⟨0, rfl⟩)
def post : Fml C [] := .eq innerLength zero

theorem input_inhabited : ∀ _b : Bool, Nonempty (State C []) := fun b => ⟨σ b⟩
theorem clean_run : statement.runR clean = .ok ⟨afterClean, List.prefix_refl _⟩ := by with_unfolding_all rfl
theorem dirty_run : statement.runR dirty = .ok ⟨afterActual, List.prefix_refl _⟩ := by with_unfolding_all rfl

theorem actual_inner_length : innerLength.denote afterActual = some (⟨1, rfl⟩ : PrimTy.uint.Denote) :=
  Tm.denote_eval afterActual innerLength ⟨1, rfl⟩ (by with_unfolding_all rfl)

theorem clean_post : holds afterClean post := by
  change innerLength.denote afterClean = zero.denote afterClean
  have h : innerLength.denote afterClean = some (⟨0, rfl⟩ : PrimTy.uint.Denote) :=
    Tm.denote_eval afterClean innerLength ⟨0, rfl⟩ (by with_unfolding_all rfl)
  rw [h]
  rfl

theorem actual_rejects_post : ¬ holds afterActual post := by
  intro h
  change innerLength.denote afterActual = zero.denote afterActual at h
  rw [actual_inner_length] at h
  change (some (⟨1, rfl⟩ : PrimTy.uint.Denote)) = some ⟨0, rfl⟩ at h
  have hn : (some (⟨1, rfl⟩ : PrimTy.uint.Denote)) ≠ some ⟨0, rfl⟩ := by decide +kernel
  exact hn h

theorem update_returns : update.globT dirty = some afterCleared.globG := by with_unfolding_all rfl

theorem typed_landing : update.Lands dirty afterCleared.globG afterCleared := by
  apply Upd.lands_iff_applyV.mpr
  refine ⟨afterCleared.locV, ?_, ?_, ?_⟩
  · with_unfolding_all rfl
  · rfl
  · intro t i
    nomatch i

theorem clean_update_returns : update.globT clean = some afterClean.globG := by with_unfolding_all rfl

theorem cleared_post : holds afterCleared post := by
  change innerLength.denote afterCleared = zero.denote afterCleared
  have h : innerLength.denote afterCleared = some (⟨0, rfl⟩ : PrimTy.uint.Denote) :=
    Tm.denote_eval afterCleared innerLength ⟨0, rfl⟩ (by with_unfolding_all rfl)
  rw [h]
  rfl

theorem premise_accepts_post : holds dirty (premise.fml .diamond .nil .nil post) := by
  change update.afterT .diamond dirty (fun τ => holds τ post)
  apply Upd.afterT_intro
  · intro h
    rw [update_returns] at h
    cases h
  · intro g τ h
    have he : τ = afterCleared := h.eq typed_landing
    subst τ
    exact cleared_post

theorem real_frames : Prog.runFrames dirty (.cons statement .nil) .nil = .ok afterActual := by with_unfolding_all rfl

theorem execution_rejects_post : ¬ holds dirty (.modal .diamond (.cons statement .nil) .nil post) := by
  change ¬ Modality.afterRunTR .diamond (fun τ => holds τ post) (Prog.runFrames dirty (.cons statement .nil) .nil)
  rw [real_frames]
  intro h
  exact actual_rejects_post h.1

theorem checked_kill : ¬ Premise.Sound .diamond statement premise dirty := by
  intro h
  exact execution_rejects_post (h .nil .nil post premise_accepts_post)

#print axioms source_link
#print axioms input_inhabited
#print axioms clean_run
#print axioms dirty_run
#print axioms actual_inner_length
#print axioms clean_post
#print axioms actual_rejects_post
#print axioms update_returns
#print axioms typed_landing
#print axioms clean_update_returns
#print axioms cleared_post
#print axioms premise_accepts_post
#print axioms real_frames
#print axioms execution_rejects_post
#print axioms checked_kill
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @clean_run
#check @dirty_run
#check @actual_inner_length
#check @clean_post
#check @actual_rejects_post
#check @update_returns
#check @typed_landing
#check @clean_update_returns
#check @cleared_post
#check @premise_accepts_post
#check @real_frames
#check @execution_rejects_post
#check @checked_kill
end H28.PushTailClearKill
