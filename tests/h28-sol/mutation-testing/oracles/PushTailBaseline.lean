import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

namespace H28.PushTailBaseline
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
def update : Upd C [] [] := .snoc .nil (.storage pushed)
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

#print axioms source_link
#print axioms input_inhabited
#print axioms clean_run
#print axioms dirty_run
#print axioms actual_inner_length
#print axioms clean_post
#print axioms actual_rejects_post
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @clean_run
#check @dirty_run
#check @actual_inner_length
#check @clean_post
#check @actual_rejects_post
end H28.PushTailBaseline
