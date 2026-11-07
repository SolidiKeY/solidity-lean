import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

namespace H28.PushOrderSwappedKill
open Solidity

def arrayName : Name := String.singleton 'a'
def C : Contract := { vars := [(arrayName, .ref (.array (.prim .uint)))] }
def path : SPath C [] (.array (.prim .uint)) := .loc (.root arrayName rfl)
def empty : State C [] := .init C
def populated : State C [] := empty.withStorage (.cons (.array
  (.cons (.prim ⟨7, rfl⟩) .nil) .nil (by decide +kernel)) .nil)
def statement : Stmt C [] [] := .pushOpAssign .add rfl rfl path (.simple (.lit 1 rfl))
def extendUpdate : Upd C [] [] := .snoc .nil (.storage (.app2 .pushSlot (.app0 .storage) path.lower))
def lastIndex : Tm C [] (.val .uint) := Tms.Term.binop .sub .uint
  (Tms.Term.lenH rfl Tms.STerm.storage path.lower) (Tms.Term.nat 1 rfl) rfl
def lastPath : Tm C [] (.path (.prim .uint)) := Tms.PTerm.at (.arr .dyn) path.lower lastIndex
def added : Tm C [] (.val .uint) := Tms.Term.binopC .add rfl rfl
  (Tms.Term.find Tms.STerm.storage lastPath) (.app0 (.lit (p := .uint) ⟨1, rfl⟩))
def writeUpdate : Upd C [] [] := .snoc .nil (.storage
  (Tms.STerm.save Tms.STerm.storage lastPath (Tms.SValT.val added)))
def first : Upd C [] [] := writeUpdate
def second : Upd C [] [] := extendUpdate
def premise : Premise C [] [] := .updates first second

theorem source_link : Taclet C 0 .box statement premise := .storagePushAddAssign (hp := rfl) (sp := path) (se := .lit 1 rfl) (hlen := rfl) rfl

def afterEmpty : State C [] := empty.withStorage (.cons (.array
  (.cons (.prim ⟨1, rfl⟩) .nil) .nil (by decide +kernel)) .nil)
def afterPopulated : State C [] := empty.withStorage (.cons (.array
  (.cons (.prim ⟨7, rfl⟩) (.cons (.prim ⟨1, rfl⟩) .nil)) .nil (by decide +kernel)) .nil)
def afterWritten : State C [] := empty.withStorage (.cons (.array
  (.cons (.prim ⟨8, rfl⟩) .nil) .nil (by decide +kernel)) .nil)
def afterSwapped : State C [] := empty.withStorage (.cons (.array
  (.cons (.prim ⟨8, rfl⟩) (.cons (.prim ⟨0, rfl⟩) .nil)) .nil (by decide +kernel)) .nil)

theorem input_inhabited : Nonempty (State C []) := ⟨empty⟩
theorem empty_run : statement.runR empty = .ok ⟨afterEmpty, List.prefix_refl _⟩ := by with_unfolding_all rfl
theorem populated_run : statement.runR populated = .ok ⟨afterPopulated, List.prefix_refl _⟩ := by with_unfolding_all rfl

theorem first_fails_empty : first.globT empty = none := by with_unfolding_all rfl
theorem first_not_exhausted : first.exh empty = false := by with_unfolding_all rfl

theorem first_landing : first.Lands populated afterWritten.globG afterWritten := by
  apply Upd.lands_iff_applyV.mpr
  refine ⟨afterWritten.locV, ?_, ?_, ?_⟩
  · with_unfolding_all rfl
  · rfl
  · intro t i
    nomatch i

theorem second_landing : second.Lands afterWritten afterSwapped.globG afterSwapped := by
  apply Upd.lands_iff_applyV.mpr
  refine ⟨afterSwapped.locV, ?_, ?_, ?_⟩
  · with_unfolding_all rfl
  · rfl
  · intro t i
    nomatch i

theorem typed_landing : first.Lands populated afterWritten.globG afterWritten ∧
    second.Lands afterWritten afterSwapped.globG afterSwapped :=
  ⟨first_landing, second_landing⟩

theorem premise_accepts_false : holds empty (premise.fml .box .nil .nil .ff) := by
  change first.afterT .box empty (fun τ => second.afterT .box τ (fun _ => ¬ True))
  apply Upd.afterT_intro
  · intro _
    trivial
  · intro g τ h
    have he := h.1
    rw [first_fails_empty] at he
    cases he

theorem real_frames : Prog.runFrames empty (.cons statement .nil) .nil = .ok afterEmpty := by with_unfolding_all rfl

theorem execution_rejects_false : ¬ holds empty (.modal .box (.cons statement .nil) .nil .ff) := by
  change ¬ Modality.afterRunTR .box (fun τ => holds τ .ff) (Prog.runFrames empty (.cons statement .nil) .nil)
  rw [real_frames]
  intro h
  exact h.1 trivial

theorem checked_kill : ¬ Premise.Sound .box statement premise empty := by
  intro h
  exact execution_rejects_false (h .nil .nil .ff premise_accepts_false)

#print axioms source_link
#print axioms input_inhabited
#print axioms empty_run
#print axioms populated_run
#print axioms first_fails_empty
#print axioms first_not_exhausted
#print axioms first_landing
#print axioms second_landing
#print axioms typed_landing
#print axioms premise_accepts_false
#print axioms real_frames
#print axioms execution_rejects_false
#print axioms checked_kill
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @empty_run
#check @populated_run
#check @first_fails_empty
#check @first_not_exhausted
#check @first_landing
#check @second_landing
#check @typed_landing
#check @premise_accepts_false
#check @real_frames
#check @execution_rejects_false
#check @checked_kill
end H28.PushOrderSwappedKill
