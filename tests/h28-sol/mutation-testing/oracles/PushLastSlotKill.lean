import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

/-! A checked counterexample to the census mutant
`storagePushAddAssign.last-slot-is-length.1`: `sp.push() += se;` writes the
sum at `sp[sp.length]` instead of the pushed slot `sp[sp.length - 1]`.  From
an empty array, the run pushes and leaves `[1]`; the mutant's second update
writes past the end of the one-slot array, fails, and so its premise under
the box admits even `false`, which the returning run falsifies. -/
namespace H28.PushLastSlotKill
open Solidity

def arrayName : Name := String.singleton 'a'
def C : Contract := { vars := [(arrayName, .ref (.array (.prim .uint)))] }
def path : SPath C [] (.array (.prim .uint)) := .loc (.root arrayName rfl)
def empty : State C [] := .init C
def statement : Stmt C [] [] := .pushOpAssign .add rfl rfl path (.simple (.lit 1 rfl))
def extendUpdate : Upd C [] [] := .snoc .nil (.storage (.app2 .pushSlot (.app0 .storage) path.lower))
def lastIndex : Tm C [] (.val .uint) := Tms.Term.binop .sub .uint
  (Tms.Term.lenH rfl Tms.STerm.storage path.lower) (Tms.Term.nat 1 rfl) rfl
def lastPath : Tm C [] (.path (.prim .uint)) := Tms.PTerm.at (.arr .dyn) path.lower lastIndex
/-- `sp[sp.length]`, as the rule language lowers it: the slot past the end. -/
def pastPath : Tm C [] (.path (.prim .uint)) := Tms.PTerm.next path.lower
def added : Tm C [] (.val .uint) := Tms.Term.binopC .add rfl rfl
  (Tms.Term.find Tms.STerm.storage lastPath) (.app0 (.lit (p := .uint) ⟨1, rfl⟩))
def writeUpdate : Upd C [] [] := .snoc .nil (.storage
  (Tms.STerm.save Tms.STerm.storage pastPath (Tms.SValT.val added)))
def first : Upd C [] [] := extendUpdate
def second : Upd C [] [] := writeUpdate
def mutated : Premise C [] [] := .updates first second

/-- This instance links the witness to the actual mutated production rule. -/
theorem source_link : Taclet C 0 .box statement mutated :=
  .storagePushAddAssign (hp := rfl) (sp := path) (se := .lit 1 rfl) (hlen := rfl) rfl

/-- A concrete inhabited input, not an assumed or empty relation. -/
theorem input_inhabited : Nonempty (State C []) := ⟨empty⟩

def extended : State C [] := empty.withStorage (.cons (.array
  (.cons (.prim ⟨0, rfl⟩) .nil) .nil (by decide +kernel)) .nil)
def afterEmpty : State C [] := empty.withStorage (.cons (.array
  (.cons (.prim ⟨1, rfl⟩) .nil) .nil (by decide +kernel)) .nil)

/-- The typed run pushes and adds: `[1]`. -/
theorem actual_run : statement.runR empty = .ok ⟨afterEmpty, List.prefix_refl _⟩ := by
  with_unfolding_all rfl

/-- The push lands on `[0]`. -/
theorem first_landing : first.Lands empty extended.globG extended := by
  apply Upd.lands_iff_applyV.mpr
  refine ⟨extended.locV, ?_, ?_, ?_⟩
  · with_unfolding_all rfl
  · rfl
  · intro t i
    nomatch i

/-- The write at index `length` (1) of the one-slot array fails. -/
theorem second_fails : second.globT extended = none := by with_unfolding_all rfl

/-- So the mutant's premise admits `false` under the box. -/
theorem premise_accepts_false : holds empty (mutated.fml .box .nil .nil .ff) := by
  change first.afterT .box empty (fun τ => second.afterT .box τ (fun _ => ¬ True))
  apply Upd.afterT_intro
  · intro _
    trivial
  · intro g τ h
    have hτ : τ = extended := by
      have h1 : first.globT empty = some g := h.1
      rw [first_landing.1] at h1
      cases h1
      have hs : τ.glob = extended.glob := h.2.1
      have e1 : ∀ σ : State C [], σ.glob = σ := by
        intro σ
        cases σ
        rfl
      rw [← e1 τ, hs, e1]
    subst hτ
    apply Upd.afterT_intro
    · intro _
      trivial
    · intro g' τ' h'
      have he := h'.1
      rw [second_fails] at he
      cases he

theorem real_frames : Prog.runFrames empty (.cons statement .nil) .nil = .ok afterEmpty := by
  with_unfolding_all rfl

/-- The real execution returns, so `false` does not hold after it. -/
theorem execution_rejects_false : ¬ holds empty (.modal .box (.cons statement .nil) .nil .ff) := by
  change ¬ Modality.afterRunTR .box (fun τ => holds τ .ff) (Prog.runFrames empty (.cons statement .nil) .nil)
  rw [real_frames]
  intro h
  exact h.1 trivial

/-- The linked mutated rule is semantically unsound at this inhabited input. -/
theorem checked_kill : ¬ Premise.Sound .box statement mutated empty := by
  intro h
  exact execution_rejects_false (h .nil .nil .ff premise_accepts_false)

#print axioms source_link
#print axioms input_inhabited
#print axioms actual_run
#print axioms first_landing
#print axioms second_fails
#print axioms premise_accepts_false
#print axioms real_frames
#print axioms execution_rejects_false
#print axioms checked_kill
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @checked_kill
end H28.PushLastSlotKill
