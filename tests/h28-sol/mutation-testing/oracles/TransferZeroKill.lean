import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

/-! A checked counterexample to `transferNoCallbackBox` with the booked amount
replaced by `0` (`{ pay(sadr, 0) }`).  A funded `transfer` of 5 to address 9
lowers the contract's balance from 10 to 5; the mutant's update applies (it
does not halt, so the box is not vacuous) and leaves the balance 10, so its
premise admits the postcondition `selfBalance = 10`, which the run falsifies. -/
namespace H28.TransferZeroKill
open Solidity

def C : Contract := { vars := [] }
def start : State C [] := { State.init C with selfBalance := ⟨10, rfl⟩ }
def statement : Stmt C [] [] := .transfer (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl))
def zeroPay : Upd C [] [] := Upd.nil.snoc (UpdElem.pay (Simple.lit 9 rfl).lower (Tms.Term.nat 0))
def mutated : Premise C [] [] := .update zeroPay
def post : Fml C [] := .eq (Tms.Term.env .selfBalance) (Tms.Term.nat 10)

/-- This instance links the witness to the actual mutated production rule. -/
theorem source_link : Taclet C 0 .box statement mutated :=
  .transferNoCallbackBox (sadr := .lit 9 rfl) (se := .lit 5 rfl)

/-- A concrete inhabited input, not an assumed or empty relation. -/
theorem input_inhabited : Nonempty (State C []) := ⟨start⟩

/-- The typed run pays 5: the transfer succeeds. -/
theorem actual_run : statement.runR start = .ok ⟨start.pay ⟨9, rfl⟩ 5, List.prefix_refl _⟩ := by
  with_unfolding_all rfl

/-- The actual payment lowers the balance to 5. -/
theorem actual_balance : (start.pay ⟨9, rfl⟩ 5).selfBalance.1 = 5 := by with_unfolding_all rfl

/-- The mutant's update applies: its box is not vacuously satisfied by a halt. -/
theorem mutant_update_applies : (zeroPay.applyV start).isSome = true := by with_unfolding_all rfl

/-- Every state the mutant's update lands in keeps the balance 10. -/
theorem premise_accepts_post : holds start (mutated.fml .box .nil .nil post) := by
  rw [show holds start (mutated.fml .box .nil .nil post) =
    Upd.afterT .box start zeroPay (fun τ => holds τ post) from rfl]
  rw [Upd.afterT_applyV]
  intro τ hg hl
  have hb := congrArg (fun g => g.selfBalance) hg
  simp only at hb
  have h10 : τ.glob.selfBalance.1 = 10 := (by rw [hb]; with_unfolding_all rfl)
  change some _ = some _
  exact congrArg some (Subtype.ext h10)

theorem real_frames : Prog.runFrames start (.cons statement .nil) .nil = .ok (start.pay ⟨9, rfl⟩ 5) := by
  with_unfolding_all rfl

/-- The real execution ends with balance 5, so it falsifies the postcondition. -/
theorem execution_rejects_post : ¬ holds start (.modal .box (.cons statement .nil) .nil post) := by
  change ¬ Modality.afterRunTR .box (fun τ => holds τ post) (Prog.runFrames start (.cons statement .nil) .nil)
  rw [real_frames]
  intro h
  cases h.1

/-- The linked mutated rule is semantically unsound at this inhabited input. -/
theorem checked_kill : ¬ Premise.Sound .box statement mutated start := by
  intro h
  exact execution_rejects_post (h .nil .nil post premise_accepts_post)

#print axioms source_link
#print axioms input_inhabited
#print axioms actual_run
#print axioms actual_balance
#print axioms mutant_update_applies
#print axioms premise_accepts_post
#print axioms real_frames
#print axioms execution_rejects_post
#print axioms checked_kill
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @checked_kill
end H28.TransferZeroKill
