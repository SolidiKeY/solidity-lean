import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

namespace H28.PaymentFalseKill
open Solidity

def C : Contract := { vars := [] }
def start : State C [.val .bool] := { (State.init C).push (t := .val .bool) true with selfBalance := ⟨10, rfl⟩ }
def refusing : State C [.val .bool] := { start with tx := { ext := [(sendKey ⟨9, rfl⟩ ⟨5, rfl⟩, .other [])] } }
def statement : Stmt C [.val .bool] [.val .bool] := .send .here (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl)) false
def paid : State C [.val .bool] := (start.pay ⟨9, rfl⟩ 5).setLocal .here (true : Bool)
def first : Upd C [.val .bool] [.val .bool] :=
  (Upd.nil.snoc (UpdElem.payTo (.lit 9 rfl) (.lit 5 rfl))).snoc (.local .here (.val (Tm.lit (p := .bool) false)))
def second : Upd C [.val .bool] [.val .bool] := .snoc .nil (.local .here (.val (Tm.lit (p := .bool) false)))
def premise : Premise C [.val .bool] [.val .bool] := .cases [] [first, second]

theorem source_link : Taclet C 0 .box statement premise := .sendNoCallbackBox (pv := .here) (sadr := .lit 9 rfl) (se := .lit 5 rfl)

theorem input_inhabited : Nonempty (State C [.val .bool]) := ⟨start⟩
theorem accepted_run : statement.runR start = .ok ⟨paid, List.prefix_refl _⟩ := by with_unfolding_all rfl
theorem paid_ledger : paid.net = [(⟨9, rfl⟩, -5)] ∧ paid.selfBalance.1 = 5 ∧ paid.env.1 = true := by exact ⟨rfl, rfl, rfl⟩
theorem refused_rollback : statement.runR refusing = .ok ⟨refusing.setLocal .here (false : Bool), List.prefix_refl _⟩ := by with_unfolding_all rfl


def mutantPaid : State C [.val .bool] := paid.setLocal .here (false : Bool)
def mutantFailed : State C [.val .bool] := start.setLocal .here (false : Bool)

theorem first_typed_landing : first.Lands start mutantPaid.globG mutantPaid := by
  apply Upd.lands_iff_applyV.mpr
  refine ⟨start.locV.set .here (false : Bool), ?_, ?_, ?_⟩
  · with_unfolding_all rfl
  · rfl
  · intro t i
    cases i with
    | here => rfl
    | there i => nomatch i

theorem second_typed_landing : second.Lands start mutantFailed.globG mutantFailed := by
  apply Upd.lands_iff_applyV.mpr
  refine ⟨start.locV.set .here (false : Bool), ?_, ?_, ?_⟩
  · with_unfolding_all rfl
  · rfl
  · intro t i
    cases i with
    | here => rfl
    | there i => nomatch i

theorem mutant_ledger_controls : mutantPaid.net = [(⟨9, rfl⟩, -5)] ∧
    mutantPaid.selfBalance.1 = 5 ∧ mutantPaid.env.1 = false ∧
    mutantFailed.net = start.net ∧ mutantFailed.selfBalance = start.selfBalance ∧
    mutantFailed.env.1 = false := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def post : Fml C [.val .bool] := .eq (.pvV .here) (Tm.lit (p := .bool) false)

theorem first_post : first.afterT .box start (fun τ => holds τ post) := by
  rw [Upd.afterT_applyV]
  intro τ hg hl
  change some (τ.getV (t := .val .bool) .here) = some false
  rw [hl .here]
  rfl

theorem second_post : second.afterT .box start (fun τ => holds τ post) := by
  rw [Upd.afterT_applyV]
  intro τ hg hl
  change some (τ.getV (t := .val .bool) .here) = some false
  rw [hl .here]
  rfl

theorem premise_accepts_post : holds start (premise.fml .box .nil .nil post) := by
  exact ⟨first_post, second_post⟩

theorem real_frames : Prog.runFrames start (.cons statement .nil) .nil = .ok paid := by with_unfolding_all rfl

theorem execution_rejects_post : ¬ holds start (.modal .box (.cons statement .nil) .nil post) := by
  change ¬ Modality.afterRunTR .box (fun τ => holds τ post) (Prog.runFrames start (.cons statement .nil) .nil)
  rw [real_frames]
  intro h
  have bad : some true = some false := h.1
  cases bad

theorem checked_kill : ¬ Premise.Sound .box statement premise start := by
  intro h
  exact execution_rejects_post (h .nil .nil post premise_accepts_post)

#print axioms source_link
#print axioms input_inhabited
#print axioms accepted_run
#print axioms paid_ledger
#print axioms refused_rollback
#print axioms first_post
#print axioms second_post
#print axioms premise_accepts_post
#print axioms real_frames
#print axioms execution_rejects_post
#print axioms checked_kill
#print axioms first_typed_landing
#print axioms second_typed_landing
#print axioms mutant_ledger_controls
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @accepted_run
#check @paid_ledger
#check @refused_rollback
#check @first_post
#check @second_post
#check @premise_accepts_post
#check @real_frames
#check @execution_rejects_post
#check @checked_kill
#check @first_typed_landing
#check @second_typed_landing
#check @mutant_ledger_controls
end H28.PaymentFalseKill
