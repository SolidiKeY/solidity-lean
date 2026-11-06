import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

namespace H28.RollbackBookedKill
open Solidity

def C : Contract := { vars := [] }
abbrev Γ : Ctx := [.val .bool]
def funded : State C Γ := { (State.init C).push (t := .val .bool) true with selfBalance := ⟨10, rfl⟩ }
def refusing : State C Γ := { funded with tx := { ext := [(sendKey ⟨9, rfl⟩ ⟨5, rfl⟩, .other [])] } }
def statement : Stmt C Γ Γ := .send .here (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl)) false
def accepted : State C Γ := (funded.pay ⟨9, rfl⟩ 5).setLocal .here (true : Bool)
def failed : State C Γ := refusing.setLocal .here (false : Bool)
def first : Upd C Γ Γ := (Upd.nil.snoc (UpdElem.payTo (.lit 9 rfl) (.lit 5 rfl))).snoc (.local .here (.val (Tm.lit (p := .bool) true)))
def second : Upd C Γ Γ := (Upd.nil.snoc (UpdElem.payTo (.lit 9 rfl) (.lit 5 rfl))).snoc (.local .here (.val (Tm.lit (p := .bool) false)))
def premise : Premise C Γ Γ := .cases [] [first, second]
def bookedTrue : State C Γ := (refusing.pay ⟨9, rfl⟩ 5).setLocal .here (true : Bool)
def bookedFalse : State C Γ := (refusing.pay ⟨9, rfl⟩ 5).setLocal .here (false : Bool)
def post : Fml C Γ := .eq (.app2 (.zcmp .eqB rfl) (.app1 .net (Tm.lit (p := .uint) ⟨9, rfl⟩)) (.app0 (.zlit (-5)))) (Tm.lit (p := .bool) true)

theorem source_link : Taclet C 0 .box statement premise := .sendNoCallbackBox (pv := .here) (sadr := .lit 9 rfl) (se := .lit 5 rfl)
theorem input_inhabited : Nonempty (State C Γ) := ⟨refusing⟩
theorem refused_run : statement.runR refusing = .ok ⟨failed, List.prefix_refl _⟩ := by with_unfolding_all rfl
theorem rollback_controls : failed.net = refusing.net ∧ failed.selfBalance.1 = 10 ∧ failed.env.1 = false := by exact ⟨rfl, rfl, rfl⟩
theorem mutant_effect_controls : bookedTrue.net = [(⟨9, rfl⟩, -5)] ∧ bookedFalse.net = [(⟨9, rfl⟩, -5)] ∧ bookedTrue.selfBalance.1 = 5 ∧ bookedFalse.selfBalance.1 = 5 ∧ bookedTrue.env.1 = true ∧ bookedFalse.env.1 = false := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem first_landing : first.Lands refusing bookedTrue.globG bookedTrue := by
  apply Upd.lands_iff_applyV.mpr
  refine ⟨refusing.locV.set .here (true : Bool), ?_, ?_, ?_⟩
  · with_unfolding_all rfl
  · rfl
  · intro t i
    cases i with
    | here => rfl
    | there i => nomatch i

theorem second_landing : second.Lands refusing bookedFalse.globG bookedFalse := by
  apply Upd.lands_iff_applyV.mpr
  refine ⟨refusing.locV.set .here (false : Bool), ?_, ?_, ?_⟩
  · with_unfolding_all rfl
  · rfl
  · intro t i
    cases i with
    | here => rfl
    | there i => nomatch i

theorem first_post : first.afterT .box refusing (fun τ => holds τ post) := by
  rw [Upd.afterT_applyV]
  intro τ hg _hl
  have hn := congrArg (fun g : State C [] => g.net) hg
  change τ.net = [(⟨9, rfl⟩, -5)] at hn
  change some (BinOp.cmpZ .eqB ((Semantics.lookupBy (⟨9, rfl⟩ : PrimTy.uint.Denote) τ.net).getD 0) (-5)) = some true
  rw [hn]
  rfl

theorem second_post : second.afterT .box refusing (fun τ => holds τ post) := by
  rw [Upd.afterT_applyV]
  intro τ hg _hl
  have hn := congrArg (fun g : State C [] => g.net) hg
  change τ.net = [(⟨9, rfl⟩, -5)] at hn
  change some (BinOp.cmpZ .eqB ((Semantics.lookupBy (⟨9, rfl⟩ : PrimTy.uint.Denote) τ.net).getD 0) (-5)) = some true
  rw [hn]
  rfl

theorem premise_accepts_post : holds refusing (premise.fml .box .nil .nil post) := ⟨first_post, second_post⟩
theorem real_frames : Prog.runFrames refusing (.cons statement .nil) .nil = .ok failed := by with_unfolding_all rfl
theorem execution_rejects_post : ¬ holds refusing (.modal .box (.cons statement .nil) .nil post) := by
  change ¬ Modality.afterRunTR .box (fun τ => holds τ post) (Prog.runFrames refusing (.cons statement .nil) .nil)
  rw [real_frames]
  intro h
  have bad : some false = some true := h.1
  cases bad

theorem checked_kill : ¬ Premise.Sound .box statement premise refusing := by
  intro h
  exact execution_rejects_post (h .nil .nil post premise_accepts_post)

#print axioms source_link
#print axioms input_inhabited
#print axioms refused_run
#print axioms rollback_controls
#print axioms mutant_effect_controls
#print axioms first_landing
#print axioms second_landing
#print axioms first_post
#print axioms second_post
#print axioms premise_accepts_post
#print axioms real_frames
#print axioms execution_rejects_post
#print axioms checked_kill
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @refused_run
#check @rollback_controls
#check @mutant_effect_controls
#check @first_landing
#check @second_landing
#check @first_post
#check @second_post
#check @premise_accepts_post
#check @real_frames
#check @execution_rejects_post
#check @checked_kill
end H28.RollbackBookedKill
