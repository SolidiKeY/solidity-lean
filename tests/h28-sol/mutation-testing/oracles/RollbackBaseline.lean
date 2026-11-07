import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

namespace H28.RollbackBaseline
open Solidity

def C : Contract := { vars := [] }
abbrev Γ : Ctx := [.val .bool]
def funded : State C Γ := { (State.init C).push (t := .val .bool) true with selfBalance := ⟨10, rfl⟩ }
def refusing : State C Γ := { funded with tx := { ext := [(sendKey ⟨9, rfl⟩ ⟨5, rfl⟩, .other [])] } }
def statement : Stmt C Γ Γ := .send .here (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl)) false
def accepted : State C Γ := (funded.pay ⟨9, rfl⟩ 5).setLocal .here (true : Bool)
def failed : State C Γ := refusing.setLocal .here (false : Bool)
def first : Upd C Γ Γ := (Upd.nil.snoc (UpdElem.payTo (.lit 9 rfl) (.lit 5 rfl))).snoc (.local .here (.val (Tm.lit (p := .bool) true)))
def second : Upd C Γ Γ := .snoc .nil (.local .here (.val (Tm.lit (p := .bool) false)))
def premise : Premise C Γ Γ := .cases [] [first, second]

theorem source_link : Taclet C 0 .box statement premise := .sendNoCallbackBox (pv := .here) (sadr := .lit 9 rfl) (se := .lit 5 rfl)
theorem input_inhabited : Nonempty (State C Γ) := ⟨refusing⟩
theorem accepted_run : statement.runR funded = .ok ⟨accepted, List.prefix_refl _⟩ := by with_unfolding_all rfl
theorem refused_run : statement.runR refusing = .ok ⟨failed, List.prefix_refl _⟩ := by with_unfolding_all rfl
theorem paid_controls : accepted.net = [(⟨9, rfl⟩, -5)] ∧ accepted.selfBalance.1 = 5 ∧ accepted.env.1 = true := by exact ⟨rfl, rfl, rfl⟩
theorem rollback_controls : failed.net = refusing.net ∧ failed.selfBalance = refusing.selfBalance ∧ failed.storage = refusing.storage ∧ failed.env.1 = false := by exact ⟨rfl, rfl, rfl, rfl⟩

#print axioms source_link
#print axioms input_inhabited
#print axioms accepted_run
#print axioms refused_run
#print axioms paid_controls
#print axioms rollback_controls
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @accepted_run
#check @refused_run
#check @paid_controls
#check @rollback_controls
end H28.RollbackBaseline
