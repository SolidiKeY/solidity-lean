import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

namespace H28.PaymentBaseline
open Solidity

def C : Contract := { vars := [] }
def start : State C [.val .bool] := { (State.init C).push (t := .val .bool) true with selfBalance := ⟨10, rfl⟩ }
def refusing : State C [.val .bool] := { start with tx := { ext := [(sendKey ⟨9, rfl⟩ ⟨5, rfl⟩, .other [])] } }
def statement : Stmt C [.val .bool] [.val .bool] := .send .here (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl)) false
def paid : State C [.val .bool] := (start.pay ⟨9, rfl⟩ 5).setLocal .here (true : Bool)
def first : Upd C [.val .bool] [.val .bool] :=
  (Upd.nil.snoc (UpdElem.payTo (.lit 9 rfl) (.lit 5 rfl))).snoc (.local .here (.val (Tm.lit (p := .bool) true)))
def second : Upd C [.val .bool] [.val .bool] := .snoc .nil (.local .here (.val (Tm.lit (p := .bool) false)))
def premise : Premise C [.val .bool] [.val .bool] := .cases [] [first, second]

theorem source_link : Taclet C 0 .box statement premise := .sendNoCallbackBox (pv := .here) (sadr := .lit 9 rfl) (se := .lit 5 rfl)

theorem input_inhabited : Nonempty (State C [.val .bool]) := ⟨start⟩
theorem accepted_run : statement.runR start = .ok ⟨paid, List.prefix_refl _⟩ := by with_unfolding_all rfl
theorem paid_ledger : paid.net = [(⟨9, rfl⟩, -5)] ∧ paid.selfBalance.1 = 5 ∧ paid.env.1 = true := by exact ⟨rfl, rfl, rfl⟩
theorem refused_rollback : statement.runR refusing = .ok ⟨refusing.setLocal .here (false : Bool), List.prefix_refl _⟩ := by with_unfolding_all rfl

#print axioms source_link
#print axioms input_inhabited
#print axioms accepted_run
#print axioms paid_ledger
#print axioms refused_rollback
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @accepted_run
#check @paid_ledger
#check @refused_rollback
end H28.PaymentBaseline
