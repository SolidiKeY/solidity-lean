import Solidity.Calculus.PaymentWitness

/-!
# Diamond payments: success and countercontrols

Kernel evidence for the payment boundary, separate from solc/EVM execution.
The ledger invariant is the payout invariant used by net callback problems:
what survives a callback is its invariant, not the pre-callback ledger value.
-/

namespace Solidity.Examples.Tactics.PaymentWitness

open Semantics

private abbrev start : State StandardExample [] :=
  { State.ofStorage Storage.standardExample with selfBalance := ⟨10, rfl⟩ }
private def recipient : Simple StandardExample [] .uint := .lit 9 rfl
private def amount : Simple StandardExample [] .uint := .lit 5 rfl
private abbrev poor : State StandardExample [] := { start with selfBalance := ⟨3, rfl⟩ }
private abbrev refusing : State StandardExample [] :=
  { start with tx := { ext := [(sendKey ⟨9, rfl⟩ ⟨5, rfl⟩, .other [])] } }

/-- A funded, accepted payment has the full expected ledger and balance effects. -/
theorem accepted_transfer :
    Modality.diamond.afterRunTR
      (fun o => (lookupBy (⟨9, rfl⟩ : PrimTy.uint.Denote) o.st.net).getD 0 = -5 ∧
        o.st.selfBalance.1 = 5)
      (TRun.transfer (.simple recipient) (.simple amount) start) := by
  apply (Solidity.PaymentWitness.transferNoCallbackDiamond start recipient amount
    (fun τ => (lookupBy (⟨9, rfl⟩ : PrimTy.uint.Denote) τ.net).getD 0 = -5 ∧
      τ.selfBalance.1 = 5)).2
  exact ⟨by decide +kernel, rfl, rfl⟩

/-- Nonnegativity alone cannot justify the upstream transfer diamond. -/
theorem insufficient_transfer :
    ¬ Modality.diamond.afterRunTR (fun _ => True)
      (TRun.transfer (.simple recipient) (.simple amount) poor) := by
  intro h
  have bad := (Solidity.PaymentWitness.transferNoCallbackDiamond poor recipient amount
    (fun _ => True)).1 h
  have hc : poor.canPay (recipient.evalT poor) (amount.evalT poor) = false := by decide +kernel
  rw [hc] at bad
  cases bad.1

/-- An accepting balance cannot justify a transfer when the recipient reverts. -/
theorem reverted_transfer :
    ¬ Modality.diamond.afterRunTR (fun _ => True)
      (TRun.transfer (.simple recipient) (.simple amount) refusing) := by
  intro h
  have bad := (Solidity.PaymentWitness.transferNoCallbackDiamond refusing recipient amount
    (fun _ => True)).1 h
  have hc : refusing.canPay (recipient.evalT refusing) (amount.evalT refusing) = false := by decide +kernel
  rw [hc] at bad
  cases bad.1

/-- The send failure continuation keeps the entire ledger and balance. -/
theorem refused_send :
    let σ := refusing.push (t := .val .bool) true
    Modality.diamond.afterRunTR
      (fun o => o.st.env.1 = false ∧ o.st.net = refusing.net ∧ o.st.selfBalance.1 = 10)
      (TRun.send .here (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl)) σ) := by
  constructor
  · exact ⟨rfl, rfl, rfl⟩
  · intro h
    cases h

/-- The invariant at the payment boundary in `net-call-withcallback-simple`:
the ledger entry at the recipient remains nonpositive. -/
def ledgerInv : StateInv StandardExample :=
  ⟨fun σ => (lookupBy (⟨9, rfl⟩ : PrimTy.uint.Denote) σ.net).getD 0 ≤ 0, true⟩

/-- A funded transfer preserves the ledger invariant in every callback outcome. -/
theorem callback_transfer :
    ∀ o, ExecS ledgerInv start (.transfer (.simple recipient) (.simple amount)) o →
      o.after .diamond (fun τ => ledgerInv.at τ) := by
  apply Solidity.PaymentWitness.transferWithCallbackDiamond ledgerInv rfl start recipient amount
  · decide +kernel
  · change (-5 : Int) ≤ 0
    decide +kernel
  · exact fun _ _ _ hj => hj

/-- The callback send diamond covers both outcomes while preserving the same
ledger invariant, including under the full-gas reading. -/
theorem callback_send :
    let σ := start.push (t := .val .bool) true
    ∀ o, ExecS ledgerInv σ
      (.send .here (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl)) true) o →
      o.after .diamond (fun τ => ledgerInv.at τ) := by
  apply Solidity.PaymentWitness.sendWithCallbackDiamond ledgerInv true rfl
    (start.push (t := .val .bool) true) .here (.lit 9 rfl) (.lit 5 rfl)
  · intro paid h
    have run : TRun.transfer (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl))
        (start.push (t := .val .bool) true) =
        .ok ⟨(start.push (t := .val .bool) true).pay ⟨9, rfl⟩ 5, List.prefix_refl _⟩ := rfl
    rw [run] at h
    cases h
    change (-5 : Int) ≤ 0
    decide +kernel
  · exact fun _ _ _ _ _ hj => hj
  · change (0 : Int) ≤ 0
    decide +kernel

/-- A successful callback send exists with the full expected result flag,
ledger debit and live balance. The nearby refusal witness uses the same inputs. -/
theorem accepted_send_success :
    let σ := start.push (t := .val .bool) false
    let paid := σ.pay ⟨9, rfl⟩ 5
    ExecS ledgerInv σ
      (.send .here (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl)) true)
      (.ok ⟨paid.setLocal .here (true : Bool), List.prefix_refl _⟩) ∧
      (paid.setLocal .here (true : Bool)).env.1 = true ∧
      (lookupBy (⟨9, rfl⟩ : PrimTy.uint.Denote) paid.net).getD 0 = -5 ∧
      paid.selfBalance.1 = 5 := by
  constructor
  · exact ExecS.sendResume (J := ledgerInv) (σ := start.push (t := .val .bool) false)
      (pv := .here) (r := .simple (.lit 9 rfl)) (a := .simple (.lit 5 rfl)) (full := true)
      (o₁ := ⟨(start.push (t := .val .bool) false).pay ⟨9, rfl⟩ 5, List.prefix_refl _⟩)
      (st := start.storage) (nt := [(⟨9, rfl⟩, -5)]) (sb := ⟨5, rfl⟩)
      rfl rfl (by change (-5 : Int) ≤ 0; decide +kernel)
      (by change (-5 : Int) ≤ 0; decide +kernel)
  · exact ⟨rfl, rfl, rfl⟩

/-- The very same invariant, option, state and operands also admit failure.
Thus deterministic acceptance cannot remove the callback failure continuation. -/
theorem accepted_send_may_revert_same_invariant :
    let σ := start.push (t := .val .bool) false
    ExecS ledgerInv σ
      (.send .here (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl)) true)
      (.ok ⟨σ.setLocal .here (false : Bool), List.prefix_refl _⟩) := by
  exact ExecS.sendFailed
    (o₁ := ⟨(start.push (t := .val .bool) false).pay ⟨9, rfl⟩ 5, List.prefix_refl _⟩)
    rfl rfl

/-- An accepted send may still fail when its callee calls back, under full gas
and `noCallback` alike. This control must survive any send diamond rule. -/
theorem accepted_send_may_revert :
    let σ := start.push (t := .val .bool) true
    ExecS (⟨fun _ => True, false⟩ : StateInv StandardExample) σ
      (.send .here (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl)) true)
      (.ok ⟨σ.setLocal .here (false : Bool), List.prefix_refl _⟩) := by
  exact ExecS.sendFailed
    (o₁ := ⟨(start.push (t := .val .bool) true).pay ⟨9, rfl⟩ 5, List.prefix_refl _⟩)
    rfl rfl

/-- Stipend sends do not fork under the selected `noCallback` assumption. -/
theorem stipend_noCallback :
    (Stmt.send (C := StandardExample) (Γ := [.val .bool]) .here
      (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl)) false).forksIn false = false := rfl

/-- Full-gas value calls fork under that same assumption. -/
theorem full_gas_noCallback :
    (Stmt.send (C := StandardExample) (Γ := [.val .bool]) .here
      (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl)) true).forksIn false = true := rfl

/-- A callback may replace the ledger even after an accepted transfer. The
invariant is essential; the deterministic post-payment value is not a frame. -/
theorem callback_changes_ledger :
    let J : StateInv StandardExample := ⟨fun _ => True, true⟩
    let paid := start.pay (recipient.evalT start) (amount.evalT start).1
    ExecS J start (.transfer (.simple recipient) (.simple amount))
      (.ok ⟨paid.havoc paid.storage [] ⟨0, rfl⟩, List.prefix_refl _⟩) ∧
      (lookupBy (⟨9, rfl⟩ : PrimTy.uint.Denote)
        (paid.havoc paid.storage [] ⟨0, rfl⟩).net).getD 0 ≠ -5 := by
  constructor
  · exact ExecS.transferResume (J := ⟨fun _ => True, true⟩) (σ := start)
      (r := .simple recipient) (a := .simple amount)
      (o₁ := ⟨start.pay ⟨9, rfl⟩ 5, List.prefix_refl _⟩) rfl rfl trivial trivial
  · decide +kernel

/-- A callback transfer still exposes insufficient balance as a revert. -/
theorem insufficient_callback_transfer :
    ExecS ledgerInv poor (.transfer (.simple recipient) (.simple amount)) (.halt .revert) :=
  Solidity.PaymentWitness.transfer_refused ledgerInv rfl poor recipient amount (by decide +kernel)

/-- An invariant initially true may be false at the payout boundary. The exit
obligation cannot be replaced by an assumption about the starting state. -/
theorem broken_exit :
    let J : StateInv StandardExample :=
      ⟨fun σ => (lookupBy (⟨9, rfl⟩ : PrimTy.uint.Denote) σ.net).getD 0 = 0, true⟩
    J.at start ∧ ExecS J start (.transfer (.simple recipient) (.simple amount)) .violated := by
  constructor
  · rfl
  · exact ExecS.transferViolated (σ := start) (r := .simple recipient) (a := .simple amount)
      (o₁ := ⟨start.pay ⟨9, rfl⟩ 5, List.prefix_refl _⟩)
      rfl rfl (by change ¬ (-5 : Int) = 0; decide +kernel)

#print axioms accepted_transfer
#print axioms callback_transfer
#print axioms callback_send
#print axioms accepted_send_success
#print axioms accepted_send_may_revert_same_invariant
#print axioms accepted_send_may_revert
#print axioms callback_changes_ledger
#print axioms insufficient_callback_transfer
#print axioms broken_exit

end Solidity.Examples.Tactics.PaymentWitness
