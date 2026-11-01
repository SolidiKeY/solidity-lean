import Solidity.Backend.Environment.Observations

/-! Inhabited G31 controls. No chain assumptions or hash uniqueness premises. -/
namespace Solidity.Backend.Environment

private def a7 : Address := account (lenU 7 (by decide))
private def a9 : Address := account (lenU 9 (by decide))

def sample : Frame :=
  { self := a7, sender := a9, value := lenU 11 (by decide),
    time := lenU 13 (by decide),
    funds := fun a => if a = a7 then lenU 41 (by decide) else lenU 73 (by decide) }

/-- Nonzero, distinct sender, self, payment, time and balance are permitted. -/
theorem sample_observations :
    (observe sample .msgSender).1 = 9 ∧ (observe sample .selfAddress).1 = 7 ∧
    (observe sample .msgValue).1 = 11 ∧ (observe sample .timestamp).1 = 13 ∧
    (observe sample .selfBalance).1 = 41 := by decide +kernel

/-- Arbitrary source storage/heap/locals/oracle/net survive this representation
witness: only the five environment projections need replacement. -/
def represented {C : Contract} {Γ : Ctx} (σ : State C Γ) (f : Frame) : State C Γ :=
  let tx : TTx :=
    { msgSender := f.sender.1
      selfAddress := f.self.1
      msgValue := f.value
      timestamp := f.time
      ext := σ.tx.ext }
  { σ with tx := tx, selfBalance := f.funds f.self }

theorem represented_ok {C : Contract} {Γ : Ctx} (σ : State C Γ) (f : Frame) :
    Represents f (represented σ f) := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem inhabited_certificate (k : EnvKey) (tail : List Word) :
    Val.evalT (represented (State.init default) sample)
      (.simple (.env k rfl) : Val default [] .uint) = .ok (observe sample k) ∧
    step sample (select k) tail = some (observe sample k :: tail) :=
  intrinsic_correct (represented_ok _ _) k tail

/-- Failing to truncate would select a different account. -/
theorem high_address_control :
    (account (lenU (2 ^ 160 + 7) (by decide))).1.1 = 7 ∧
    (lenU (2 ^ 160 + 7) (by decide)).1 ≠ (account (lenU (2 ^ 160 + 7) (by decide))).1.1 := by
  decide

theorem high_balance_control :
    step sample (.op .BALANCE) [lenU (2 ^ 160 + 7) (by decide)] =
      some [lenU 41 (by decide)] := by decide +kernel

/-- SELFBALANCE must not use the top word as its account argument. -/
theorem own_balance_control :
    step sample (.op .SELFBALANCE) [a9.1] = some [lenU 41 (by decide), a9.1] ∧
    step sample (.op .BALANCE) [a9.1] = some [lenU 73 (by decide)] := by decide +kernel

/-- Substituting CALLER for ADDRESS changes an inhabited observation. -/
theorem wrong_opcode_control :
    step sample (.op .CALLER) [] ≠ step sample (.op .ADDRESS) [] := by decide +kernel

/-- info: 'Solidity.Backend.Environment.select_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms select_correct
/-- info: 'Solidity.Backend.Environment.intrinsic_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms intrinsic_correct
/-- info: 'Solidity.Backend.Environment.account_address' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms account_address
end Solidity.Backend.Environment
