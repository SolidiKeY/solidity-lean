import Solidity.Source.Monetary

/-! H25 exact-money authority adapter draft for G01 review. The shared Word
ledger is unchanged. Session wiring, actual fee settlement and EVM-reachable
range are NOT supplied. Funding saturation is not a balance observation. -/
namespace Solidity.Source.Monetary
open Solidity.Roadmap (Address Word Request)

structure Authority where
  balance : Address → Balance

def Authority.set (authority : Authority) (address : Address) (amount : Balance) : Authority :=
  ⟨fun other => if other = address then amount else authority.balance other⟩

theorem Authority.set_at (authority : Authority) (address : Address) (amount : Balance) :
    (authority.set address amount).balance address = amount := by
  simp only [Authority.set, if_true]

/-- Exact funding authority, separate from the unchanged shared ledger. -/
def Authority.funded (authority : Authority) (request : Request) : Prop :=
  request.value.val ≤ authority.balance request.sender

/-- Bounded affordability adapter only. Never use it as an observed balance. -/
def Authority.fundingWord (authority : Authority) (address : Address) : Word :=
  ⟨min (authority.balance address) (wordLimit-1),
    Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide : wordLimit-1 < 2^256)⟩

/-- Every legal Word-valued request has the SAME funding decision even when
exact money exceeds the Word limit. No range premise or amount is discarded. -/
theorem Authority.funding_iff (authority : Authority) (request : Request) :
    request.value.val ≤ (authority.fundingWord request.sender).val ↔ authority.funded request := by
  have bound : request.value.val ≤ wordLimit-1 := by
    have inputBound := request.value.isLt
    unfold wordLimit
    omega
  simp only [Authority.fundingWord, Authority.funded, Nat.le_min, bound, and_true]

/-- Lossless optional balance conversion, distinct from the funding adapter. -/
def Authority.balanceWord? (authority : Authority) (address : Address) : Option Word :=
  checkedWord (authority.balance address)

/-- This includes the exact post-fee value required by H19/H25. -/
def wideAuthority : Authority := ⟨fun _ => 2^256⟩

theorem wide_authority_control (address : Address) :
    wideAuthority.balance address = 2^256 ∧
    wideAuthority.balanceWord? address = none ∧
    (wideAuthority.fundingWord address).val = 2^256-1 ∧
    1 ≤ (wideAuthority.fundingWord address).val ∧
    ¬ 1 ≤ (wordView (wideAuthority.balance address)).val := by
  dsimp only [wideAuthority, Authority.balanceWord?, Authority.fundingWord]
  decide

end Solidity.Source.Monetary

/-- info: 'Solidity.Source.Monetary.Authority.set_at' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.Authority.set_at

/-- info: 'Solidity.Source.Monetary.Authority.funding_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.Authority.funding_iff

/-- info: 'Solidity.Source.Monetary.wide_authority_control' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.wide_authority_control
