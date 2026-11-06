import Solidity.Yul.Views.SourceTargetInputs

namespace Solidity.Yul.Views

/-- The actual target Address's uint/160bit bounds derive this inverse. -/
def sourceAddressOfEnvironment (address : ContractWorld.Address) : Roadmap.Address :=
  ⟨address.1.1.toNat,by
    have lower : 0≤address.1.1 := (of_decide_eq_true address.1.2).1
    apply (Int.toNat_lt lower).2
    rw [Int.natCast_pow]
    exact address.2⟩

theorem sourceAddress_environment_roundtrip (address : Roadmap.Address) :
    sourceAddressOfEnvironment (environmentAddress address)=address := by
  apply Fin.ext
  change ((environmentAddress address).1).1.toNat=address.val
  rw [environmentAddress_word,environmentWord_nat]
  rfl

theorem environmentAddress_source_roundtrip (address : ContractWorld.Address) :
    environmentAddress (sourceAddressOfEnvironment address)=address := by
  apply Subtype.ext
  rw [environmentAddress_word]
  apply Subtype.ext
  have lower : 0≤address.1.1 := (of_decide_eq_true address.1.2).1
  have bound : address.1.1.toNat < 2^256 := (addressInputWord (sourceAddressOfEnvironment address)).isLt
  change ((address.1.1.toNat % 2^256 : Nat) : Int)=address.1.1
  rw [Nat.mod_eq_of_lt bound,Int.toNat_of_nonneg lower]

/-- Exactly the existing Source.evalE.balance observation. Code presence is
not replaced by program catalog membership. No state/ledger semantics added. -/
def sourceObservedBalance {E Γ} (G : Source.Glob E) (s : Source.EMState E Γ)
    (address : Roadmap.Address) : Roadmap.Word :=
  match (s.2.ex.world.accounts address).code with
  | some _ => (s.2.ex.world.accounts address).balance
  | none => G.fixed.ledger G.balance0 s.2.events address

theorem sourceObservedBalance_system {E Γ} (G : Source.Glob E) (s : Source.EMState E Γ)
    (address : Roadmap.Address) (code : Nat) (found : (s.2.ex.world.accounts address).code=some code) :
    sourceObservedBalance G s address=(s.2.ex.world.accounts address).balance := by
  simp only [sourceObservedBalance,found]

theorem sourceObservedBalance_external {E Γ} (G : Source.Glob E) (s : Source.EMState E Γ)
    (address : Roadmap.Address) (missing : (s.2.ex.world.accounts address).code=none) :
    sourceObservedBalance G s address=G.fixed.ledger G.balance0 s.2.events address := by
  simp only [sourceObservedBalance,missing]

/-- Constructed snapshot of actual source observations. This is NOT a proof
that an independently provided target runtime ledger equals this function. -/
def sourceObservedFunds {E Γ} (G : Source.Glob E) (s : Source.EMState E Γ)
    (address : ContractWorld.Address) : Backend.Environment.Word :=
  environmentWord (sourceObservedBalance G s (sourceAddressOfEnvironment address))

theorem sourceObservedFunds_address {E Γ} (G : Source.Glob E) (s : Source.EMState E Γ)
    (address : Roadmap.Address) : sourceObservedFunds G s (environmentAddress address)=
      environmentWord (sourceObservedBalance G s address) := by
  unfold sourceObservedFunds
  rw [sourceAddress_environment_roundtrip]

theorem sourceObserved_self_balance {E Γ} (G : Source.Glob E) (F : Source.Fr) (s : Source.EMState E Γ) :
    Backend.Environment.observe (sourceEnvironmentFrame G F (sourceObservedFunds G s)) .selfBalance=
      environmentWord (sourceObservedBalance G s F.this) := sourceObservedFunds_address G s F.this

end Solidity.Yul.Views
