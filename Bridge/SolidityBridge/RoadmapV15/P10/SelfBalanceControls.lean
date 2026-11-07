import SolidityBridge.RoadmapV15.P10.SelfBalanceTransport
import SolidityBridge.RoadmapV15.P10.HeaderEnvironmentControls

/-! Canonical self-ledger clients with independent existing expected records.
These native fixtures do not certify source/world entry provenance. -/
namespace SolidityBridge.RoadmapV15.P10.SelfBalanceControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (u accounts)

def words : Scalar.Stack := [11,258,513]
def site : Site .SELFBALANCE := HeaderEnvironmentControls.entry .SELFBALANCE 9 false 260 accounts words
def expected : EVM.State := HeaderEnvironmentControls.observed .SELFBALANCE false 260 accounts words (u 29) 4
/-- Deliberately different candidate self/funds; the view obtains both from native data. -/
def frame : Backend.Environment.Frame :=
  {self := Backend.Environment.account (slotWord (u 11)),
   sender := Backend.Environment.account (slotWord (u 19)),
   value := slotWord (u 37),time := slotWord (u 260),funds := fun _ => slotWord (u 999)}

theorem client :
    Backend.Environment.step (selfBalanceFrame frame site.state.toState) (Backend.Environment.select .selfBalance) (site.state.stack.map slotWord) = some (slotWord (UInt256.ofNat 29)::site.state.stack.map slotWord) ∧ Assembly.driverSteps 1 2 #[] site.state = .ok expected ∧ EVM.X 2 #[] site.state = EVM.X 1 #[] expected ∧ expected.toState = site.state.toState ∧ expected.memory = site.state.memory ∧ expected.returnData = site.state.returnData ∧ expected.H_return = site.state.H_return
    := by
  exact selfbalance_agreement frame site 0 (by decide) (by decide)

#print axioms client

theorem negative :
    Backend.Environment.step frame (.op .SELFBALANCE) [] = some [slotWord (UInt256.ofNat 999)] ∧ Backend.Environment.step (balanceFrame frame site.state.toState) (.op .SELFBALANCE) [] = some [slotWord (UInt256.ofNat 41)] ∧ expected.stack ≠ [UInt256.ofNat 41,UInt256.ofNat 11,UInt256.ofNat 258,UInt256.ofNat 513] ∧ expected.stack ≠ [UInt256.ofNat 29,UInt256.ofNat 11,UInt256.ofNat 513,UInt256.ofNat 258]
    := by
  refine ⟨rfl,rfl,?_,?_⟩ <;> decide

#print axioms negative

theorem boundary :
    AccountAddress.ofUInt256 (UInt256.ofNat (AccountAddress.ofNat (2^160-1)).val) = AccountAddress.ofNat (2^160-1)
    := by
  exact native_address_word_roundtrip _

#print axioms boundary

end SolidityBridge.RoadmapV15.P10.SelfBalanceControls
