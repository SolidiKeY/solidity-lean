import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# DeFi: fixed-rate native-asset vault

Source: EIP-4626, Specification, deposit/withdraw accounting:
<https://github.com/ethereum/ERCs/blob/ee3298cc117ecc5311ac5fa3fafc2d8e54984cc3/ERCS/erc-4626.md> (Final, created 2021-12-22).
This is the fixed 1:1 share-price verification example, using native currency
instead of an external ERC20. It is not an implementation of the ERC4626 API:
allowances, previews, external tokens, fees and variable share prices are absent.
Explicit assets and supply counters track managed deposits, not unsolicited ETH.

Both counters and the caller's shares change by the same amount. The round-trip
obligation retains the initial values, including outstanding shares of other
accounts. Successful-run specifications do not assert that ETH delivery succeeds.
-/
namespace Solidity.Examples.Benchmark.Defi.FixedRateVault

def FixedRateVault : Contract := contract!{
  uint public totalAssets;
  uint public totalSupply;
  mapping(address => uint) public shares;
  ensures shares[msg.sender] == \old(shares[msg.sender]) + msg.value;
  ensures totalAssets == \old(totalAssets) + msg.value;
  ensures totalSupply == \old(totalSupply) + msg.value;
  function deposit() public payable {
    shares[msg.sender] += msg.value;
    totalAssets += msg.value;
    totalSupply += msg.value;
  }
  ensures shares[msg.sender] == \old(shares[msg.sender]) - assets;
  ensures totalAssets == \old(totalAssets) - assets;
  ensures totalSupply == \old(totalSupply) - assets;
  function withdraw(uint assets) public {
    shares[msg.sender] -= assets;
    totalAssets -= assets;
    totalSupply -= assets;
    msg.sender.transfer(assets);
  }
}
local instance : InContract := ⟨FixedRateVault⟩
open scoped Scoped

/-- Deposit mints one share for every managed asset. -/
def deposit_obligation : Fml FixedRateVault [] := spec!{ deposit }
/- Unknown: after the payable old-storage snapshot and three saves, the leaf
must relate shares, assets and supply to their old values plus msg.value.
Missing closure: payable snapshot normalization across mapping/scalar saves. -/
/-- Withdrawal burns one share for every managed asset paid out. -/
theorem withdraw_spec : ⊢ spec!{ withdraw } := by sol_prove
/-- Deposit followed by withdrawal of that deposit restores all three accounts. -/
theorem roundTrip : ⊢ dl!{
  s == shares[msg.sender] && a == totalAssets && t == totalSupply →
  [ deposit(); withdraw(msg.value); ]
  shares[msg.sender] == s && totalAssets == a && totalSupply == t } := by
  sol_prove

end Solidity.Examples.Benchmark.Defi.FixedRateVault
