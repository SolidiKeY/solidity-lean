import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Fee-on-transfer token (weird-erc20 `TransferFeeToken`)

Sources (d-xo/weird-erc20, commit `781c8f039c106eb2d5c6071046b0dbb2f72c9870`):
<https://raw.githubusercontent.com/d-xo/weird-erc20/781c8f039c106eb2d5c6071046b0dbb2f72c9870/src/TransferFee.sol>
and the same commit's `src/ERC20.sol` (the base `Math`, constructor, `transfer`).

Every transfer moves `wad` out of `src`, credits `dst` with `wad - fee` and
the sink `balanceOf[address(0)]` with `fee`. `Math.add`/`Math.sub` revert
exactly when the word operation wraps, so they are written as checked `+`/`-`.
Events, `name`/`symbol`/`decimals` and inheritance are omitted; `transfer`
calls `transferFrom` (inlined) as the base does.

Natural spec: for distinct `src`, `dst` and sink, the three touched balances
keep their sum (the fee goes to the sink), each has its exact effect, other
balances and `totalSupply` are unchanged, and a finite allowance of a third
party is spent. Verdicts are on each theorem/definition below.

Verdicts: constructor proved; transferFrom and transfer UNKNOWN at the
three-slot sum leaf, every other clause proved as a component.
-/
namespace Solidity.Examples.Benchmark.TokenExtensions.FeeOnTransfer

def TransferFeeToken : Contract := contract!{
  uint256 totalSupply;
  mapping(address => uint) balanceOf;
  mapping(address => mapping(address => uint)) allowance;
  uint immutable fee;
  ensures fee == _fee && totalSupply == _totalSupply && balanceOf[msg.sender] == _totalSupply;
  constructor(uint _totalSupply, uint _fee) {
    totalSupply = _totalSupply;
    balanceOf[msg.sender] = _totalSupply;
    fee = _fee;
  }
  requires balanceOf[src] >= wad;
  ensures \result && totalSupply == \old(totalSupply);
  ensures src != dst && src != address(0) && dst != address(0) -> balanceOf[src] + balanceOf[dst] + balanceOf[address(0)] == \old(balanceOf[src]) + \old(balanceOf[dst]) + \old(balanceOf[address(0)]);
  ensures src != dst && src != address(0) && dst != address(0) -> balanceOf[src] == \old(balanceOf[src]) - wad && balanceOf[dst] == \old(balanceOf[dst]) + (wad - fee) && balanceOf[address(0)] == \old(balanceOf[address(0)]) + fee;
  ensures \forall address a; a != src && a != dst && a != address(0) -> balanceOf[a] == \old(balanceOf[a]);
  ensures src != msg.sender && \old(allowance[src][msg.sender]) != 115792089237316195423570985008687907853269984665640564039457584007913129639935 -> allowance[src][msg.sender] == \old(allowance[src][msg.sender]) - wad;
  function transferFrom(address src, address dst, uint wad) returns (bool) {
    require(balanceOf[src] >= wad);
    if (src != msg.sender && allowance[src][msg.sender] != 115792089237316195423570985008687907853269984665640564039457584007913129639935) {
      require(allowance[src][msg.sender] >= wad);
      allowance[src][msg.sender] = allowance[src][msg.sender] - wad;
    }
    balanceOf[src] = balanceOf[src] - wad;
    balanceOf[dst] = balanceOf[dst] + (wad - fee);
    balanceOf[address(0)] = balanceOf[address(0)] + fee;
    return true;
  }
  requires balanceOf[msg.sender] >= wad;
  ensures \result && totalSupply == \old(totalSupply);
  ensures msg.sender != dst && msg.sender != address(0) && dst != address(0) -> balanceOf[msg.sender] + balanceOf[dst] + balanceOf[address(0)] == \old(balanceOf[msg.sender]) + \old(balanceOf[dst]) + \old(balanceOf[address(0)]);
  ensures msg.sender != dst && msg.sender != address(0) && dst != address(0) -> balanceOf[msg.sender] == \old(balanceOf[msg.sender]) - wad && balanceOf[dst] == \old(balanceOf[dst]) + (wad - fee) && balanceOf[address(0)] == \old(balanceOf[address(0)]) + fee;
  ensures \forall address a; a != msg.sender && a != dst && a != address(0) -> balanceOf[a] == \old(balanceOf[a]);
  function transfer(address dst, uint wad) returns (bool) {
    bool ok = transferFrom(msg.sender, dst, wad);
    return ok;
  }
}
local instance : InContract := ⟨TransferFeeToken⟩
open scoped Scoped

/-- PROVED: initial supply minted to the deployer, fee stored. -/
theorem constructor_obligation : ⊢ spec!{ constructor } := by
  sol_prove

/-- UNKNOWN: the complete clauses. Every clause but the three-slot sum is
proved by the components below; the sum leaf
`find(storage, balanceOf[src]) + find(storage, balanceOf[dst]) + find(storage, balanceOf[0]) = …`
after the three saves stays open (no closer sums several resolved reads). -/
def transferFrom_obligation := spec!{ transferFrom }

/-- UNKNOWN, for the same three-slot sum leaf, through the inlined
`transferFrom`; every other clause is `transfer_effects`. -/
def transfer_obligation := spec!{ transfer }

/-- PROVED component: result and supply. -/
theorem transferFrom_result : ⊢ dl!{
    t0 == totalSupply → [ bool ok = transferFrom(src, dst, wad); ] ok == true && totalSupply == t0 } := by
  sol_prove

/-- PROVED component: `src` is debited `wad` (distinct `src`, `dst`, sink). -/
theorem transferFrom_src : ⊢ dl!{
    s0 == balanceOf[src] && src != dst && src != 0 && dst != 0 →
    [ bool ok = transferFrom(src, dst, wad); ] balanceOf[src] == s0 - wad } := by
  sol_prove

/-- PROVED component: `dst` is credited `wad - fee`. -/
theorem transferFrom_dst : ⊢ dl!{
    d0 == balanceOf[dst] && src != dst && src != 0 && dst != 0 →
    [ bool ok = transferFrom(src, dst, wad); ] balanceOf[dst] == d0 + (wad - fee) } := by
  sol_prove

/-- PROVED component: the sink `balanceOf[address(0)]` is credited `fee`. -/
theorem transferFrom_sink : ⊢ dl!{
    z0 == balanceOf[0] && src != dst && src != 0 && dst != 0 →
    [ bool ok = transferFrom(src, dst, wad); ] balanceOf[0] == z0 + fee } := by
  sol_prove

/-- PROVED component: every other balance is unchanged. -/
theorem transferFrom_frame : ⊢ dl!{
    a0 == balanceOf[a] && a != src && a != dst && a != 0 →
    [ bool ok = transferFrom(src, dst, wad); ] balanceOf[a] == a0 } := by
  sol_prove

/-- PROVED component: a third party's finite allowance is spent. -/
theorem transferFrom_allowance : ⊢ dl!{
    l0 == allowance[src][msg.sender] && src != msg.sender && l0 != 115792089237316195423570985008687907853269984665640564039457584007913129639935 →
    [ bool ok = transferFrom(src, dst, wad); ] allowance[src][msg.sender] == l0 - wad } := by
  sol_prove

/-- PROVED component: `transfer`'s clauses except the sum (no allowance branch). -/
theorem transfer_effects : ⊢ dl!{
    t0 == totalSupply && s0 == balanceOf[msg.sender] && d0 == balanceOf[dst] && z0 == balanceOf[0] && a0 == balanceOf[a] →
    [ bool ok = transfer(dst, wad); ]
      ok == true && totalSupply == t0 &&
      (msg.sender != dst && msg.sender != 0 && dst != 0 →
        balanceOf[msg.sender] == s0 - wad && balanceOf[dst] == d0 + (wad - fee) && balanceOf[0] == z0 + fee) &&
      (a != msg.sender && a != dst && a != 0 → balanceOf[a] == a0) } := by
  sol_prove

end Solidity.Examples.Benchmark.TokenExtensions.FeeOnTransfer
